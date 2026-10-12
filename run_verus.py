#!/usr/bin/env python3
"""
Script to run a solver binary on each .smt2 file in a folder
and count the number of unsat, unknown, and other results.
Supports parallel processing for improved performance.
"""
import os
import json
import shlex
import shutil
import subprocess
import sys
from pathlib import Path
import argparse
from typing import Dict, List, Tuple, Optional, IO, Any
import multiprocessing as mp
import time
import re
import csv
from datetime import datetime


SOLVER_PRESETS = {
    "z3": "z3 auto_config=false smt.mbqi=false smt.case_split=3 smt.qi.eager_threshold=100.0 smt.delay_units=true smt.arith.solver=2 smt.arith.nl=false pi.enabled=false rewriter.sort_disjunctions=false",
    "cvc5": "cvc5",
}


def get_git_info(repo_dir: Path) -> Dict[str, str]:
    """Get git commit hash, branch, and diff of src/ from the solver repo."""
    info = {}
    try:
        info['branch'] = subprocess.run(
            ["git", "rev-parse", "--abbrev-ref", "HEAD"],
            cwd=str(repo_dir), capture_output=True, text=True
        ).stdout.strip()
        info['commit'] = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=str(repo_dir), capture_output=True, text=True
        ).stdout.strip()
        info['diff'] = subprocess.run(
            ["git", "diff", "HEAD", "--", "src/"],
            cwd=str(repo_dir), capture_output=True, text=True
        ).stdout
    except Exception as e:
        info['error'] = str(e)
    return info


def run_solver_on_file(filepath: Path, solver: str, timeout: int,
                       proof_file: Optional[str] = None,
                       solver_kind: str = "sundance",
                       profile_path: Optional[str] = None) -> Tuple[str, str, float]:
    """
    Run solver on a single file and return the output and execution time.
    solver can be a full command string with arguments (e.g. "z3 auto_config=false ...").

    For sundance, we pass --timeout to the solver itself so it handles the timeout
    internally and still prints stats. The Python subprocess timeout is set higher
    as a safety net.

    If profile_path is set, wraps the command with 'perf record' and saves the
    profile data to that path.
    """
    start_time = time.time()
    try:
        command = shlex.split(solver) + [str(filepath)]

        if proof_file is not None:
            command.append(f"--proof={proof_file}")

        # For sundance, use internal timeout and give subprocess extra grace time
        if solver_kind == "sundance":
            command.append(f"--timeout={timeout}")
            subprocess_timeout = timeout + 30
        else:
            subprocess_timeout = timeout

        if profile_path:
            command = ["perf", "record", "-g", "--call-graph", "dwarf",
                       "-F", "99", "-o", profile_path, "--"] + command

        result = subprocess.run(
            command,
            capture_output=True,
            text=True,
            timeout=subprocess_timeout
        )
        end_time = time.time()
        return result.stdout, result.stderr, end_time - start_time
    except subprocess.TimeoutExpired:
        end_time = time.time()
        return "", "TIMEOUT", end_time - start_time
    except Exception as e:
        end_time = time.time()
        return "", f"ERROR: {str(e)}", end_time - start_time


def process_single_file_wrapper(args: Tuple[Path, Path, bool, str, int, Optional[str], str, Optional[str]]) -> Tuple[Path, str, float, str, str, Dict[str, Any]]:
    """
    Wrapper function to process a single file for multiprocessing.
    """
    filepath, base_folder_path, verbose, solver, timeout, proofs_dir, solver_kind, profile_dir = args

    proof_file = None
    if proofs_dir:
        relative_proof = filepath.relative_to(base_folder_path).with_suffix(".edrat")
        proof_path = Path(proofs_dir) / relative_proof
        proof_path.parent.mkdir(parents=True, exist_ok=True)
        proof_file = str(proof_path)

    profile_path = None
    if profile_dir:
        profile_name = filepath.stem + ".perf.data"
        profile_path = str(Path(profile_dir) / profile_name)

    stdout, stderr, time_taken = run_solver_on_file(
        filepath, solver, timeout, proof_file, solver_kind, profile_path
    )

    # Post-process profile: convert to collapsed stacks and remove raw data
    if profile_path and Path(profile_path).exists():
        collapsed_path = profile_path.replace(".perf.data", ".collapsed")
        try:
            collapse = subprocess.run(
                ["perf", "script", "-i", profile_path],
                capture_output=True, text=True, timeout=60
            )
            if collapse.returncode == 0:
                # Collapse stacks: each unique stack trace -> count
                stacks: Dict[str, int] = {}
                current_stack = []
                for sline in collapse.stdout.splitlines():
                    sline = sline.rstrip()
                    if not sline:
                        if current_stack:
                            key = ";".join(reversed(current_stack))
                            stacks[key] = stacks.get(key, 0) + 1
                            current_stack = []
                    elif sline.startswith("\t"):
                        parts = sline.strip().split(" ", 1)
                        func = parts[1] if len(parts) > 1 else parts[0]
                        func = func.split(" (")[0]
                        current_stack.append(func)
                if current_stack:
                    key = ";".join(reversed(current_stack))
                    stacks[key] = stacks.get(key, 0) + 1
                with open(collapsed_path, 'w') as cf:
                    for stack, count in sorted(stacks.items(), key=lambda x: -x[1]):
                        cf.write(f"{stack} {count}\n")
                Path(profile_path).unlink()
        except Exception:
            pass
    category = categorize_result(stdout, stderr)

    # For sundance with internal timeout, "unknown" is reported as the result
    # but stderr still has stats. For external subprocess timeouts, stderr is "TIMEOUT".
    stats: Dict[str, Any] = {}
    if solver_kind == "sundance":
        # Always try to extract stats — sundance prints them even on internal timeout
        stats = extract_sundance_stats(stderr)
        # Sundance reports "unknown" on internal timeout — reclassify as timeout
        # if solve_time >= timeout threshold
        if category == 'unknown' and stats.get('solve_time', 0) >= timeout * 0.95:
            category = 'timeout'
    elif stderr not in ("TIMEOUT",) and not (stderr and stderr.startswith("ERROR")):
        if solver_kind == "z3":
            stats = extract_z3_stats(stdout)
        elif solver_kind == "cvc5":
            stats = extract_cvc5_stats(stderr)

    return filepath, category, time_taken, stdout, stderr, stats


def flatten_stats(obj: Any, prefix: str = "") -> Dict[str, Any]:
    """Flatten a nested stats dict, joining keys with '.'. Skips lists."""
    flat = {}
    if isinstance(obj, dict):
        for k, v in obj.items():
            key = f"{prefix}.{k}" if prefix else k
            flat.update(flatten_stats(v, key))
    elif isinstance(obj, list):
        pass  # per_round array handled separately
    else:
        flat[prefix] = obj
    return flat


def extract_sundance_stats(text: str) -> Dict[str, Any]:
    """
    Extract a trailing JSON stats block from text (produced by sundance --stats).
    Returns a flattened dict with top-level aggregates and per-round summary stats.
    """
    stripped = text.rstrip()
    if not stripped.endswith("}"):
        return {}
    # Find the matching '{' for the last '}' by scanning backwards
    depth = 0
    start = -1
    for i in range(len(stripped) - 1, -1, -1):
        c = stripped[i]
        if c == "}":
            depth += 1
        elif c == "{":
            depth -= 1
            if depth == 0:
                start = i
                break
    if start < 0:
        return {}
    try:
        raw = json.loads(stripped[start:])
    except json.JSONDecodeError:
        return {}

    # Flatten top-level stats (skips per_round list)
    flat = flatten_stats(raw)

    # Extract per-round stats as comma-separated lists for each field
    per_round = raw.get("per_round")
    if per_round and isinstance(per_round, list) and len(per_round) > 0:
        # Collect all keys from round entries (flatten nested dicts like "arith")
        round_keys: Dict[str, List[Any]] = {}
        for r in per_round:
            flat_round = flatten_stats({k: v for k, v in r.items() if k != "round"})
            for k, v in flat_round.items():
                round_keys.setdefault(k, []).append(v)
        for k, vals in round_keys.items():
            flat[f"per_round.{k}"] = ",".join(str(x) for x in vals)

    return flat


def extract_z3_stats(text: str) -> Dict[str, Any]:
    """
    Extract z3 --st output. z3 prints stats after the result as an s-expression:
        (:key1 val1
         :key2 val2
         ...)
    on stdout. Returns a dict of numeric stats.
    """
    # Find the last '(' matching the trailing ')'
    stripped = text.rstrip()
    if not stripped.endswith(")"):
        return {}
    depth = 0
    start = -1
    for i in range(len(stripped) - 1, -1, -1):
        c = stripped[i]
        if c == ")":
            depth += 1
        elif c == "(":
            depth -= 1
            if depth == 0:
                start = i
                break
    if start < 0:
        return {}
    block = stripped[start + 1:-1]
    stats: Dict[str, Any] = {}
    # Match :key   value  pairs. Values are numeric (int or float).
    for match in re.finditer(r':([a-zA-Z0-9_\-]+)\s+([\d.eE\-+]+)', block):
        key, val = match.group(1), match.group(2)
        try:
            stats[key] = int(val)
        except ValueError:
            try:
                stats[key] = float(val)
            except ValueError:
                pass
    return stats


def _parse_number(s: str) -> Optional[Any]:
    """Parse a possibly-suffixed number ('2ms', '1.5', '42') into int/float, else None."""
    m = re.match(r'^(-?[\d.]+(?:[eE][\-+]?\d+)?)(ms|s|us|ns)?$', s.strip())
    if not m:
        return None
    num = m.group(1)
    try:
        return int(num)
    except ValueError:
        try:
            return float(num)
        except ValueError:
            return None


def extract_cvc5_stats(text: str) -> Dict[str, Any]:
    """
    Extract cvc5 --stats output. cvc5 prints stats on stderr as lines:
        path::to::stat = value
    Values are either scalars (e.g. '2ms', '1338') or dicts (e.g. '{ FOO: 1, BAR: 2 }').
    Dict entries are flattened as 'path::to::stat.FOO' etc.
    """
    stats: Dict[str, Any] = {}
    for line in text.splitlines():
        if " = " not in line:
            continue
        key, _, val = line.partition(" = ")
        key = key.strip()
        val = val.strip()
        if not key or not val:
            continue
        if val.startswith("{") and val.endswith("}"):
            # Flatten dict entries into individual stats
            inner = val[1:-1].strip()
            if not inner:
                continue
            for pair in inner.split(","):
                if ":" not in pair:
                    continue
                subkey, _, subval = pair.partition(":")
                num = _parse_number(subval)
                if num is not None:
                    stats[f"{key}.{subkey.strip()}"] = num
        else:
            num = _parse_number(val)
            if num is not None:
                stats[key] = num
    return stats


def categorize_result(stdout: str, stderr: str) -> str:
    """
    Categorize the result based on output content.

    The check-sat verdict may not be the very last thing on stdout when the
    solver also prints stats. Scan lines from the top to find the verdict.
    """
    for line in stdout.splitlines():
        stripped = line.strip()
        if stripped == "unsat":
            return 'unsat'
        if stripped == "sat":
            return 'other'
        if stripped == "unknown":
            return 'unknown'
    if 'TIMEOUT' in stderr:
        return 'timeout'
    if 'ERROR' in stderr:
        return 'error'
    return 'other'


def parse_previous_results(results_file: Path, base_folder: Path) -> Dict[str, str]:
    """
    Parse a previous results file and return a mapping of file paths to their results.
    """
    file_results = {}

    if not results_file.exists():
        return file_results

    pattern = re.compile(r'\[\d+/\d+\]\s+(.+?)\s+->\s+(\w+)\s+\[[\d.]+s\]')

    try:
        with open(results_file, 'r', encoding='utf-8') as f:
            for line in f:
                match = pattern.match(line.strip())
                if match:
                    file_path = match.group(1)
                    result = match.group(2).lower()
                    file_results[file_path] = result
    except Exception:
        pass

    return file_results


def should_rerun_file(filepath: Path, base_folder: Path, previous_results: Dict[str, str]) -> bool:
    """
    Determine if a file should be rerun based on previous results.
    """
    try:
        relative_path = filepath.relative_to(base_folder)
        relative_path_str = str(relative_path)

        if relative_path_str not in previous_results:
            return True

        previous_result = previous_results[relative_path_str]
        if previous_result == 'other':
            return True

        return False
    except ValueError:
        return True


def log(out: IO, msg: str):
    out.write(msg + "\n")
    out.flush()


def process_folder(folder_path: Path, out: IO, verbose: bool = False, num_processes: int = 4,
                   previous_results: Optional[Dict[str, str]] = None,
                   solver: str = "target/release/sundance-smt",
                   timeout: int = 60,
                   proofs: Optional[str] = None,
                   solver_kind: str = "sundance",
                   profile_dir: Optional[str] = None) -> Tuple[Dict[str, List[Path]], List[Tuple[Path, str, float, Dict[str, Any]]]]:
    """
    Recursively process all files in a folder using parallel processing.
    Returns results dict and a list of (filepath, category, time, stats) for CSV output.
    """
    results = {
        'unsat': [],
        'unknown': [],
        'timeout': [],
        'error': [],
        'other': []
    }

    all_files = []
    for root, dirs, files in os.walk(folder_path):
        for file in sorted(files):
            filepath = Path(root) / file
            if not any(part.startswith('.') for part in filepath.parts) and str(filepath).endswith('.smt2'):
                all_files.append(filepath)

    files_to_process = []
    if previous_results is not None:
        skipped_count = 0
        for filepath in all_files:
            if should_rerun_file(filepath, folder_path, previous_results):
                files_to_process.append(filepath)
            else:
                skipped_count += 1
        log(out, f"Found {len(all_files)} total files, filtering to {len(files_to_process)} files to process")
        log(out, f"Skipping {skipped_count} files that already have UNSAT/UNKNOWN/TIMEOUT/ERROR results")
    else:
        files_to_process = all_files

    total_files = len(files_to_process)
    log(out, f"Processing {total_files} files in '{folder_path}'")
    log(out, f"Using {num_processes} parallel processes")
    log(out, f"Solver: {solver}")
    log(out, f"Timeout: {timeout}s")
    if proofs:
        log(out, f"Proof directory: {proofs}")
    log(out, "-" * 60)

    if total_files == 0:
        return results, []

    process_args = [(filepath, folder_path, verbose, solver, timeout, proofs, solver_kind, profile_dir)
                    for filepath in files_to_process]

    start_time = time.time()
    completed = 0
    detailed_results = []

    with mp.Pool(processes=num_processes) as pool:
        for filepath, category, time_taken, stdout, stderr, stats in pool.imap_unordered(process_single_file_wrapper, process_args):
            completed += 1
            results[category].append(filepath)
            detailed_results.append((filepath, category, time_taken, stats))

            relative_path = filepath.relative_to(folder_path)
            stats_suffix = ""
            if stats:
                stats_suffix = " " + " ".join(f"{k}={v}" for k, v in stats.items())
            log(out, f"[{completed}/{total_files}] {relative_path} -> {category.upper()} [{time_taken:.2f}s]{stats_suffix}")

            if verbose:
                if stdout:
                    log(out, f"  Output preview: {stdout[:1000]}...")
                else:
                    log(out, "  No output")
                if stderr and stderr not in ['TIMEOUT', 'ERROR']:
                    log(out, f"  Stderr preview: {stderr[-1000:]}...")

    elapsed_time = time.time() - start_time
    log(out, f"\nProcessing completed in {elapsed_time:.2f} seconds")

    return results, detailed_results


def print_summary(results: Dict[str, List[Path]], folder_path: Path, out: IO):
    """
    Print a summary of the results.
    """
    log(out, "\n" + "=" * 60)
    log(out, "SUMMARY")
    log(out, "=" * 60)
    total = sum(len(files) for files in results.values())
    log(out, f"\nTotal files processed: {total}")
    if total == 0:
        return
    log(out, f"  - UNSAT results:   {len(results['unsat']):4d} ({len(results['unsat'])*100/total:.1f}%)")
    log(out, f"  - UNKNOWN results: {len(results['unknown']):4d} ({len(results['unknown'])*100/total:.1f}%)")
    log(out, f"  - TIMEOUT results: {len(results['timeout']):4d} ({len(results['timeout'])*100/total:.1f}%)")
    log(out, f"  - ERROR results:   {len(results['error']):4d} ({len(results['error'])*100/total:.1f}%)")
    log(out, f"  - OTHER results:   {len(results['other']):4d} ({len(results['other'])*100/total:.1f}%)")
    neither_count = len(results['timeout']) + len(results['error']) + len(results['other'])
    log(out, f"\n  - Neither UNSAT nor UNKNOWN: {neither_count:4d} ({neither_count*100/total:.1f}%)")

    if any(len(files) > 0 and len(files) <= 10 for files in results.values()):
        log(out, "\n" + "-" * 60)
        for category, files in results.items():
            if 0 < len(files) <= 10:
                log(out, f"\n{category.upper()} files:")
                for f in files:
                    log(out, f"  - {f.relative_to(folder_path)}")


def save_results_csv(detailed_results: List[Tuple[Path, str, float, Dict[str, Any]]], folder_path: Path, output_path: Path):
    """Save per-file results to a CSV file. Stats fields become additional columns."""
    # Collect the union of all stat keys, preserving first-seen order
    stat_keys: List[str] = []
    seen = set()
    for _, _, _, stats in detailed_results:
        for k in stats:
            if k not in seen:
                seen.add(k)
                stat_keys.append(k)

    with open(output_path, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['file', 'result', 'time_seconds'] + stat_keys)
        for filepath, category, time_taken, stats in sorted(detailed_results, key=lambda x: str(x[0])):
            try:
                relative = filepath.relative_to(folder_path)
            except ValueError:
                relative = filepath
            row = [str(relative), category, f"{time_taken:.2f}"]
            row.extend(stats.get(k, "") for k in stat_keys)
            writer.writerow(row)


def main():
    parser = argparse.ArgumentParser(
        description="Run a solver on all .smt2 files in a folder and count results"
    )
    parser.add_argument(
        "folder",
        type=str,
        help="Path to the folder containing .smt2 files to process"
    )
    parser.add_argument(
        "-v", "--verbose",
        action="store_true",
        help="Show detailed output for each file"
    )
    parser.add_argument(
        "-o", "--output-dir",
        type=str,
        default="outputs",
        help="Directory to save output files (default: outputs)"
    )
    parser.add_argument(
        "-j", "--jobs",
        type=int,
        default=4,
        help="Number of parallel processes to use (default: 4)"
    )
    parser.add_argument(
        "--solver",
        type=str,
        default=None,
        help="Solver to use: a preset name (z3, cvc5), a path to a binary, or a full command string"
    )
    parser.add_argument(
        "--build-dir",
        type=str,
        default="/local/home/shaamarl/Sundance-SMT",
        help="Path to the solver project directory for cargo build (default: /local/home/shaamarl/Sundance-SMT)"
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=60,
        help="Timeout in seconds per file (default: 60)"
    )
    proof_group = parser.add_mutually_exclusive_group()
    proof_group.add_argument(
        "--proofs",
        action="store_true",
        help="Enable proof production. Proofs are saved under "
             "verus_benchmarks/proofs/<run-name>/"
    )
    proof_group.add_argument(
        "--proofs-dir",
        type=str,
        default=None,
        help="Enable proof production and save proofs under PATH/<run-name>/"
    )
    parser.add_argument(
        "--sundance-flags",
        type=str,
        default=None,
        help="Extra flags to pass to sundance-smt (e.g. '--arithmetic internal'). Also used as output file prefix."
    )
    parser.add_argument(
        "--instantiation-cap",
        type=int,
        default=None,
        help="Max quantifier instantiations sundance materializes per complete-model check "
             "(passed through as --batch-cap). 0 = unbounded. Only applies to sundance."
    )
    parser.add_argument(
        "--relevancy",
        type=int,
        default=None,
        choices=[0, 1, 2],
        help="z3 relevancy propagation level (passed through as smt.relevancy=<n>). "
             "0 = off, 2 = default. Only applies to --solver z3."
    )
    parser.add_argument(
        "--z3-proof-production",
        action="store_true",
        help="Run z3 in proof-production mode (passes proof=true). Only applies to --solver z3."
    )
    parser.add_argument(
        "--cvc5-proof-production",
        action="store_true",
        help="Run cvc5 in proof-production mode (passes --produce-proofs --check-proofs). "
             "Only applies to --solver cvc5."
    )
    parser.add_argument(
        "--filter-from",
        type=str,
        help="Path to a previous results file. Only rerun benchmarks that had OTHER results"
    )
    parser.add_argument(
        "--profile",
        action="store_true",
        help="Run each solver invocation under 'perf record'. Profiles are saved to profiles/{timestamp}/"
    )
    parser.add_argument(
        "--no-build",
        action="store_true",
        help="Skip cargo build step (assume solver binary already exists)"
    )
    args = parser.parse_args()

    if args.jobs < 1:
        print("Error: Number of jobs must be at least 1")
        sys.exit(1)

    folder_path = Path(args.folder).resolve()
    if not folder_path.exists():
        print(f"Error: Folder '{folder_path}' does not exist")
        sys.exit(1)
    if not folder_path.is_dir():
        print(f"Error: '{folder_path}' is not a directory")
        sys.exit(1)

    build_dir = Path(args.build_dir).resolve()

    # Resolve solver command: preset name, explicit command/path, or default (sundance-smt)
    # "external" means it's not sundance-smt — skip build, log version instead of git info
    using_external = False
    solver_label = None
    solver_kind = "sundance"
    if args.solver and args.solver in SOLVER_PRESETS:
        solver = SOLVER_PRESETS[args.solver]
        using_external = True
        solver_label = args.solver
        solver_kind = args.solver  # "z3" or "cvc5"
    elif args.solver:
        solver = args.solver
        # Detect external solvers by binary name
        binary_name = Path(shlex.split(solver)[0]).name
        if binary_name.startswith("cvc5"):
            using_external = True
            solver_label = binary_name
            solver_kind = "cvc5"
        elif binary_name.startswith("z3"):
            using_external = True
            solver_label = binary_name
            solver_kind = "z3"
    else:
        solver = str(build_dir / "target" / "release" / "sundance-smt")

    if (args.proofs or args.proofs_dir) and using_external:
        print("Error: --proofs and --proofs-dir only apply to Sundance")
        sys.exit(1)

    # Append sundance flags to the solver command
    if args.sundance_flags and not using_external:
        solver = solver + " " + args.sundance_flags

    # Append the instantiation cap (sundance only)
    if args.instantiation_cap is not None:
        if using_external:
            print("Warning: --instantiation-cap only applies to sundance; ignoring for external solver")
        else:
            solver = solver + f" --batch-cap {args.instantiation_cap}"

    # Append the z3 relevancy level (z3 only)
    if args.relevancy is not None:
        if solver_kind == "z3":
            solver = solver + f" smt.relevancy={args.relevancy}"
        else:
            print("Warning: --relevancy only applies to --solver z3; ignoring")

    # Enable z3 proof-production mode (z3 only).
    if args.z3_proof_production:
        if solver_kind == "z3":
            solver = solver + " proof=true"
        else:
            print("Warning: --z3-proof-production only applies to --solver z3; ignoring")

    # Enable cvc5 proof-production mode (cvc5 only).
    if args.cvc5_proof_production:
        if solver_kind == "cvc5":
            solver = solver + " --produce-proofs --check-proofs"
        else:
            print("Warning: --cvc5-proof-production only applies to --solver cvc5; ignoring")

    # Enable stats output
    if solver_kind == "sundance":
        solver = solver + " --stats"
    elif solver_kind == "z3":
        solver = solver + " --st"
    elif solver_kind == "cvc5":
        solver = solver + " --stats"

    # Parse previous results if filtering is requested
    previous_results = None
    if args.filter_from:
        results_file_path = Path(args.filter_from).resolve()
        if not results_file_path.exists():
            print(f"Error: Results file '{results_file_path}' does not exist")
            sys.exit(1)
        previous_results = parse_previous_results(results_file_path, folder_path)

    # Build the solver if needed (skip for external solvers and --no-build)
    if not args.no_build and not using_external:
        print(f"Building solver in {build_dir}...")
        build_result = subprocess.run(
            ["cargo", "build", "--release"],
            cwd=str(build_dir),
            capture_output=True,
            text=True
        )
        if build_result.returncode != 0:
            print(f"Error: cargo build failed:\n{build_result.stderr[-2000:]}")
            sys.exit(1)
        print("Build successful.")

    # Verify solver binary exists (check first token of the command)
    solver_binary = shlex.split(solver)[0]
    if not Path(solver_binary).exists() and not shutil.which(solver_binary):
        print(f"Error: Solver binary not found at '{solver_binary}'")
        sys.exit(1)

    # Create output directory
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    # Generate output filenames based on benchmark folder name
    benchmark_name = folder_path.name.lower()
    if benchmark_name in ('20241211-verus',):
        benchmark_name = folder_path.parent.name.lower()
    timestamp = datetime.now().strftime('%Y-%m-%d_%H-%M-%S')
    if using_external:
        prefix = f"{solver_label}-"
    elif args.sundance_flags:
        # Turn flags like "--arithmetic internal" into "arithmetic-internal-"
        flag_slug = args.sundance_flags.replace("--", "").replace(" ", "-").strip("-")
        prefix = f"sundance-{flag_slug}-"
    else:
        prefix = ""
    # Distinguish runs by instantiation cap so they don't overwrite each other
    if args.instantiation_cap is not None and not using_external:
        prefix = f"{prefix}cap{args.instantiation_cap}-"
    # Distinguish z3 runs by relevancy level
    if args.relevancy is not None and solver_kind == "z3":
        prefix = f"{prefix}rel{args.relevancy}-"
    # Distinguish z3 proof-production runs
    if args.z3_proof_production and solver_kind == "z3":
        prefix = f"{prefix}proof-"
    # Distinguish cvc5 proof-production runs
    if args.cvc5_proof_production and solver_kind == "cvc5":
        prefix = f"{prefix}proof-"
    run_name = f"{prefix}{timestamp}_{benchmark_name}"
    txt_output = output_dir / f"{run_name}_results.txt"
    csv_output = output_dir / f"{run_name}_results.csv"

    # Set up proof directory if proof production is enabled
    proofs_dir = None
    if args.proofs_dir:
        proofs_dir = Path(args.proofs_dir).expanduser().resolve() / run_name
        proofs_dir.mkdir(parents=True, exist_ok=True)
    elif args.proofs:
        script_dir = Path(__file__).resolve().parent.parent
        proofs_dir = script_dir / "proofs" / run_name
        proofs_dir.mkdir(parents=True, exist_ok=True)
    if proofs_dir:
        print(f"Proof production enabled. Proofs will be saved to: {proofs_dir}")

    # Set up profile directory if profiling is enabled
    profile_dir = None
    if args.profile:
        script_dir = Path(__file__).resolve().parent.parent
        profile_dir = script_dir / "profiles" / timestamp
        profile_dir.mkdir(parents=True, exist_ok=True)
        print(f"Profiling enabled. Profiles will be saved to: {profile_dir}")
        print("Note: perf adds ~10-20% overhead. Consider using a larger --timeout.")

    # Open txt file and write all output there as the script runs
    with open(txt_output, 'w') as out:
        log(out, datetime.now().strftime('%Y-%m-%d %H:%M:%S'))
        log(out, f"Starting to process folder: {folder_path}")

        if using_external:
            # For external solvers, log version and path instead of git info
            solver_path = shutil.which(solver_binary) or solver_binary
            log(out, f"Solver: {solver_label}")
            log(out, f"Solver binary: {solver_path}")
            log(out, f"Solver command: {solver}")
            try:
                version_result = subprocess.run(
                    [solver_path, "--version"],
                    capture_output=True, text=True, timeout=5
                )
                version_str = version_result.stdout.strip().split('\n')[0] if version_result.stdout else version_result.stderr.strip().split('\n')[0]
                log(out, f"Solver version: {version_str}")
            except Exception:
                log(out, "Solver version: <unknown>")
            log(out, "-" * 60)
        else:
            # For sundance-smt, log git info
            git_info = get_git_info(build_dir)
            if git_info.get('branch'):
                log(out, f"Git branch: {git_info['branch']}")
                log(out, f"Git commit: {git_info['commit']}")
                if git_info.get('diff'):
                    log(out, f"Git diff (src/):")
                    log(out, git_info['diff'])
                else:
                    log(out, "Git diff (src/): <clean>")
                log(out, "-" * 60)

        if previous_results:
            log(out, f"Filtering based on previous results from: {args.filter_from}")
        if proofs_dir:
            log(out, f"Proofs: {proofs_dir}")

        results, detailed_results = process_folder(
            folder_path, out, args.verbose, args.jobs, previous_results,
            solver, args.timeout, str(proofs_dir) if proofs_dir else None,
            solver_kind, str(profile_dir) if profile_dir else None
        )

        print_summary(results, folder_path, out)

    # Save CSV separately
    save_results_csv(detailed_results, folder_path, csv_output)
    print(f"Done. Results written to {txt_output} and {csv_output}")


if __name__ == "__main__":
    main()
