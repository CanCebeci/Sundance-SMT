// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};

/// Global debug level - controls which debug messages are printed
static DEBUG_LEVEL: AtomicU8 = AtomicU8::new(30);

pub fn set_debug_level(level: u8) {
    DEBUG_LEVEL.store(level, Ordering::SeqCst);
}

pub fn get_debug_level() -> u8 {
    DEBUG_LEVEL.load(Ordering::Relaxed)
}

pub fn is_important(importance: u8) -> bool {
    get_debug_level() <= importance
}

/// Whether to trace CDCL decisions, quantifier instances and backtracks
static TRACE_DECISIONS: AtomicBool = AtomicBool::new(false);

pub fn set_trace_decisions(enabled: bool) {
    TRACE_DECISIONS.store(enabled, Ordering::SeqCst);
}

pub fn trace_decisions() -> bool {
    TRACE_DECISIONS.load(Ordering::Relaxed)
}

/// Whether to trace the relevant e-nodes of each eager matching round
static TRACE_RELEVANCY: AtomicBool = AtomicBool::new(false);

pub fn set_trace_relevancy(enabled: bool) {
    TRACE_RELEVANCY.store(enabled, Ordering::SeqCst);
}

pub fn trace_relevancy() -> bool {
    TRACE_RELEVANCY.load(Ordering::Relaxed)
}

/// Whether to log the Z3 query of each partial arithmetic check
static TRACE_Z3_QUERIES: AtomicBool = AtomicBool::new(false);

pub fn set_trace_z3_queries(enabled: bool) {
    TRACE_Z3_QUERIES.store(enabled, Ordering::SeqCst);
}

pub fn trace_z3_queries() -> bool {
    TRACE_Z3_QUERIES.load(Ordering::Relaxed)
}

/// Debug macro -> used to print debug statements
#[macro_export]
macro_rules! debug_println {
    // Version with importance level and indentation
    ($importance:expr, $indent:expr, $($arg:tt)*) => {{
        let importance: u8 = $importance;
        if $crate::log::is_important(importance) {
            let indent: usize = $indent;
            let indent_str = "  ".repeat(indent);
            let color_str = match importance {
                0 => "\x1b[90m", // gray
                1 => "\x1b[34m", // blue
                2 => "\x1b[32m", // green
                3 => "\x1b[33m", // yellow
                4 => "\x1b[35m", // magenta
                5 => "\x1b[36m", // cyan
                _ => "\x1b[31m", // red
            };
            eprint!("{}{}", color_str, indent_str);
            eprint!($($arg)*);
            eprintln!("\x1b[0m");
        }
    }};

    // Backward compatibility - default importance 1, no indent
    ($($arg:tt)*) => {
        $crate::debug_println!(1, 0, $($arg)*)
    };
}
