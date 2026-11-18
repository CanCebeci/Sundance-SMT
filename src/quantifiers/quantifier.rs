// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Instantiation of quantifiers

use std::cell::RefCell;
use std::collections::VecDeque;
use std::rc::Rc;

use crate::arithmetic::simplify::ArithSimplify;
use crate::cnf::{CNFConversion, push_literal_if_not_tautology};
use crate::egraphs::EgraphTrait;
use crate::log::{planner_trace, planner_trace_eq, planner_trace_fact, trace_relevancy};
use crate::preprocess::check_for_function_bool;
use crate::proof::{ProofStepType, SMTProofTracer, Theory};
use crate::quantifiers::skolem::skolemize;
use crate::solver_state::SolverState;
use crate::solver_types::Polarity;
use crate::utils::{DeterministicHashMap, FastDeterministicHashSet};

use crate::debug_println;
use yaspar_ir::ast::{
    AConstant, ATerm, LetElim, Repr as _, Local, Sort, Str, Substitute, Substitution, Term, TermAllocator,
};

#[derive(Debug, Clone)]
pub(crate) enum QuantifierInstance {
    Instantiation {
        clauses: Vec<Vec<i32>>,
        generation: u32,
        /// Solver UID of the instantiated quantifier
        quantifier_id: u64,
        /// The match's bindings in variable declaration order (only with `--planner-trace`)
        bindings: Vec<Term>,
        /// Identifies the match (see `SolverState::added_instantiations`)
        instance_id: usize,
        /// Index of the instance's root in `SolverState::relevancy_roots`
        relevancy_root: usize,
        /// The egraph term ids allocated while materializing the instance
        term_ids: std::ops::Range<u32>,
    },
    Skolemization {
        clauses: Vec<Vec<i32>>,
    },
}

struct DeferredInstantiation {
    instance_id: usize,
    substituted_term: Term,
    is_exists: bool,
    literal: i32,
    quantifier_id: u64,
    /// One more than the largest generation among the match's bindings
    generation: u32,
    bindings: Vec<Term>,
}

struct DeferredSkolemization {
    skolem: Term,
    skolem_vars: Vec<(Str, Sort)>,
    is_exists: bool,
    literal: i32,
}

pub(crate) struct PendingInstantiations {
    deferred_instantiations: VecDeque<DeferredInstantiation>,
    deferred_skolemizations: VecDeque<DeferredSkolemization>,
    skolemized_quantifier_idxs: Vec<usize>,
}

impl PendingInstantiations {
    pub(crate) fn is_empty(&self) -> bool {
        self.deferred_instantiations.is_empty() && self.deferred_skolemizations.is_empty()
    }

    pub(crate) fn skolemized_quantifier_idxs(&self) -> &[usize] {
        &self.skolemized_quantifier_idxs
    }
}

/// Decides whether an instance of a quantifier body is already true (or already
/// false) in the current e-graph, without creating any term, following Z3's
/// `smt::checker`. Bound variables stand for their bindings' e-classes; other
/// terms are looked up as registered terms or, failing that, through congruence
/// (a term with the same operator over equal children). An atom has a value when
/// its class contains `true` or `false`, which assigned atoms are merged with.
/// With relevancy, only the values of relevant atoms count, and a registered
/// formula that is relevant decides by its own value, even when it has none
/// yet. Unlike Z3, the terms used only to find a class need not be relevant:
/// e.g. constructor terms from datatype axioms are never relevant here, but
/// the equalities they take part in hold all the same.
struct SatChecker<'a> {
    solver_state: &'a SolverState,
    subs: &'a DeterministicHashMap<Local, u32>,
    relevant: Option<&'a FastDeterministicHashSet<u32>>,
    true_root: u32,
    false_root: u32,
}

impl<'a> SatChecker<'a> {
    fn new(
        solver_state: &'a SolverState,
        subs: &'a DeterministicHashMap<Local, u32>,
        relevant: Option<&'a FastDeterministicHashSet<u32>>,
    ) -> Self {
        let egraph = &solver_state.egraph;
        let true_root = egraph.find(solver_state.to_egraph_id(solver_state.true_uid));
        let false_root = egraph.find(solver_state.to_egraph_id(solver_state.false_uid));
        SatChecker {
            solver_state,
            subs,
            relevant,
            true_root,
            false_root,
        }
    }

    fn is_relevant(&self, id: u32) -> bool {
        self.relevant.is_none_or(|r| r.contains(&id))
    }

    /// The truth value of the class of `id`, if it contains `true` or `false`
    fn class_value(&self, id: u32) -> Option<bool> {
        let root = self.solver_state.egraph.find(id);
        if root == self.true_root {
            Some(true)
        } else if root == self.false_root {
            Some(false)
        } else {
            None
        }
    }

    /// An e-graph term equal to `term` under the bindings
    fn eq_to(&self, term: &Term) -> Option<u32> {
        match term.repr() {
            ATerm::Local(local) => return self.subs.get(&local).copied(),
            ATerm::Annotated(inner, _) => return self.eq_to(inner),
            _ => {}
        }
        if let Some(id) = self.solver_state.registered_egraph_id(term.uid()) {
            return Some(id);
        }
        let children: Vec<&Term> = match term.repr() {
            ATerm::App(_, args, _) => args.iter().collect(),
            ATerm::Eq(a, b) => vec![a, b],
            ATerm::Ite(c, a, b) => vec![c, a, b],
            _ => return None,
        };
        if children.is_empty() {
            return None;
        }
        let ids = children
            .iter()
            .map(|c| self.eq_to(c))
            .collect::<Option<Vec<u32>>>()?;
        let op = SolverState::extract_op(term);
        let egraph = &self.solver_state.egraph;
        egraph.lookup_congruent(&op, &ids).or_else(|| {
            matches!(term.repr(), ATerm::Eq(..))
                .then(|| egraph.lookup_congruent(&op, &[ids[1], ids[0]]))
                .flatten()
        })
    }

    /// The value of the atom `term` under the bindings: that of a relevant
    /// e-graph term equal to it
    fn atom_value(&self, term: &Term) -> Option<bool> {
        let id = self.eq_to(term)?;
        if self.is_relevant(id) {
            self.class_value(id)
        } else {
            None
        }
    }

    /// Whether `term` (a formula) is known to have the value `is_true`
    fn check(&self, term: &Term, is_true: bool) -> bool {
        if let Some(id) = self.solver_state.registered_egraph_id(term.uid())
            && self.is_relevant(id)
        {
            return self.class_value(id) == Some(is_true);
        }
        match term.repr() {
            ATerm::Constant(AConstant::Bool(b), _) => *b == is_true,
            ATerm::Annotated(inner, _) => self.check(inner, is_true),
            ATerm::Not(a) => self.check(a, !is_true),
            ATerm::And(args) if is_true => args.iter().all(|a| self.check(a, true)),
            ATerm::And(args) => args.iter().any(|a| self.check(a, false)),
            ATerm::Or(args) if is_true => args.iter().any(|a| self.check(a, true)),
            ATerm::Or(args) => args.iter().all(|a| self.check(a, false)),
            ATerm::Implies(lhs, rhs) if is_true => {
                lhs.iter().any(|a| self.check(a, false)) || self.check(rhs, true)
            }
            ATerm::Implies(lhs, rhs) => {
                lhs.iter().all(|a| self.check(a, true)) && self.check(rhs, false)
            }
            ATerm::Ite(c, a, b) => {
                if self.check(c, true) {
                    self.check(a, is_true)
                } else if self.check(c, false) {
                    self.check(b, is_true)
                } else {
                    self.check(a, is_true) && self.check(b, is_true)
                }
            }
            ATerm::Eq(a, b) => {
                if is_true
                    && let (Some(x), Some(y)) = (self.eq_to(a), self.eq_to(b))
                    && self.solver_state.egraph.are_equal(x, y)
                {
                    return true;
                }
                // A congruent equality atom with a value (e.g. a disequality)
                if self.atom_value(term) == Some(is_true) {
                    return true;
                }
                // Boolean sides: equal or opposite values
                (self.check(a, true) && self.check(b, is_true))
                    || (self.check(a, false) && self.check(b, !is_true))
            }
            _ => self.atom_value(term) == Some(is_true),
        }
    }
}

/// Computes trigger matches and substitutions, returning deferred items
/// that can be materialized one at a time.
///
/// A match's instance has generation one more than the match's generation: the
/// largest generation among the e-nodes its trigger matched (input terms are 0;
/// terms an instance introduces get the instance's generation). With
/// `max_generation`, matches whose instance would exceed it are skipped without
/// being recorded as added, so a later round without the limit can still
/// instantiate them. This bounds matching loops: only finitely many terms have
/// a generation up to the limit, and so only finitely many matches.
pub(crate) fn instantiate_quantifiers(
    solver_state: &mut SolverState,
    assignments: &[i32],
    allow_skolemization: bool,
    max_generation: Option<u32>,
    relevant: Option<&FastDeterministicHashSet<u32>>,
) -> PendingInstantiations {
    let eager_skolem = solver_state.eager_skolem;
    debug_println!(24, 0, "Starting a matching round");
    // With `relevant`, trigger matches only start from relevant e-nodes
    if let Some(relevant) = relevant
        && trace_relevancy()
    {
        eprintln!("[relevancy] {} relevant e-nodes", relevant.len());
        let mut ids: Vec<u32> = relevant.iter().copied().collect();
        ids.sort_unstable();
        for id in ids {
            let term = solver_state.get_term(solver_state.to_solver_uid(id));
            eprintln!("[relevancy]   #{id}: {term}");
        }
    }
    let quantifiers = &solver_state.quantifiers.clone();
    let mut skolemized_quantifier_idxs = vec![];
    let mut deferred_skolemizations: VecDeque<DeferredSkolemization> = VecDeque::new();
    let mut deferred_instantiations: VecDeque<DeferredInstantiation> = VecDeque::new();

    // We `enumerate()` so we can update quantifiers[i].skolemized after the loop
    for (i, quantifier) in quantifiers.iter().enumerate() {
        debug_println!(
            19,
            0,
            "We have the quantifier {}",
            solver_state.get_term(quantifier.id)
        );

        // check if the quantifier is assigned
        let quantifier_literal = solver_state.get_lit_from_u64(quantifier.id);
        assert!(quantifier_literal != 0); // todo: note I think this should actually always be positive but not sure
        let quantifier_assignment = assignments
            .get(quantifier_literal.unsigned_abs() as usize)
            .copied()
            .unwrap_or(0);

        // if the quantifier is unassigned, we can skip it
        if quantifier_assignment == 0 {
            continue;
        }

        // if an odd number of these is true (i.e., XOR true) -> skolemize
        // if an even number of these is true (i.e., XOR false) -> instantiate
        let quantifier_is_exists = quantifier.polarity == Polarity::Existential;
        let quantifier_polarity =
            (quantifier_assignment > 0) ^ (quantifier_literal > 0) ^ quantifier_is_exists;

        // if the quantifier has positive polarity or we are doing ddsmt optimizations, and we haven't skolemized it yet, then we skolemize it
        if allow_skolemization && (quantifier_polarity || eager_skolem) && !quantifier.skolemized {
            skolemized_quantifier_idxs.push(i);

            let term = solver_state.get_term(quantifier.id);
            let (skolem, skolem_vars) =
                skolemize(&term, &mut solver_state.context, quantifier_is_exists);

            deferred_skolemizations.push_back(DeferredSkolemization {
                skolem,
                skolem_vars,
                is_exists: quantifier_is_exists,
                literal: quantifier_literal,
            });
        }

        // if this was a skolemization case, we don't want to instantiate
        if quantifier_polarity {
            continue;
        }

        let triggers = &quantifier.triggers;
        if triggers.is_empty() {
            debug_println!(
                "Warning: quantifier {} reached instantiation with no triggers",
                quantifier.id
            );
            continue;
        }
        // note we consider patterns in a multipattern conjunctively and multipatterns in a trigger disjunctively
        for multipattern in triggers {
            let body = quantifier.body;
            let trigger_term_pairs: Vec<(usize, Option<u32>)> =
                multipattern.iter().map(|t| (*t, None)).collect();

            let list_assignments = solver_state
                .egraph
                .match_triggers(trigger_term_pairs, relevant);

            if list_assignments.is_empty() {
                continue;
            }

            for (subs_ids, match_generation) in list_assignments.iter() {
                let generation = match_generation + 1;
                if max_generation.is_some_and(|max| generation > max) {
                    continue;
                }

                // Convert the (Local -> egraph id) map into a (Local -> Term) map for substitution
                let subs: DeterministicHashMap<Local, Term> = subs_ids
                    .iter()
                    .map(|(k, v)| {
                        // Fold the class representative (e.g. `(+ 2 1)` -> `3`) so that
                        // arithmetically equal bindings dedup and instantiate alike
                        let rep = solver_state.get_term(solver_state.to_solver_uid(*v));
                        (k.clone(), rep.simplify(&mut solver_state.context))
                    })
                    .collect();

                if let Some(&id) = solver_state
                    .added_instantiations
                    .get(&quantifier.id)
                    .and_then(|matches| matches.get(&subs))
                {
                    // Z3 would re-create the instance if it dropped it on backtracking
                    solver_state.rematched_instances.push(id);
                    continue;
                }

                // Like Z3, skip instances whose body is already true. They are not
                // recorded as added, so a later round can still add them once the
                // body no longer holds (e.g. after backtracking).
                let checker = SatChecker::new(solver_state, subs_ids, relevant);
                if checker.check(&solver_state.get_term(body), !quantifier_is_exists) {
                    if trace_relevancy() {
                        let mut sorted: Vec<_> = subs.iter().collect();
                        sorted.sort_by(|a, b| a.0.cmp(b.0));
                        let bindings: Vec<String> =
                            sorted.iter().map(|(_, t)| t.to_string()).collect();
                        eprintln!(
                            "[satisfied] {} {}",
                            solver_state.get_term(quantifier.id),
                            bindings.join(" ")
                        );
                    }
                    continue;
                }
                let instance_id = solver_state.num_instance_ids;
                solver_state.num_instance_ids += 1;
                solver_state
                    .added_instantiations
                    .entry(quantifier.id)
                    .or_default()
                    .insert(subs.clone(), instance_id);

                // Locals order by binder id, i.e. declaration order
                let bindings = if planner_trace() {
                    let mut sorted: Vec<_> = subs.iter().collect();
                    sorted.sort_by(|a, b| a.0.cmp(b.0));
                    sorted.into_iter().map(|(_, t)| t.clone()).collect()
                } else {
                    vec![]
                };
                let term = solver_state.get_term(body);
                let substitution = Substitution::new(subs);
                let substituted_term = term.subst(&substitution, &mut solver_state.context);
                deferred_instantiations.push_back(DeferredInstantiation {
                    substituted_term,
                    is_exists: quantifier_is_exists,
                    literal: quantifier_literal,
                    quantifier_id: quantifier.id,
                    generation,
                    bindings,
                    instance_id,
                });
            }
        }
    }

    PendingInstantiations {
        deferred_instantiations,
        deferred_skolemizations,
        skolemized_quantifier_idxs,
    }
}

/// Materializes the next pending instantiation or skolemization.
/// This does the expensive work: insert_predecessor, cnf_tseitin, proof steps.
/// Returns None if there's nothing left to materialize.
pub(crate) fn materialize_next(
    pending: &mut PendingInstantiations,
    solver_state: &mut SolverState,
    proof_tracer: &Rc<RefCell<SMTProofTracer>>,
) -> Option<Vec<QuantifierInstance>> {
    let ddsmt = solver_state.ddsmt;
    let lazy_dt = solver_state.lazy_dt;

    // Skolemizations first
    if let Some(deferred) = pending.deferred_skolemizations.pop_front() {
        let results = process_deferred_skolemizations(
            vec![deferred],
            solver_state,
            proof_tracer,
            ddsmt,
            lazy_dt,
        );
        return Some(results);
    }

    // Then instantiations
    if let Some(deferred) = pending.deferred_instantiations.pop_front() {
        let results = process_deferred_instantiations(
            vec![deferred],
            solver_state,
            proof_tracer,
            ddsmt,
            lazy_dt,
        );
        return Some(results);
    }

    None
}

fn process_deferred_skolemizations(
    deferred_skolemizations: Vec<DeferredSkolemization>,
    solver_state: &mut SolverState,
    proof_tracer: &Rc<RefCell<SMTProofTracer>>,
    ddsmt: bool,
    lazy_dt: bool,
) -> Vec<QuantifierInstance> {
    let mut results = vec![];
    for DeferredSkolemization {
        skolem,
        skolem_vars,
        is_exists,
        literal,
    } in deferred_skolemizations
    {
        let reduced_skolem: Term = skolem.let_elim(&mut solver_state.context);
        let reduced_skolem = reduced_skolem.nnf(solver_state);
        let additional_constraints =
            check_for_function_bool(&reduced_skolem, solver_state, true, ddsmt, lazy_dt);

        solver_state.insert_predecessor(&reduced_skolem, None, None, true);

        // Must do Tseitin *before* looking up the skolem literal — see comment on instantiation path
        let clauses = reduced_skolem.cnf_tseitin(solver_state);

        debug_println!(26, 0, "(assert {})", reduced_skolem);

        let quantifier_dimacs_literal = if is_exists { literal } else { -literal };
        if planner_trace() {
            // The skolemized body holds whenever the quantifier literal does
            let q = solver_state.get_term_from_lit(quantifier_dimacs_literal.abs());
            let guard = if quantifier_dimacs_literal > 0 {
                q.to_string()
            } else {
                format!("(not {q})")
            };
            planner_trace_fact(&format!("(=> {guard} {reduced_skolem})"), "skolem");
        }
        solver_state
            .relevancy_roots
            .push((quantifier_dimacs_literal, reduced_skolem.clone()));
        let reduced_skolem_literal = solver_state.get_lit_from_term(&reduced_skolem);
        // Must happen *after* `cnf_tseitin` so Tseitin literals are registered first
        let skolem_literal = if skolem.uid() != reduced_skolem.uid() {
            solver_state
                .get_lit_from_term_safe(&skolem)
                .unwrap_or_else(|| proof_tracer.borrow_mut().new_proof_only_literal())
        } else {
            0
        };

        proof_tracer
            .borrow_mut()
            .push_skolem_or_instantiation_derivation(
                quantifier_dimacs_literal,
                skolem_literal,
                &skolem,
                reduced_skolem_literal,
                &reduced_skolem,
                ProofStepType::Skolemization {
                    parent_term: literal,
                    skolem_vars,
                },
                Theory::Boolean,
            );

        let skolem_imp = vec![-quantifier_dimacs_literal, reduced_skolem_literal];
        let mut skolem_clauses = vec![skolem_imp];

        for clause in clauses {
            let mut c = clause.0;
            if push_literal_if_not_tautology(&mut c, -reduced_skolem_literal) {
                proof_tracer
                    .borrow_mut()
                    .add_theory_clause(&c, Theory::Boolean);
                skolem_clauses.push(c);
            }
        }

        for clause in additional_constraints {
            let mut c = clause;
            if push_literal_if_not_tautology(&mut c, -reduced_skolem_literal) {
                proof_tracer
                    .borrow_mut()
                    .add_theory_clause(&c, Theory::Boolean);
                skolem_clauses.push(c);
            }
        }

        results.push(QuantifierInstance::Skolemization {
            clauses: skolem_clauses,
        });
    }
    results
}

fn process_deferred_instantiations(
    deferred_instantiations: Vec<DeferredInstantiation>,
    solver_state: &mut SolverState,
    proof_tracer: &Rc<RefCell<SMTProofTracer>>,
    ddsmt: bool,
    lazy_dt: bool,
) -> Vec<QuantifierInstance> {
    let mut results = vec![];
    for DeferredInstantiation {
        substituted_term,
        is_exists,
        literal,
        quantifier_id,
        generation,
        bindings,
        instance_id,
    } in deferred_instantiations
    {
        let t = if is_exists {
            solver_state.context.not(substituted_term)
        } else {
            substituted_term
        };

        debug_println!(
            22,
            0,
            "We are adding the instantiation {} for quantifier {}",
            t.clone(),
            solver_state.get_term(quantifier_id),
        );

        let let_elim_term = t.let_elim(&mut solver_state.context);

        // Fold ground arithmetic that substitution creates, e.g. `(+ 3 1)` -> `4`
        let simplified_term = let_elim_term.simplify(&mut solver_state.context);
        let reduction_theory = if simplified_term.uid() == let_elim_term.uid() {
            Theory::Boolean
        } else {
            Theory::QfLia
        };

        let nnf_term = simplified_term.nnf(solver_state);
        planner_trace_eq(&t, &nnf_term, "instance");

        debug_println!(26, 4, "(assert {})", nnf_term.clone());

        // E-nodes this instance introduces inherit its generation (reset below)
        let first_term_id = solver_state.egraph.num_term_ids();
        solver_state.egraph.current_generation = generation;
        solver_state.insert_predecessor(&nnf_term, None, None, true);

        let cnf_term = nnf_term.cnf_tseitin(solver_state);

        let mut raw_clauses: Vec<Vec<i32>> = cnf_term
            .into_iter()
            .map(|x| x.into_iter().collect::<Vec<_>>())
            .collect();

        let quantifier_dimacs_literal = if is_exists { -literal } else { literal };
        let relevancy_root = solver_state.relevancy_roots.len();
        solver_state
            .relevancy_roots
            .push((quantifier_dimacs_literal, nnf_term.clone()));
        let nnf_term_literal = solver_state.get_lit_from_term(&nnf_term);
        // Must happen *after* `cnf_tseitin` so Tseitin literals are registered first.
        // The un-reduced instance only appears in the proof, so unless it already
        // has a SAT literal it gets a proof-only one that CaDiCaL never sees.
        let subst_literal = if t.uid() != nnf_term.uid() {
            solver_state
                .get_lit_from_term_safe(&t)
                .unwrap_or_else(|| proof_tracer.borrow_mut().new_proof_only_literal())
        } else {
            0
        };

        proof_tracer
            .borrow_mut()
            .push_skolem_or_instantiation_derivation(
                quantifier_dimacs_literal,
                subst_literal,
                &t,
                nnf_term_literal,
                &nnf_term,
                ProofStepType::Instantiation,
                reduction_theory,
            );

        // Assert the body only when the quantifier holds (`quantifier => body`).
        // `cnf_tseitin` appends, as its final clause, a unit clause asserting the
        // top literal unconditionally; guarding just that clause (turning it into
        // the implication `-quantifier \/ top`) is enough for soundness. The
        // remaining clauses only define fresh Tseitin variables and are valid
        // regardless of the quantifier, so they stay ungated. Gating every clause
        // instead (as the skolemization path does) suppresses all propagation of
        // the body's structure until the top literal is decided, which badly
        // hurts search.
        let top = raw_clauses
            .pop()
            .expect("cnf_tseitin always emits the top-level clause");
        debug_assert_eq!(top, vec![nnf_term_literal]);
        raw_clauses.push(vec![-quantifier_dimacs_literal, nnf_term_literal]);

        proof_tracer
            .borrow_mut()
            .push_steps(&raw_clauses, ProofStepType::TheoryClause(Theory::Boolean));

        let additional_constraints =
            check_for_function_bool(&nnf_term, solver_state, true, ddsmt, lazy_dt);
        solver_state.egraph.current_generation = 0;
        let term_ids = first_term_id..solver_state.egraph.num_term_ids();
        proof_tracer.borrow_mut().push_steps(
            &additional_constraints,
            ProofStepType::TheoryClause(Theory::Background),
        );

        let mut clauses = raw_clauses;
        clauses.extend(additional_constraints);

        results.push(QuantifierInstance::Instantiation {
            clauses,
            generation,
            quantifier_id,
            bindings,
            instance_id,
            relevancy_root,
            term_ids,
        });
    }
    results
}
