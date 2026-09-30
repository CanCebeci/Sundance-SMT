// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Minimal relevancy filter for eager e-matching.
//!
//! Following Z3, a formula is relevant if it is a root (an input assertion, or a
//! quantifier instance or skolemization whose quantifier literal is true), or if
//! it is needed to justify the truth value of a relevant parent:
//!
//! * true `and` / false `or`: every child
//! * false `and` / true `or`: one child with that value (the first found)
//! * `not`: its child
//! * anything else is an atom: it and all its non-binder subterms are relevant
//!
//! Formulas whose value is still unassigned justify nothing yet. Eager matching
//! only starts from relevant e-nodes, so e.g. the branch of a disjunction the
//! assignment does not rely on does not feed quantifier instantiation.
//!
//! The relevant set is recomputed from scratch for each eager round, so there is
//! nothing to undo on backtracking. Complete-model rounds do not filter.

use crate::solver_state::SolverState;
use crate::utils::DeterministicHashSet;
use yaspar_ir::ast::{ATerm, Repr, Term};

/// E-graph ids of the terms relevant under the current `assignments`
/// (indexed by variable, signed by value).
pub(crate) fn relevant_enodes(
    solver_state: &SolverState,
    assignments: &[i32],
) -> DeterministicHashSet<u32> {
    let mut walker = Walker {
        solver_state,
        assignments,
        visited_formulas: DeterministicHashSet::new(),
        visited_terms: DeterministicHashSet::new(),
        relevant: DeterministicHashSet::new(),
    };
    for (guard, root) in &solver_state.relevancy_roots {
        if *guard == 0 || walker.lit_value(*guard) > 0 {
            walker.formula(root);
        }
    }
    walker.relevant
}

struct Walker<'a> {
    solver_state: &'a SolverState,
    assignments: &'a [i32],
    visited_formulas: DeterministicHashSet<u64>,
    visited_terms: DeterministicHashSet<u64>,
    relevant: DeterministicHashSet<u32>,
}

impl Walker<'_> {
    /// 1 if `lit` is true, -1 if false, 0 if unassigned.
    fn lit_value(&self, lit: i32) -> i32 {
        let assigned = self
            .assignments
            .get(lit.unsigned_abs() as usize)
            .copied()
            .unwrap_or(0);
        assigned.signum() * lit.signum()
    }

    /// Value of a formula: from its own SAT variable, or its negated child's.
    fn value(&self, formula: &Term) -> i32 {
        if let Some(var) = self.solver_state.get_lit_from_term_safe(formula) {
            self.lit_value(var)
        } else if let ATerm::Not(child) = formula.repr() {
            -self.value(child)
        } else {
            0
        }
    }

    fn formula(&mut self, formula: &Term) {
        if !self.visited_formulas.insert(formula.uid()) {
            return;
        }
        match formula.repr() {
            ATerm::And(children) => match self.value(formula) {
                1 => children.iter().for_each(|c| self.formula(c)),
                -1 => self.first_with_value(children, -1),
                _ => {}
            },
            ATerm::Or(children) => match self.value(formula) {
                1 => self.first_with_value(children, 1),
                -1 => children.iter().for_each(|c| self.formula(c)),
                _ => {}
            },
            ATerm::Not(child) => self.formula(child),
            // Quantified bodies become relevant through their instances
            ATerm::Forall(..) | ATerm::Exists(..) => {}
            _ => self.atom(formula),
        }
    }

    fn first_with_value(&mut self, children: &[Term], value: i32) {
        if let Some(child) = children.iter().find(|c| self.value(c) == value) {
            self.formula(child);
        }
    }

    /// Mark `term` and its subterms relevant, stopping at binders.
    fn atom(&mut self, term: &Term) {
        if !self.visited_terms.insert(term.uid()) {
            return;
        }
        if let Some(id) = self.solver_state.egraph_id(term.uid()) {
            self.relevant.insert(id);
        }
        match term.repr() {
            ATerm::Forall(..) | ATerm::Exists(..) | ATerm::Let(..) | ATerm::Matching(..) => {}
            repr => repr.sub_terms().for_each(|sub| self.atom(sub)),
        }
    }
}
