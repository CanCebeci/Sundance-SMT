// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Z3-style clause flattening of input assertions (Z3's
//! `asserted_formulas::flatten_clauses`).
//!
//! Splits conjunctions into separate assertions and distributes a disjunction
//! over a conjunction child, so `(or (and A B) (and C D))` becomes the
//! assertions `(or A C)`, `(or A D)`, `(or B C)` and `(or B D)`. Each of these
//! is a relevancy root of its own, so deciding `A` makes it relevant right away
//! instead of waiting for `B` to justify the conjunction.
//!
//! As in Z3, a conjunction is only distributed if it is not shared, i.e. it has
//! a single parent in the input assertions, or if the disjunction is binary and
//! its other disjunct is a Boolean literal. Z3 checks the reference count of the
//! inner `or` of `(not (or (not A) (not B)))`, which plays the role of the
//! NNF conjunction here. Terms are hash-consed, so parents are counted over the
//! term DAG of all input assertions before any flattening.

use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use yaspar_ir::ast::{ATerm, Context, Repr, Term, TermAllocator};

/// Number of references to each subterm of the input assertions: one per
/// parent argument position, plus one per assertion it is the root of.
pub struct ParentCounts(DeterministicHashMap<u64, usize>);

impl ParentCounts {
    pub fn new(assertions: &[Term]) -> Self {
        let mut counts = DeterministicHashMap::new();
        let mut visited = DeterministicHashSet::new();
        for t in assertions {
            *counts.entry(t.uid()).or_insert(0) += 1;
        }
        let mut stack: Vec<&Term> = assertions.iter().collect();
        while let Some(t) = stack.pop() {
            if !visited.insert(t.uid()) {
                continue;
            }
            for sub in t.repr().sub_terms() {
                *counts.entry(sub.uid()).or_insert(0) += 1;
                stack.push(sub);
            }
        }
        Self(counts)
    }

    fn is_shared(&self, term: &Term) -> bool {
        self.0.get(&term.uid()).copied().unwrap_or(0) > 1
    }
}

/// A Boolean constant or variable, possibly negated (Z3's `is_literal`).
fn is_literal(term: &Term) -> bool {
    let term = match term.repr() {
        ATerm::Not(t) => t,
        _ => term,
    };
    match term.repr() {
        ATerm::Constant(..) | ATerm::Global(..) | ATerm::Local(..) => true,
        ATerm::App(_, args, _) => args.is_empty(),
        _ => false,
    }
}

/// Whether the disjunction `disjuncts` may be distributed over its child `child`.
fn distributable(child: &Term, disjuncts: &[Term], counts: &ParentCounts) -> bool {
    if !matches!(child.repr(), ATerm::And(_)) {
        return false;
    }
    if !counts.is_shared(child) {
        return true;
    }
    disjuncts.len() == 2
        && disjuncts
            .iter()
            .any(|d| d.uid() != child.uid() && is_literal(d))
}

/// Split an NNF assertion into the assertions Z3's clause flattening produces.
pub fn flatten_clauses(term: &Term, counts: &ParentCounts, context: &mut Context) -> Vec<Term> {
    let mut clauses = vec![];
    // Reversed pushes keep the clauses in the order Z3 produces them
    let mut todo = vec![term.clone()];
    while let Some(t) = todo.pop() {
        match t.repr() {
            ATerm::And(conjuncts) => todo.extend(conjuncts.iter().rev().cloned()),
            ATerm::Or(disjuncts) => {
                let Some(i) = disjuncts
                    .iter()
                    .position(|d| distributable(d, disjuncts, counts))
                else {
                    clauses.push(t.clone());
                    continue;
                };
                let ATerm::And(conjuncts) = disjuncts[i].repr() else {
                    unreachable!()
                };
                for c in conjuncts.iter().rev() {
                    let mut clause = disjuncts.clone();
                    clause[i] = c.clone();
                    todo.push(context.or(clause));
                }
            }
            _ => clauses.push(t.clone()),
        }
    }
    clauses
}
