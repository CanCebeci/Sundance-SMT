// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Dormant quantifier instances and out-of-scope variables.
//!
//! Z3 deletes what it creates above a decision level when it backtracks below
//! it: quantifier instances (their clauses, atoms and terms) and the atoms and
//! terms its theories created, e.g. datatype accessor terms. It creates them
//! again only when needed: an instance when E-matching finds its match again, a
//! theory atom when the theory produces it again. Sundance keeps all of them, so
//! the search would branch on atoms that Z3 does not have at that point.
//!
//! Instead of deleting them, Sundance deprioritizes such variables as decisions
//! (CaDiCaL decides them only once every other variable is assigned). A variable
//! stays decidable while it is used by an active instance or is in scope:
//!
//! * An instance is active from the level it was (re)created at until
//!   backtracking below it; it is then dormant, and its relevancy root is
//!   disabled too, so its body feeds neither decisions nor E-matching. When
//!   E-matching finds its match again, it is reactivated at the current level.
//!   It uses the instance-created variables of its clauses, and the variables
//!   whose atoms are over terms it created (Z3 deletes such atoms with the
//!   terms).
//! * A variable is in scope from the level it was (re)created at until
//!   backtracking below it. It is created when first observed, and re-created
//!   when a clause handed to CaDiCaL mentions it, or when a theory would produce
//!   it again (e.g. the datatype axioms of a term, see
//!   `SolverState::recreated_vars`). A theory re-creates nothing about a term
//!   whose instances are all dormant: Z3 has deleted such a term.
//!
//! Variables created at level 0, including the input's, are always in scope.

use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use std::ops::Range;

struct InstanceState {
    /// Level the instance was (re)activated at; None while dormant
    level: Option<usize>,
    /// Variables it uses
    vars: Vec<i32>,
    /// Index of its root in `SolverState::relevancy_roots`
    relevancy_root: usize,
}

/// Changes for the propagator to make in CaDiCaL and the relevancy filter
#[derive(Default)]
pub(crate) struct Effects {
    /// (variable, deprioritized)
    pub deprioritize: Vec<(i32, bool)>,
    /// (relevancy root, enabled)
    pub roots: Vec<(usize, bool)>,
}

#[derive(Default)]
pub(crate) struct InstanceLifetimes {
    instances: DeterministicHashMap<usize, InstanceState>,
    /// Level -> instances (re)activated at that level
    instances_by_level: Vec<Vec<usize>>,
    /// Variable -> level it is in scope from (absent: out of scope)
    scope: DeterministicHashMap<i32, usize>,
    /// Level -> variables brought in scope at that level
    scope_by_level: Vec<Vec<i32>>,
    /// Variables created while materializing instances
    instance_vars: DeterministicHashSet<i32>,
    /// Variable -> number of active instances using it, plus 1 while in scope
    users: DeterministicHashMap<i32, u32>,
    /// Variables currently deprioritized in CaDiCaL
    deprioritized: DeterministicHashSet<i32>,
    /// (egraph term ids, instance) for each instance, by increasing ids
    term_owners: Vec<(Range<u32>, usize)>,
}

impl InstanceLifetimes {
    /// A new instance, created at `level`, whose materialization created the
    /// variables `created` and egraph terms `term_ids`, and added `clauses`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn add(
        &mut self,
        id: usize,
        level: usize,
        created: Range<i32>,
        clauses: &[Vec<i32>],
        relevancy_root: usize,
        term_ids: Range<u32>,
        effects: &mut Effects,
    ) {
        if !term_ids.is_empty() {
            self.term_owners.push((term_ids, id));
        }
        self.instance_vars.extend(created);
        let mut vars: Vec<i32> = clauses
            .iter()
            .flatten()
            .map(|l| l.abs())
            .filter(|v| self.instance_vars.contains(v))
            .collect();
        vars.sort_unstable();
        vars.dedup();
        self.instances.insert(
            id,
            InstanceState {
                level: None,
                vars,
                relevancy_root,
            },
        );
        self.activate(id, level, effects);
    }

    /// The instance that created the egraph term `term_id`, if any
    pub(crate) fn owner_of_term(&self, term_id: u32) -> Option<usize> {
        let i = self
            .term_owners
            .partition_point(|(ids, _)| ids.start <= term_id);
        let (ids, id) = self.term_owners.get(i.checked_sub(1)?)?;
        ids.contains(&term_id).then_some(*id)
    }

    /// Whether instance `id` is active (not dormant)
    pub(crate) fn is_active(&self, id: usize) -> bool {
        self.instances
            .get(&id)
            .is_some_and(|state| state.level.is_some())
    }

    /// Whether `var` was created while materializing an instance
    pub(crate) fn is_instance_var(&self, var: i32) -> bool {
        self.instance_vars.contains(&var)
    }

    /// A variable just created at `level`: it is in scope. If it was created
    /// outside instance materialization (e.g. for a datatype axiom) and its atom
    /// is over terms created by the instances `owners`, it is also used by them.
    pub(crate) fn add_var(&mut self, var: i32, level: usize, owners: &[usize], effects: &mut Effects) {
        let owners = if self.is_instance_var(var) { &[][..] } else { owners };
        for id in owners {
            if let Some(state) = self.instances.get_mut(id)
                && !state.vars.contains(&var)
            {
                state.vars.push(var);
                if state.level.is_some() {
                    self.use_var(var, effects);
                }
            }
        }
        self.recreate(var, level, effects);
    }

    /// `var` is (re)created at `level`: it is in scope from there
    pub(crate) fn recreate(&mut self, var: i32, level: usize, effects: &mut Effects) {
        if self.scope.get(&var).is_some_and(|&l| l <= level) {
            return;
        }
        if self.scope.insert(var, level).is_none() {
            self.use_var(var, effects);
        }
        while self.scope_by_level.len() <= level {
            self.scope_by_level.push(Vec::new());
        }
        self.scope_by_level[level].push(var);
    }

    /// E-matching found the match of instance `id` again at `level`
    pub(crate) fn rematched(&mut self, id: usize, level: usize, effects: &mut Effects) {
        if let Some(state) = self.instances.get(&id)
            && state.level.is_none()
        {
            effects.roots.push((state.relevancy_root, true));
            self.activate(id, level, effects);
        }
    }

    fn activate(&mut self, id: usize, level: usize, effects: &mut Effects) {
        let state = self.instances.get_mut(&id).unwrap();
        state.level = Some(level);
        while self.instances_by_level.len() <= level {
            self.instances_by_level.push(Vec::new());
        }
        self.instances_by_level[level].push(id);
        let vars = state.vars.clone();
        for v in vars {
            self.use_var(v, effects);
        }
    }

    fn use_var(&mut self, var: i32, effects: &mut Effects) {
        let users = self.users.entry(var).or_default();
        *users += 1;
        if *users == 1 && self.deprioritized.remove(&var) {
            effects.deprioritize.push((var, false));
        }
    }

    fn unuse_var(&mut self, var: i32, effects: &mut Effects) {
        let users = self.users.get_mut(&var).unwrap();
        *users -= 1;
        if *users == 0 && self.deprioritized.insert(var) {
            effects.deprioritize.push((var, true));
        }
    }

    /// Make the instances (re)activated and the variables brought in scope above
    /// `level` dormant and out of scope. To be applied before the relevancy filter
    /// backtracks, which would re-activate the instances' roots.
    pub(crate) fn backtrack(&mut self, level: usize, effects: &mut Effects) {
        while self.instances_by_level.len() > level + 1 {
            let l = self.instances_by_level.len() - 1;
            for id in self.instances_by_level.pop().unwrap() {
                let state = self.instances.get_mut(&id).unwrap();
                if state.level != Some(l) {
                    continue;
                }
                state.level = None;
                effects.roots.push((state.relevancy_root, false));
                let vars = state.vars.clone();
                for v in vars {
                    self.unuse_var(v, effects);
                }
            }
        }
        while self.scope_by_level.len() > level + 1 {
            let l = self.scope_by_level.len() - 1;
            for v in self.scope_by_level.pop().unwrap() {
                if self.scope.get(&v) == Some(&l) {
                    self.scope.remove(&v);
                    self.unuse_var(v, effects);
                }
            }
        }
    }
}
