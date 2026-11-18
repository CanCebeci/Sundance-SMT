// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Dormant quantifier instances.
//!
//! Z3 deletes a quantifier instance (its clauses, atoms and terms) when it
//! backtracks below the level the instance was created at, and creates it again
//! only if E-matching finds its match again. Sundance's instance clauses are
//! permanent, so their atoms stay decision variables, and the search branches on
//! atoms of instances Z3 would not have at that point.
//!
//! Instead of deleting instances, they become dormant: on backtracking below the
//! level an instance was (re)activated at, its variables are deprioritized as
//! decisions (CaDiCaL decides them only once every other variable is assigned)
//! and its relevancy root is disabled, so its body feeds neither decisions nor
//! E-matching. When E-matching finds the instance's match again, the instance is
//! reactivated at the current level, as Z3 would re-create it.
//!
//! A variable is deprioritized while it was created by some instance and every
//! instance whose clauses use it is dormant. A variable created otherwise, e.g. for
//! a datatype axiom, belongs to the instances that created the terms of its atom
//! (Z3 deletes such atoms with the terms): it is deprioritized while all of them
//! are dormant. Variables of the input, and others over input terms only, never
//! are.

use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use std::ops::Range;

struct InstanceState {
    /// Level the instance was (re)activated at; None while dormant
    level: Option<usize>,
    /// Variables it uses: instance-created ones in its clauses, and others
    /// over terms it created
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
    by_level: Vec<Vec<usize>>,
    /// Variables created while materializing instances
    instance_vars: DeterministicHashSet<i32>,
    /// Variable -> number of active instances whose clauses use it
    active_users: DeterministicHashMap<i32, u32>,
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

    /// Whether `var` was created while materializing an instance
    pub(crate) fn is_instance_var(&self, var: i32) -> bool {
        self.instance_vars.contains(&var)
    }

    /// The instance that created the egraph term `term_id`, if any
    pub(crate) fn owner_of_term(&self, term_id: u32) -> Option<usize> {
        let i = self
            .term_owners
            .partition_point(|(ids, _)| ids.start <= term_id);
        let (ids, id) = self.term_owners.get(i.checked_sub(1)?)?;
        ids.contains(&term_id).then_some(*id)
    }

    /// A variable created outside instance materialization whose atom is over
    /// terms created by the instances `owners`: it belongs to them, and is
    /// deprioritized while all of them are dormant.
    pub(crate) fn add_theory_var(&mut self, var: i32, owners: &[usize], effects: &mut Effects) {
        let mut active = 0;
        for id in owners {
            if let Some(state) = self.instances.get_mut(id) {
                state.vars.push(var);
                if state.level.is_some() {
                    active += 1;
                }
            }
        }
        self.active_users.insert(var, active);
        if active == 0 && self.deprioritized.insert(var) {
            effects.deprioritize.push((var, true));
        }
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
        while self.by_level.len() <= level {
            self.by_level.push(Vec::new());
        }
        self.by_level[level].push(id);
        for &v in &state.vars {
            let users = self.active_users.entry(v).or_default();
            *users += 1;
            if *users == 1 && self.deprioritized.remove(&v) {
                effects.deprioritize.push((v, false));
            }
        }
    }

    /// Make the instances (re)activated above `level` dormant. To be applied
    /// before the relevancy filter backtracks, which would re-activate their
    /// roots.
    pub(crate) fn backtrack(&mut self, level: usize, effects: &mut Effects) {
        while self.by_level.len() > level + 1 {
            let l = self.by_level.len() - 1;
            for id in self.by_level.pop().unwrap() {
                let state = self.instances.get_mut(&id).unwrap();
                if state.level != Some(l) {
                    continue;
                }
                state.level = None;
                effects.roots.push((state.relevancy_root, false));
                for &v in &state.vars {
                    let users = self.active_users.get_mut(&v).unwrap();
                    *users -= 1;
                    if *users == 0 && self.deprioritized.insert(v) {
                        effects.deprioritize.push((v, true));
                    }
                }
            }
        }
    }
}
