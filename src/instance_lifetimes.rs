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
//! instance whose clauses use it is dormant; variables of the input or of other
//! theories never are.

use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use std::ops::Range;

struct InstanceState {
    /// Level the instance was (re)activated at; None while dormant
    level: Option<usize>,
    /// Instance-created variables its clauses use
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
}

impl InstanceLifetimes {
    /// A new instance, created at `level`, whose materialization created the
    /// variables `created` and added `clauses`.
    pub(crate) fn add(
        &mut self,
        id: usize,
        level: usize,
        created: Range<i32>,
        clauses: &[Vec<i32>],
        relevancy_root: usize,
        effects: &mut Effects,
    ) {
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
