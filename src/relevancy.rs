// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Incremental relevancy filter for eager e-matching.
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
//! The relevant set is maintained incrementally, as in Z3's relevancy
//! propagation: a relevant formula that cannot justify anything yet watches the
//! variables that decide it, and is revisited when one is assigned. Every change
//! is recorded on a trail and undone on backtracking. Like the propagator's
//! `assignments`, all changes belong to the decision level at which they are
//! made. Once a false `and` / true `or` has picked its child, it keeps it until
//! backtracking, even if an earlier child takes the same value later.
//!
//! Complete-model rounds do not filter.

use crate::solver_state::SolverState;
use crate::utils::{FastDeterministicHashMap, FastDeterministicHashSet};
use yaspar_ir::ast::{ATerm, Repr, Term};

struct Node {
    term: Term,
    /// Formula nodes of the children of `and`, `or` and `not`
    children: Vec<u32>,
    relevant: bool,
    /// Justified its value: the children it needs are marked relevant
    expanded: bool,
    /// Watches its own variable, waiting for a value
    watching_self: bool,
    /// Watches its children's variables, waiting for one with the right value
    watching_children: bool,
}

struct Root {
    /// 0 for roots that are always relevant
    guard: i32,
    node: u32,
    active: bool,
}

enum Undo {
    Relevant(u32),
    Expanded(u32),
    WatchingSelf(u32),
    WatchingChildren(u32),
    /// Pop the last watch of this variable
    Watch(usize),
    AtomTerm(u64),
    Enode(u32),
    RootActive(u32),
}

pub(crate) struct Relevancy {
    nodes: Vec<Node>,
    node_ids: FastDeterministicHashMap<u64, u32>,
    /// Terms marked relevant as (sub)terms of atoms
    atom_terms: FastDeterministicHashSet<u64>,
    /// E-graph ids of all relevant terms
    enodes: FastDeterministicHashSet<u32>,
    /// Variable -> nodes to revisit when it is assigned (trailed)
    watches: Vec<Vec<u32>>,
    roots: Vec<Root>,
    /// Prefix of `SolverState::relevancy_roots` already registered
    roots_seen: usize,
    /// Guard variable -> roots it activates (roots are permanent, so these are not trailed)
    guard_watches: Vec<Vec<u32>>,
    trail: Vec<Undo>,
    /// `level_starts[l]` is the trail length when decision level `l + 1` began
    level_starts: Vec<usize>,
    queue: Vec<u32>,
}

/// 1 if `lit` is true, -1 if false, 0 if unassigned.
fn lit_value(assignments: &[i32], lit: i32) -> i32 {
    let assigned = assignments
        .get(lit.unsigned_abs() as usize)
        .copied()
        .unwrap_or(0);
    assigned.signum() * lit.signum()
}

impl Relevancy {
    pub(crate) fn new() -> Self {
        Relevancy {
            nodes: Vec::new(),
            node_ids: FastDeterministicHashMap::default(),
            atom_terms: FastDeterministicHashSet::default(),
            enodes: FastDeterministicHashSet::default(),
            watches: Vec::new(),
            roots: Vec::new(),
            roots_seen: 0,
            guard_watches: Vec::new(),
            trail: Vec::new(),
            level_starts: Vec::new(),
            queue: Vec::new(),
        }
    }

    /// E-graph ids of the terms relevant under the current assignment.
    pub(crate) fn enodes(&self) -> &FastDeterministicHashSet<u32> {
        &self.enodes
    }

    pub(crate) fn new_decision_level(&mut self) {
        self.level_starts.push(self.trail.len());
    }

    /// Undo everything above `level`. Call after the assignments above `level`
    /// have been cleared.
    pub(crate) fn backtrack(
        &mut self,
        level: usize,
        solver_state: &SolverState,
        assignments: &[i32],
    ) {
        let Some(&start) = self.level_starts.get(level) else {
            return;
        };
        self.level_starts.truncate(level);
        let mut deactivated = vec![];
        while self.trail.len() > start {
            match self.trail.pop().unwrap() {
                Undo::Relevant(n) => self.nodes[n as usize].relevant = false,
                Undo::Expanded(n) => self.nodes[n as usize].expanded = false,
                Undo::WatchingSelf(n) => self.nodes[n as usize].watching_self = false,
                Undo::WatchingChildren(n) => self.nodes[n as usize].watching_children = false,
                Undo::Watch(var) => {
                    self.watches[var].pop();
                }
                Undo::AtomTerm(uid) => {
                    self.atom_terms.remove(&uid);
                }
                Undo::Enode(id) => {
                    self.enodes.remove(&id);
                }
                Undo::RootActive(r) => {
                    self.roots[r as usize].active = false;
                    deactivated.push(r);
                }
            }
        }
        // A root added above `level` may have a guard that is still true
        for r in deactivated.into_iter().rev() {
            self.try_activate(r, assignments);
        }
        self.propagate(solver_state, assignments);
    }

    /// Register roots added to `solver_state.relevancy_roots` since the last call.
    pub(crate) fn sync_roots(&mut self, solver_state: &SolverState, assignments: &[i32]) {
        while self.roots_seen < solver_state.relevancy_roots.len() {
            let (guard, term) = &solver_state.relevancy_roots[self.roots_seen];
            self.roots_seen += 1;
            let r = self.roots.len() as u32;
            let node = self.node(term);
            self.roots.push(Root {
                guard: *guard,
                node,
                active: false,
            });
            if *guard != 0 {
                let var = guard.unsigned_abs() as usize;
                if self.guard_watches.len() <= var {
                    self.guard_watches.resize_with(var + 1, Vec::new);
                }
                self.guard_watches[var].push(r);
            }
            self.try_activate(r, assignments);
        }
        self.propagate(solver_state, assignments);
    }

    /// Revisit what waits on the variables of `lits`, which `assignments` already holds.
    pub(crate) fn on_assignments(
        &mut self,
        lits: &[i32],
        solver_state: &SolverState,
        assignments: &[i32],
    ) {
        for lit in lits {
            let var = lit.unsigned_abs() as usize;
            if let Some(watching) = self.watches.get(var) {
                self.queue.extend_from_slice(watching);
            }
            for i in 0..self.guard_watches.get(var).map_or(0, Vec::len) {
                let r = self.guard_watches[var][i];
                self.try_activate(r, assignments);
            }
        }
        self.propagate(solver_state, assignments);
    }

    fn try_activate(&mut self, r: u32, assignments: &[i32]) {
        let root = &self.roots[r as usize];
        if root.active || (root.guard != 0 && lit_value(assignments, root.guard) <= 0) {
            return;
        }
        let node = root.node;
        self.roots[r as usize].active = true;
        self.trail.push(Undo::RootActive(r));
        self.mark(node);
    }

    /// The node of a formula, created on first use.
    fn node(&mut self, term: &Term) -> u32 {
        if let Some(&n) = self.node_ids.get(&term.uid()) {
            return n;
        }
        let children = match term.repr() {
            ATerm::And(children) | ATerm::Or(children) => {
                children.iter().map(|c| self.node(c)).collect()
            }
            ATerm::Not(child) => vec![self.node(child)],
            _ => vec![],
        };
        let n = self.nodes.len() as u32;
        self.nodes.push(Node {
            term: term.clone(),
            children,
            relevant: false,
            expanded: false,
            watching_self: false,
            watching_children: false,
        });
        self.node_ids.insert(term.uid(), n);
        n
    }

    fn mark(&mut self, n: u32) {
        let node = &mut self.nodes[n as usize];
        if !node.relevant {
            node.relevant = true;
            self.trail.push(Undo::Relevant(n));
            self.queue.push(n);
        }
    }

    /// The literal deciding a formula's value: its own SAT literal, or its
    /// negated child's.
    fn value_lit(&self, solver_state: &SolverState, n: u32) -> Option<i32> {
        let node = &self.nodes[n as usize];
        if let Some(lit) = solver_state.get_lit_from_term_safe(&node.term) {
            Some(lit)
        } else if let ATerm::Not(_) = node.term.repr() {
            self.value_lit(solver_state, node.children[0])
                .map(|lit| -lit)
        } else {
            None
        }
    }

    fn value(&self, solver_state: &SolverState, assignments: &[i32], n: u32) -> i32 {
        self.value_lit(solver_state, n)
            .map_or(0, |lit| lit_value(assignments, lit))
    }

    fn watch(&mut self, solver_state: &SolverState, n: u32, watched: u32) {
        if let Some(lit) = self.value_lit(solver_state, watched) {
            let var = lit.unsigned_abs() as usize;
            if self.watches.len() <= var {
                self.watches.resize_with(var + 1, Vec::new);
            }
            self.watches[var].push(n);
            self.trail.push(Undo::Watch(var));
        }
    }

    fn propagate(&mut self, solver_state: &SolverState, assignments: &[i32]) {
        while let Some(n) = self.queue.pop() {
            self.visit(solver_state, assignments, n);
        }
    }

    /// Justify a relevant formula's value as far as the assignment allows.
    fn visit(&mut self, solver_state: &SolverState, assignments: &[i32], n: u32) {
        let node = &self.nodes[n as usize];
        if !node.relevant || node.expanded {
            return;
        }
        let is_and = match node.term.repr() {
            ATerm::And(_) => true,
            ATerm::Or(_) => false,
            ATerm::Not(_) => {
                let child = node.children[0];
                self.expand(n);
                self.mark(child);
                return;
            }
            // Quantified bodies become relevant through their instances
            ATerm::Forall(..) | ATerm::Exists(..) => {
                self.expand(n);
                return;
            }
            _ => {
                let term = node.term.clone();
                self.expand(n);
                self.atom(solver_state, &term);
                return;
            }
        };
        let value = self.value(solver_state, assignments, n);
        if value == 0 {
            if !self.nodes[n as usize].watching_self {
                self.nodes[n as usize].watching_self = true;
                self.trail.push(Undo::WatchingSelf(n));
                self.watch(solver_state, n, n);
            }
            return;
        }
        let children = self.nodes[n as usize].children.clone();
        // A true `and` or a false `or` needs every child
        if (value > 0) == is_and {
            self.expand(n);
            for c in children {
                self.mark(c);
            }
            return;
        }
        if let Some(&c) = children
            .iter()
            .find(|&&c| self.value(solver_state, assignments, c) == value)
        {
            self.expand(n);
            self.mark(c);
        } else if !self.nodes[n as usize].watching_children {
            self.nodes[n as usize].watching_children = true;
            self.trail.push(Undo::WatchingChildren(n));
            for c in children {
                self.watch(solver_state, n, c);
            }
        }
    }

    fn expand(&mut self, n: u32) {
        self.nodes[n as usize].expanded = true;
        self.trail.push(Undo::Expanded(n));
    }

    /// Mark `term` and its subterms relevant, stopping at binders.
    fn atom(&mut self, solver_state: &SolverState, term: &Term) {
        let mut stack = vec![term.clone()];
        while let Some(term) = stack.pop() {
            if !self.atom_terms.insert(term.uid()) {
                continue;
            }
            self.trail.push(Undo::AtomTerm(term.uid()));
            if let Some(id) = solver_state.egraph_id(term.uid())
                && self.enodes.insert(id)
            {
                self.trail.push(Undo::Enode(id));
            }
            match term.repr() {
                ATerm::Forall(..) | ATerm::Exists(..) | ATerm::Let(..) | ATerm::Matching(..) => {}
                repr => stack.extend(repr.sub_terms().cloned()),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Relevancy;
    use crate::cnf::CNFConversion;
    use crate::solver_state::SolverState;
    use yaspar_ir::ast::{Context, ObjectAllocatorExt, Term, TermAllocator};

    struct Setup {
        state: SolverState,
        relevancy: Relevancy,
        assignments: Vec<i32>,
        level: usize,
    }

    impl Setup {
        fn new() -> Self {
            Setup {
                state: SolverState::new(Context::default(), false, false, false, false),
                relevancy: Relevancy::new(),
                assignments: vec![0; 64],
                level: 0,
            }
        }

        fn var(&mut self, name: &str) -> Term {
            self.state.context.simple_symbol(name)
        }

        /// Give `term` and its subformulas SAT literals.
        fn encode(&mut self, term: &Term) -> i32 {
            term.cnf_tseitin(&mut self.state);
            self.state.get_lit_from_term(term)
        }

        fn add_root(&mut self, guard: i32, term: &Term) {
            self.encode(term);
            self.state.relevancy_roots.push((guard, term.clone()));
            self.relevancy.sync_roots(&self.state, &self.assignments);
        }

        fn decide(&mut self) {
            self.level += 1;
            self.relevancy.new_decision_level();
        }

        fn assign(&mut self, term: &Term, value: bool) {
            let lit = self.encode(term);
            let lit = if value { lit } else { -lit };
            self.assignments[lit.unsigned_abs() as usize] = (self.level as i32 + 1) * lit.signum();
            self.relevancy
                .on_assignments(&[lit], &self.state, &self.assignments);
        }

        fn backtrack(&mut self, level: usize) {
            for a in self.assignments.iter_mut() {
                if a.unsigned_abs() as usize > level + 1 {
                    *a = 0;
                }
            }
            self.level = level;
            self.relevancy
                .backtrack(level, &self.state, &self.assignments);
        }

        fn relevant(&self, term: &Term) -> bool {
            self.relevancy.atom_terms.contains(&term.uid())
        }
    }

    #[test]
    fn true_or_keeps_its_branch_until_backtracking() {
        let mut s = Setup::new();
        let (a, b) = (s.var("a"), s.var("b"));
        let or = s.state.context.or(vec![a.clone(), b.clone()]);
        s.add_root(0, &or);
        s.assign(&or, true);
        assert!(!s.relevant(&a) && !s.relevant(&b));

        s.decide();
        s.assign(&b, true);
        assert!(s.relevant(&b) && !s.relevant(&a));

        // `a` comes first, but `b` already justifies the disjunction
        s.decide();
        s.assign(&a, true);
        assert!(s.relevant(&b) && !s.relevant(&a));

        s.backtrack(0);
        assert!(!s.relevant(&a) && !s.relevant(&b));
        s.decide();
        s.assign(&a, true);
        assert!(s.relevant(&a) && !s.relevant(&b));
    }

    #[test]
    fn false_and_waits_for_a_false_child() {
        let mut s = Setup::new();
        let (a, b, c) = (s.var("a"), s.var("b"), s.var("c"));
        let and = s.state.context.and(vec![a.clone(), b.clone()]);
        let or = s.state.context.or(vec![and.clone(), c.clone()]);
        s.add_root(0, &or);
        s.decide();
        // A false disjunction needs every disjunct, so the false `and` is relevant
        s.assign(&or, false);
        s.assign(&and, false);
        s.assign(&c, false);
        assert!(s.relevant(&c));
        assert!(!s.relevant(&a) && !s.relevant(&b));
        s.decide();
        s.assign(&b, false);
        assert!(s.relevant(&b) && !s.relevant(&a));
        s.backtrack(1);
        assert!(!s.relevant(&b));
        s.assign(&a, false);
        assert!(s.relevant(&a) && !s.relevant(&b));
    }

    #[test]
    fn root_added_above_its_guard_survives_backtracking_to_the_guard() {
        let mut s = Setup::new();
        let (g, a) = (s.var("g"), s.var("a"));
        let guard = s.encode(&g);
        s.decide();
        s.assign(&g, true);
        s.decide();
        s.add_root(guard, &a);
        assert!(s.relevant(&a));

        s.backtrack(1);
        assert!(s.relevant(&a));
        s.backtrack(0);
        assert!(!s.relevant(&a));
        s.decide();
        s.assign(&g, true);
        assert!(s.relevant(&a));
    }
}
