// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Ground arithmetic simplification.
//!
//! Folds integer `+`, `-` and `*` whose arguments are all integer literals, e.g.
//! `(<= (h (+ 2 1)) (f (+ (+ 2 1) 1)))` becomes `(<= (h 3) (f 4))`, and
//! comparisons (`<=`, `<`, `>=`, `>`, `=`) of integer literals to `true` or
//! `false`, as Z3's rewriter does: e.g. `(<= 0 1)` in a quantifier instance
//! would otherwise be a fresh atom that only a decision can assign. Terms are
//! hash-consed, so a folded term is the very term the input already contains and
//! shares its e-graph node and CNF variable, letting Boolean propagation relate the
//! two directly instead of leaving it to arithmetic conflicts.

use crate::utils::FastDeterministicHashMap;
use dashu::integer::IBig;
use yaspar_ir::ast::alg::Constant;
use yaspar_ir::ast::{ATerm, CheckedApi, Context, ObjectAllocatorExt, Repr, Term, TermAllocator};

pub trait ArithSimplify {
    /// Fold ground integer arithmetic, bottom-up.
    ///
    /// Descends through applications, `=`, `distinct`, the Boolean connectives and `ite`, and
    /// stops at binders (`let`, quantifiers, `match`) and annotations. Only `Int`-sorted `+`, `-`
    /// and `*` over integer literals (numerals and `(- numeral)`) fold, as do `<=`, `<`, `>=`,
    /// `>` and `=` over integer literals; `div`, `mod`, `abs`, `/` and reals are left alone.
    /// Returns the term unchanged (same uid) when nothing folds.
    fn simplify(&self, context: &mut Context) -> Self;
}

impl ArithSimplify for Term {
    fn simplify(&self, context: &mut Context) -> Term {
        simplify_rec(self, context, &mut FastDeterministicHashMap::default())
    }
}

fn simplify_rec(
    term: &Term,
    ctx: &mut Context,
    cache: &mut FastDeterministicHashMap<u64, Term>,
) -> Term {
    if let Some(cached) = cache.get(&term.uid()) {
        return cached.clone();
    }
    let mut go = |t: &Term, ctx: &mut Context| simplify_rec(t, ctx, cache);
    let result = match term.repr() {
        ATerm::App(id, args, sort) => {
            let args: Vec<Term> = args.iter().map(|a| go(a, ctx)).collect();
            let int_sort = ctx.int_sort();
            let symbol = id.0.symbol.as_str();
            if let Some(b) = fold_int_comparison(symbol, &args) {
                ctx.bool(b)
            } else {
                match fold_int_app(symbol, &args) {
                    Some(n) if sort.as_ref() == Some(&int_sort) => ctx
                        .integer(n)
                        .expect("Int-sorted term implies Int is supported"),
                    _ => ctx.app(id.clone(), args, sort.clone()),
                }
            }
        }
        ATerm::Eq(a, b) => {
            let (a, b) = (go(a, ctx), go(b, ctx));
            match (int_literal(&a), int_literal(&b)) {
                (Some(x), Some(y)) => ctx.bool(x == y),
                _ => ctx.eq(a, b),
            }
        }
        ATerm::Distinct(ts) => {
            let ts = ts.iter().map(|t| go(t, ctx)).collect();
            ctx.distinct(ts)
        }
        ATerm::And(ts) => {
            let ts = ts.iter().map(|t| go(t, ctx)).collect();
            ctx.and(ts)
        }
        ATerm::Or(ts) => {
            let ts = ts.iter().map(|t| go(t, ctx)).collect();
            ctx.or(ts)
        }
        ATerm::Xor(ts) => {
            let ts = ts.iter().map(|t| go(t, ctx)).collect();
            ctx.xor(ts)
        }
        ATerm::Not(t) => {
            let t = go(t, ctx);
            ctx.not(t)
        }
        ATerm::Implies(ts, t) => {
            let ts = ts.iter().map(|t| go(t, ctx)).collect();
            let t = go(t, ctx);
            ctx.implies(ts, t)
        }
        ATerm::Ite(b, t, e) => {
            let (b, t, e) = (go(b, ctx), go(t, ctx), go(e, ctx));
            ctx.ite(b, t, e)
        }
        ATerm::Constant(..)
        | ATerm::Global(..)
        | ATerm::Local(..)
        | ATerm::Let(..)
        | ATerm::Exists(..)
        | ATerm::Forall(..)
        | ATerm::Matching(..)
        | ATerm::Annotated(..) => term.clone(),
    };
    cache.insert(term.uid(), result.clone());
    result
}

/// Value of `symbol` applied to `args` if every argument is an integer literal.
fn fold_int_app(symbol: &str, args: &[Term]) -> Option<IBig> {
    if !matches!(symbol, "+" | "-" | "*") {
        return None;
    }
    let vals = args
        .iter()
        .map(int_literal)
        .collect::<Option<Vec<IBig>>>()?;
    match (symbol, vals.as_slice()) {
        ("+", _) => Some(vals.iter().sum()),
        ("*", _) => Some(vals.iter().product()),
        ("-", [v]) => Some(-v.clone()),
        ("-", [first, rest @ ..]) => Some(rest.iter().fold(first.clone(), |acc, v| acc - v)),
        _ => None,
    }
}

/// Value of the (chainable) comparison `symbol` over `args` if every argument is
/// an integer literal.
fn fold_int_comparison(symbol: &str, args: &[Term]) -> Option<bool> {
    let holds: fn(&IBig, &IBig) -> bool = match symbol {
        "<=" => |a, b| a <= b,
        "<" => |a, b| a < b,
        ">=" => |a, b| a >= b,
        ">" => |a, b| a > b,
        _ => return None,
    };
    if args.len() < 2 {
        return None;
    }
    let vals = args
        .iter()
        .map(int_literal)
        .collect::<Option<Vec<IBig>>>()?;
    Some(vals.windows(2).all(|w| holds(&w[0], &w[1])))
}

/// `n` for a numeral and `-n` for `(- numeral)`, the two shapes `Context::integer` emits.
fn int_literal(term: &Term) -> Option<IBig> {
    match term.repr() {
        ATerm::Constant(Constant::Numeral(n), _) => Some(IBig::from(n.clone())),
        ATerm::App(id, args, _) if id.0.symbol.as_str() == "-" && args.len() == 1 => {
            match args[0].repr() {
                ATerm::Constant(Constant::Numeral(n), _) => Some(-IBig::from(n.clone())),
                _ => None,
            }
        }
        _ => None,
    }
}
