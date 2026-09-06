//! Oracle-based fuzz for zipper movement and iteration.  The oracle is the sorted key set itself:
//! every movement op is modelled on it (see `Model`), matching `lean/PathMapModel/Zipper.lean`.
//! Defaults are small for CI; set FUZZ_SEEDS / FUZZ_OPS / FUZZ_START to scale, FUZZ_EXISTING_ONLY=1
//! to stay on existing paths, FUZZ_MINIMIZE=<seed> to shrink a failure, FUZZ_REPORT=1 for a per-seed table.

use std::collections::BTreeSet;
use std::ops::Bound::{Excluded, Unbounded};
use pathmap::PathMap;
use pathmap::zipper::*;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Rng(seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(0xD1B54A32D192ED03) | 1) }
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    fn below(&mut self, n: usize) -> usize { (self.next() % (n as u64)) as usize }
    fn chance(&mut self, pct: u64) -> bool { self.next() % 100 < pct }
}

struct Model {
    keys: BTreeSet<Vec<u8>>,
    paths: BTreeSet<Vec<u8>>,
}

fn sw(a: &[u8], b: &[u8]) -> bool { a.len() >= b.len() && &a[..b.len()] == b }

impl Model {
    fn new(keys: &[Vec<u8>]) -> Self {
        let mut paths = BTreeSet::new();
        for k in keys {
            for i in 0..=k.len() { paths.insert(k[..i].to_vec()); }
        }
        Model { keys: keys.iter().cloned().collect(), paths }
    }
    fn exists(&self, p: &[u8]) -> bool { self.paths.contains(p) }
    fn is_val(&self, p: &[u8]) -> bool { self.keys.contains(p) }
    fn children(&self, p: &[u8]) -> Vec<u8> {
        self.paths.range::<[u8], _>((Excluded(p), Unbounded))
            .take_while(|q| sw(q, p))
            .filter(|q| q.len() == p.len() + 1)
            .map(|q| q[p.len()])
            .collect()
    }
    fn next_val(&self, p: &[u8]) -> Option<Vec<u8>> {
        self.keys.range::<[u8], _>((Excluded(p), Unbounded)).next().cloned()
    }
    fn next_path(&self, p: &[u8]) -> Option<Vec<u8>> {
        self.paths.range::<[u8], _>((Excluded(p), Unbounded)).next().cloned()
    }
    fn first_k_path(&self, p: &[u8], k: usize) -> Option<Vec<u8>> {
        self.paths.range::<[u8], _>((Excluded(p), Unbounded))
            .take_while(|q| sw(q, p))
            .find(|q| q.len() == p.len() + k).cloned()
    }
    fn next_k_path(&self, p: &[u8], k: usize) -> Option<Vec<u8>> {
        let base = &p[..p.len() - k];
        self.paths.range::<[u8], _>((Excluded(p), Unbounded))
            .take_while(|q| sw(q, base))
            .find(|q| q.len() == p.len()).cloned()
    }
}

#[derive(Debug, Clone)]
enum Op {
    DescendToByte(u8),
    DescendToExistingByte(u8),
    DescendTo(Vec<u8>),
    DescendFirstByte,
    DescendLastByte,
    DescendIndexedByte(usize),
    DescendUntil,
    ToNextSibling,
    ToPrevSibling,
    Ascend(usize),
    AscendByte,
    AscendUntil,
    AscendUntilBranch,
    ToNextVal,
    ToNextStep,
    DescendFirstKPath(usize),
    ToNextKPath(usize),
    MoveToPath(Vec<u8>),
    Reset,
    DescendUntilMaxBytes(usize),
    DescendToCheck(Vec<u8>),
    DescendLastPath,
    ToNextValObs,
    ToNextStepObs,
    DescendUntilObs,
    DescendFirstKPathObs(usize),
    ToNextKPathObs(usize),
}

fn existing_only() -> bool { std::env::var("FUZZ_EXISTING_ONLY").is_ok() }

fn gen_op(rng: &mut Rng, alphabet: usize, model: &Model, p: &[u8]) -> Op {
    let r = rng.below(130);
    let rb = |rng: &mut Rng| -> u8 { if rng.chance(85) { rng.below(alphabet) as u8 } else { rng.below(256) as u8 } };
    let eo = existing_only();
    match r {
        0..=7 => {
            if eo {
                let c = model.children(p);
                if c.is_empty() { Op::DescendFirstByte } else { Op::DescendToByte(c[rng.below(c.len())]) }
            } else { Op::DescendToByte(rb(rng)) }
        },
        8..=12 => Op::DescendToExistingByte(rb(rng)),
        13..=16 => {
            let n = 1 + rng.below(4);
            if eo {
                let mut q = p.to_vec(); let mut ext = vec![];
                for _ in 0..n { let c = model.children(&q); if c.is_empty() { break } let b = c[rng.below(c.len())]; q.push(b); ext.push(b); }
                if ext.is_empty() { Op::DescendFirstByte } else { Op::DescendTo(ext) }
            } else { Op::DescendTo((0..n).map(|_| rb(rng)).collect()) }
        },
        17..=26 => Op::DescendFirstByte,
        27..=29 => Op::DescendLastByte,
        30..=32 => Op::DescendIndexedByte(rng.below(4)),
        33..=36 => Op::DescendUntil,
        37..=48 => Op::ToNextSibling,
        49..=51 => Op::ToPrevSibling,
        52..=55 => Op::Ascend(1 + rng.below(4)),
        56..=63 => Op::AscendByte,
        64..=66 => Op::AscendUntil,
        67..=69 => Op::AscendUntilBranch,
        70..=81 => Op::ToNextVal,
        82..=87 => Op::ToNextStep,
        88..=91 => Op::DescendFirstKPath(1 + rng.below(4)),
        92..=96 => Op::ToNextKPath(1 + rng.below(p.len().max(1)).min(4)),
        97 => {
            // Move to a random existing path, or a random path
            let v: Vec<Vec<u8>> = model.paths.iter().cloned().collect();
            if (eo || rng.chance(70)) && !v.is_empty() { Op::MoveToPath(v[rng.below(v.len())].clone()) }
            else { let n = rng.below(5); Op::MoveToPath((0..n).map(|_| rb(rng)).collect()) }
        },
        98..=99 => Op::Reset,
        100..=103 => Op::DescendUntilMaxBytes(rng.below(4)),
        104..=106 => {
            let n = 1 + rng.below(3);
            if eo {
                let mut q = p.to_vec(); let mut ext = vec![];
                for _ in 0..n { let c = model.children(&q); if c.is_empty() { break } let b = c[rng.below(c.len())]; q.push(b); ext.push(b); }
                if ext.is_empty() { Op::DescendFirstByte } else { Op::DescendToCheck(ext) }
            } else { Op::DescendToCheck((0..n).map(|_| rb(rng)).collect()) }
        },
        107..=109 => Op::DescendLastPath,
        110..=115 => Op::ToNextValObs,
        116..=119 => Op::ToNextStepObs,
        120..=122 => Op::DescendUntilObs,
        123..=125 => Op::DescendFirstKPathObs(1 + rng.below(4)),
        _ => Op::ToNextKPathObs(1 + rng.below(p.len().max(1)).min(4)),
    }
}

fn descend_until_model(model: &Model, q: &mut Vec<u8>) -> bool {
    let mut moved = false;
    if model.exists(q) {
        loop {
            let c = model.children(q);
            if c.len() != 1 { break }
            q.push(c[0]); moved = true;
            if model.is_val(q) { break }
        }
    }
    moved
}

/// Applies `op` to the zipper and to the model path `p`; returns a description of a mismatch, if any.
fn apply<Z: ZipperMoving + ZipperIteration + ZipperPath>(z: &mut Z, model: &Model, p: &mut Vec<u8>, op: &Op) -> Result<(), String> {
    match op {
        Op::DescendToByte(b) => { z.descend_to_byte(*b); p.push(*b); },
        Op::DescendToExistingByte(b) => {
            let mut q = p.clone(); q.push(*b);
            let expect = model.exists(&q);
            let got = z.descend_to_existing_byte(*b);
            if got != expect { return Err(format!("descend_to_existing_byte({b}) returned {got}, expected {expect}")) }
            if expect { *p = q; }
        },
        Op::DescendTo(k) => { z.descend_to(k); p.extend(k); },
        Op::DescendFirstByte => {
            let expect = model.children(p).first().copied();
            let got = z.descend_first_byte();
            if got != expect { return Err(format!("descend_first_byte returned {got:?}, expected {expect:?}")) }
            if let Some(b) = expect { p.push(b); }
        },
        Op::DescendLastByte => {
            let expect = model.children(p).last().copied();
            let got = z.descend_last_byte();
            if got != expect { return Err(format!("descend_last_byte returned {got:?}, expected {expect:?}")) }
            if let Some(b) = expect { p.push(b); }
        },
        Op::DescendIndexedByte(i) => {
            let expect = model.children(p).get(*i).copied();
            let got = z.descend_indexed_byte(*i);
            if got != expect { return Err(format!("descend_indexed_byte({i}) returned {got:?}, expected {expect:?}")) }
            if let Some(b) = expect { p.push(b); }
        },
        Op::DescendUntil => {
            let mut q = p.clone();
            let mut moved = false;
            if model.exists(&q) {
                loop {
                    let c = model.children(&q);
                    if c.len() != 1 { break }
                    q.push(c[0]); moved = true;
                    if model.is_val(&q) { break }
                }
            }
            let got = z.descend_until();
            if got != moved { return Err(format!("descend_until returned {got}, expected {moved}")) }
            *p = q;
        },
        Op::ToNextSibling => {
            let expect = if p.is_empty() { None } else {
                let last = *p.last().unwrap();
                model.children(&p[..p.len()-1]).into_iter().find(|b| *b > last)
            };
            let got = z.to_next_sibling_byte();
            if got != expect { return Err(format!("to_next_sibling_byte returned {got:?}, expected {expect:?}")) }
            if let Some(b) = expect { *p.last_mut().unwrap() = b; }
        },
        Op::ToPrevSibling => {
            let expect = if p.is_empty() { None } else {
                let last = *p.last().unwrap();
                model.children(&p[..p.len()-1]).into_iter().rev().find(|b| *b < last)
            };
            let got = z.to_prev_sibling_byte();
            if got != expect { return Err(format!("to_prev_sibling_byte returned {got:?}, expected {expect:?}")) }
            if let Some(b) = expect { *p.last_mut().unwrap() = b; }
        },
        Op::Ascend(n) => {
            let expect = (*n).min(p.len());
            let got = z.ascend(*n);
            if got != expect { return Err(format!("ascend({n}) returned {got}, expected {expect}")) }
            p.truncate(p.len() - expect);
        },
        Op::AscendByte => {
            let expect = !p.is_empty();
            let got = z.ascend_byte();
            if got != expect { return Err(format!("ascend_byte returned {got}, expected {expect}")) }
            if expect { p.pop(); }
        },
        Op::AscendUntil | Op::AscendUntilBranch => {
            let with_val = matches!(op, Op::AscendUntil);
            let mut q = p.clone();
            let mut n = 0;
            if !q.is_empty() {
                loop {
                    q.pop(); n += 1;
                    if q.is_empty() || model.children(&q).len() > 1 || (with_val && model.is_val(&q)) { break }
                }
            }
            let got = if with_val { z.ascend_until() } else { z.ascend_until_branch() };
            if got != n { return Err(format!("{op:?} returned {got}, expected {n}")) }
            *p = q;
        },
        Op::ToNextVal => {
            let expect = model.next_val(p);
            let got = z.to_next_val();
            if got != expect.is_some() { return Err(format!("to_next_val returned {got}, expected {} (next val {expect:?})", expect.is_some())) }
            *p = expect.unwrap_or_default();
        },
        Op::ToNextStep => {
            let expect = model.next_path(p);
            let got = z.to_next_step();
            if got != expect.is_some() { return Err(format!("to_next_step returned {got}, expected {} (next path {expect:?})", expect.is_some())) }
            *p = expect.unwrap_or_default();
        },
        Op::DescendFirstKPath(k) => {
            let expect = model.first_k_path(p, *k);
            let got = z.descend_first_k_path(*k);
            if got != expect.is_some() { return Err(format!("descend_first_k_path({k}) returned {got}, expected {} ({expect:?})", expect.is_some())) }
            if let Some(q) = expect { *p = q; }
        },
        Op::ToNextKPath(k) => {
            if p.len() < *k {
                let got = z.to_next_k_path(*k);
                if got { return Err(format!("to_next_k_path({k}) with short path returned true")) }
                if std::env::var("FUZZ_OLD_SHORT_K").is_err() { p.clear(); }
            } else {
                let expect = model.next_k_path(p, *k);
                let got = z.to_next_k_path(*k);
                if got != expect.is_some() { return Err(format!("to_next_k_path({k}) returned {got}, expected {} ({expect:?})", expect.is_some())) }
                match expect {
                    Some(q) => *p = q,
                    None => { let l = p.len() - *k; p.truncate(l); }
                }
            }
        },
        Op::MoveToPath(k) => { z.move_to_path(k); *p = k.clone(); },
        Op::Reset => { z.reset(); p.clear(); },
        Op::DescendUntilMaxBytes(n) => {
            let mut q = p.clone();
            let mut moved = false;
            if *n > 0 {
                moved = descend_until_model(model, &mut q);
                if q.len() > p.len() + n { q.truncate(p.len() + n); }
            }
            let got = z.descend_until_max_bytes(*n);
            if got != moved { return Err(format!("descend_until_max_bytes({n}) returned {got}, expected {moved}")) }
            *p = q;
        },
        Op::DescendToCheck(k) => {
            let mut q = p.clone(); q.extend(k);
            let expect = model.exists(&q);
            let got = z.descend_to_check(k);
            if got != expect { return Err(format!("descend_to_check returned {got}, expected {expect}")) }
            *p = q;
        },
        Op::DescendLastPath => {
            let mut q = p.clone();
            let mut any = false;
            loop {
                let c = model.children(&q);
                if c.is_empty() { break }
                q.push(*c.last().unwrap()); any = true;
                descend_until_model(model, &mut q);
            }
            let got = z.descend_last_path();
            if got != any { return Err(format!("descend_last_path returned {got}, expected {any}")) }
            *p = q;
        },
        Op::ToNextValObs => {
            let expect = model.next_val(p);
            let mut obs: Vec<u8> = p.clone();
            let got = z.to_next_val_observed(&mut obs);
            if got != expect.is_some() { return Err(format!("to_next_val_observed returned {got}, expected {}", expect.is_some())) }
            *p = expect.unwrap_or_default();
            if obs != z.path() { return Err(format!("to_next_val_observed OBSERVER MISMATCH observer = {obs:?}, zipper path = {:?}", z.path())) }
        },
        Op::ToNextStepObs => {
            let expect = model.next_path(p);
            let mut obs: Vec<u8> = p.clone();
            let got = z.to_next_step_observed(&mut obs);
            if got != expect.is_some() { return Err(format!("to_next_step_observed returned {got}, expected {}", expect.is_some())) }
            *p = expect.unwrap_or_default();
            if obs != z.path() { return Err(format!("to_next_step_observed OBSERVER MISMATCH observer = {obs:?}, zipper path = {:?}", z.path())) }
        },
        Op::DescendUntilObs => {
            let mut q = p.clone();
            let moved = descend_until_model(model, &mut q);
            let mut obs: Vec<u8> = p.clone();
            let got = z.descend_until_observed(&mut obs);
            if got != moved { return Err(format!("descend_until_observed returned {got}, expected {moved}")) }
            *p = q;
            if obs != z.path() { return Err(format!("descend_until_observed OBSERVER MISMATCH observer = {obs:?}, zipper path = {:?}", z.path())) }
        },
        Op::DescendFirstKPathObs(k) => {
            let expect = model.first_k_path(p, *k);
            let mut obs: Vec<u8> = p.clone();
            let got = z.descend_first_k_path_observed(*k, &mut obs);
            if got != expect.is_some() { return Err(format!("descend_first_k_path_observed({k}) returned {got}, expected {}", expect.is_some())) }
            if let Some(q) = expect { *p = q; }
            if obs != z.path() { return Err(format!("descend_first_k_path_observed OBSERVER MISMATCH observer = {obs:?}, zipper path = {:?}", z.path())) }
        },
        Op::ToNextKPathObs(k) => {
            let mut obs: Vec<u8> = p.clone();
            if p.len() < *k {
                let got = z.to_next_k_path_observed(*k, &mut obs);
                if got { return Err(format!("to_next_k_path_observed({k}) with short path returned true")) }
                if std::env::var("FUZZ_OLD_SHORT_K").is_err() { p.clear(); } // documented: resets to root
            } else {
                let expect = model.next_k_path(p, *k);
                let got = z.to_next_k_path_observed(*k, &mut obs);
                if got != expect.is_some() { return Err(format!("to_next_k_path_observed({k}) returned {got}, expected {}", expect.is_some())) }
                match expect { Some(q) => *p = q, None => { let l = p.len() - *k; p.truncate(l); } }
            }
            if obs != z.path() { return Err(format!("to_next_k_path_observed OBSERVER MISMATCH observer = {obs:?}, zipper path = {:?}", z.path())) }
        },
    }
    // Invariants after every op
    if z.path() != &p[..] { return Err(format!("path() = {:?}, model = {:?}", z.path(), p)) }
    if z.at_root() != p.is_empty() { return Err(format!("at_root() = {}, model = {}", z.at_root(), p.is_empty())) }
    if z.path_exists() != model.exists(p) { return Err(format!("path_exists() = {}, model = {}", z.path_exists(), model.exists(p))) }
    if z.is_val() != model.is_val(p) { return Err(format!("is_val() = {}, model = {}", z.is_val(), model.is_val(p))) }
    let cc = model.children(p).len();
    if z.child_count() != cc { return Err(format!("child_count() = {}, model = {}", z.child_count(), cc)) }
    Ok(())
}

fn gen_keys(rng: &mut Rng) -> (Vec<Vec<u8>>, usize) {
    let alphabet = [2usize, 3, 4, 6, 16, 256][rng.below(6)];
    let n = 1 + rng.below(30);
    let max_len = 1 + rng.below(24);
    let mut keys = BTreeSet::new();
    for _ in 0..n {
        let len = 1 + rng.below(max_len);
        let k: Vec<u8> = (0..len).map(|_| rng.below(alphabet) as u8).collect();
        keys.insert(k);
    }
    if rng.chance(20) { keys.insert(vec![]); }
    (keys.into_iter().collect(), alphabet)
}

struct Case { keys: Vec<Vec<u8>>, dangling: Vec<Vec<u8>>, root: Vec<u8>, ops: Vec<Op>, owned: bool, flavor: u8 }

fn build_map(keys: &[Vec<u8>], dangling: &[Vec<u8>]) -> PathMap<u64> {
    let mut map = PathMap::<u64>::new();
    for (i, k) in keys.iter().enumerate() {
        if k.is_empty() { let mut w = map.write_zipper(); w.set_val(i as u64); }
        else { map.insert(k, i as u64); }
    }
    for d in dangling { if !d.is_empty() { map.create_path(d); } }
    map
}

/// The model's universe: values are `keys`; existing paths are all prefixes of keys and of dangling paths.
fn model_for(keys: &[Vec<u8>], dangling: &[Vec<u8>], root: &[u8]) -> Model {
    let sub_keys: Vec<Vec<u8>> = keys.iter().filter(|k| sw(k, root)).map(|k| k[root.len()..].to_vec()).collect();
    let sub_dangling: Vec<Vec<u8>> = dangling.iter().filter(|k| sw(k, root)).map(|k| k[root.len()..].to_vec()).collect();
    let mut m = Model::new(&sub_keys);
    for d in &sub_dangling { for i in 0..=d.len() { m.paths.insert(d[..i].to_vec()); } }
    m
}

fn run_ops<Z: ZipperMoving + ZipperIteration + ZipperPath>(z: &mut Z, model: &Model, ops: &[Op], idx: &mut usize) -> Result<(), (usize, String)> {
    let mut p: Vec<u8> = vec![];
    for (i, op) in ops.iter().enumerate() { *idx = i; apply(z, model, &mut p, op).map_err(|e| (i, e))?; }
    Ok(())
}

fn panic_msg(panic: Box<dyn std::any::Any + Send>) -> String {
    panic.downcast_ref::<String>().cloned()
        .or_else(|| panic.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_else(|| "non-string panic".to_string())
}

/// Replays `ops` on a fresh zipper.  Returns Err((index_of_failing_op, error)).
fn replay(case: &Case) -> Result<(), (usize, String)> {
    let map = build_map(&case.keys, &case.dangling);
    let model = model_for(&case.keys, &case.dangling, &case.root);
    let mut idx = 0;
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        match case.flavor {
            1 => { let mut z = map.clone().into_read_zipper(&case.root); run_ops(&mut z, &model, &case.ops, &mut idx) },
            2 => { let mut z = map.read_zipper_at_borrowed_path(&case.root); run_ops(&mut z, &model, &case.ops, &mut idx) },
            3 => { let base = map.read_zipper_at_path(&case.root); let mut z = base.fork_read_zipper(); run_ops(&mut z, &model, &case.ops, &mut idx) },
            _ => { let mut z = map.read_zipper_at_path(&case.root); run_ops(&mut z, &model, &case.ops, &mut idx) },
        }
    }));
    match res {
        Ok(r) => r,
        Err(panic) => Err((idx, format!("PANIC: {}", panic_msg(panic)))),
    }
}

fn category(case: &Case, idx: usize, err: &str) -> String {
    let op = format!("{:?}", case.ops[idx]);
    let op = op.split('(').next().unwrap().to_string();
    let e = err.split(" returned").next().unwrap().split(" = ").next().unwrap();
    format!("{op}: {e}")
}

fn gen_case(seed: u64, ops_per_seed: usize) -> Case {
    let mut rng = Rng::new(seed);
    let (keys, alphabet) = gen_keys(&mut rng);
    let full_model = Model::new(&keys);
    let root: Vec<u8> = if rng.chance(30) {
        let v: Vec<&Vec<u8>> = full_model.paths.iter().collect();
        v[rng.below(v.len())].clone()
    } else { vec![] };
    let flavor = rng.below(4) as u8;
    let owned = flavor == 1;
    // Dangling paths: extensions of existing prefixes (or fresh), created with `create_path`
    let mut dangling: Vec<Vec<u8>> = vec![];
    if rng.chance(35) {
        let n = 1 + rng.below(3);
        let all: Vec<&Vec<u8>> = full_model.paths.iter().collect();
        for _ in 0..n {
            let mut d = all[rng.below(all.len())].clone();
            let ext = 1 + rng.below(3);
            for _ in 0..ext { d.push(rng.below(alphabet) as u8); }
            dangling.push(d);
        }
    }
    let model = model_for(&keys, &dangling, &root);
    // Ops are generated against the model path only, so generation is independent of the zipper.
    let mut p: Vec<u8> = vec![];
    let mut ops = Vec::new();
    let map = build_map(&keys, &dangling);
    let mut z = map.read_zipper_at_path(&root);
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        for _ in 0..ops_per_seed {
            let op = gen_op(&mut rng, alphabet, &model, &p);
            ops.push(op.clone());
            // Track the model path (and zipper) so that op generation stays meaningful; ignore errors.
            if apply(&mut z, &model, &mut p, &op).is_err() { break }
        }
    }));
    Case { keys, dangling, root, ops, owned, flavor }
}

fn run_seed(seed: u64, ops_per_seed: usize) -> Result<(), String> {
    let case = gen_case(seed, ops_per_seed);
    match replay(&case) {
        Ok(()) => Ok(()),
        Err((idx, err)) => {
            let ops: Vec<String> = case.ops[..=idx].iter().map(|o| format!("{o:?}")).collect();
            Err(format!("seed {seed}: {err}\n  root = {:?} flavor = {} dangling = {:?}\n  keys = {:?}\n  ops = [{}]", case.root, case.flavor, case.dangling, case.keys, ops.join(", ")))
        }
    }
}

/// Greedy one-at-a-time minimization of a failing case, preserving the failure category.
fn minimize(case: Case) -> (Case, String) {
    let (idx, err) = replay(&case).err().expect("case does not fail");
    let cat = category(&case, idx, &err);
    let mut cur = Case { keys: case.keys.clone(), dangling: case.dangling.clone(), root: case.root.clone(), ops: case.ops[..=idx].to_vec(), owned: case.owned, flavor: case.flavor };
    // Minimize ops
    loop {
        let mut changed = false;
        let mut i = 0;
        while i < cur.ops.len() {
            let mut cand = Case { keys: cur.keys.clone(), dangling: cur.dangling.clone(), root: cur.root.clone(), ops: cur.ops.clone(), owned: cur.owned, flavor: cur.flavor };
            cand.ops.remove(i);
            if let Err((j, e)) = replay(&cand) {
                if j == cand.ops.len() - 1 && category(&cand, j, &e) == cat { cur = cand; changed = true; continue }
            }
            i += 1;
        }
        // Minimize keys
        let mut k = 0;
        while k < cur.keys.len() {
            let mut cand = Case { keys: cur.keys.clone(), dangling: cur.dangling.clone(), root: cur.root.clone(), ops: cur.ops.clone(), owned: cur.owned, flavor: cur.flavor };
            cand.keys.remove(k);
            if !cand.keys.iter().chain(cand.dangling.iter()).any(|key| sw(key, &cand.root)) { k += 1; continue }
            if let Err((j, e)) = replay(&cand) {
                if j == cand.ops.len() - 1 && category(&cand, j, &e) == cat { cur = cand; changed = true; continue }
            }
            k += 1;
        }
        if !changed { break }
    }
    let (idx, err) = replay(&cur).err().unwrap();
    (cur, format!("{err} (at op {idx})"))
}

#[test]
fn minimize_seed() {
    let Some(seed) = std::env::var("FUZZ_MINIMIZE").ok().and_then(|s| s.parse::<u64>().ok()) else { return };
    let ops: usize = std::env::var("FUZZ_OPS").ok().and_then(|s| s.parse().ok()).unwrap_or(150);
    let case = gen_case(seed, ops);
    std::panic::set_hook(Box::new(|_| {}));
    let (min, err) = minimize(case);
    let _ = std::panic::take_hook();
    let ops: Vec<String> = min.ops.iter().map(|o| format!("{o:?}")).collect();
    println!("MINIMIZED seed {seed}: {err}\n  root = {:?} flavor = {} dangling = {:?}\n  keys = {:?}\n  ops = [{}]", min.root, min.flavor, min.dangling, min.keys, ops.join(", "));
}

#[test]
fn zipper_movement_oracle_fuzz() {
    let seeds: u64 = std::env::var("FUZZ_SEEDS").ok().and_then(|s| s.parse().ok()).unwrap_or(200);
    let ops: usize = std::env::var("FUZZ_OPS").ok().and_then(|s| s.parse().ok()).unwrap_or(150);
    let start: u64 = std::env::var("FUZZ_START").ok().and_then(|s| s.parse().ok()).unwrap_or(0);
    let report = std::env::var("FUZZ_REPORT").is_ok();
    let mut failures = Vec::new();
    let mut n_fail = 0;
    for seed in start..start + seeds {
        match run_seed(seed, ops) {
            Ok(()) => { if report { println!("RESULT seed={seed} ok"); } },
            Err(e) => {
                n_fail += 1;
                if report {
                    // e begins with "seed N: <err>\n  root ...\n  keys ...\n  ops = [...]"
                    let first = e.lines().next().unwrap_or("");
                    let err = first.splitn(2, ": ").nth(1).unwrap_or(first);
                    let ops_line = e.lines().last().unwrap_or("");
                    let idx = ops_line.matches(", ").count() + 1;
                    let last_op = ops_line.rsplit(", ").next().unwrap_or("").trim_end_matches(']').trim_start_matches("ops = [");
                    let last_op = last_op.split('(').next().unwrap_or(last_op);
                    println!("RESULT seed={seed} fail idx={idx} op={last_op} err={}", err.replace('\n', " "));
                }
                if failures.len() < 12 { failures.push(e); }
            }
        }
    }
    if report { println!("SUMMARY fails={n_fail} of {seeds}"); return }
    if !failures.is_empty() {
        panic!("{} failing seeds (showing up to 12):\n\n{}", n_fail, failures.join("\n\n"));
    }
}


fn k(v: &[&[u8]]) -> Vec<Vec<u8>> { v.iter().map(|x| x.to_vec()).collect() }

/// Minimized cases found by the fuzzer.  (name, zipper root, keys, ops)
fn minimized_cases() -> Vec<(&'static str, Vec<u8>, Vec<Vec<u8>>, Vec<Op>)> {
    use Op::*;
    vec![
        // --- R1: failed / exhausted k-path walk leaves a token the following op trusts
        ("R1a descend_first_k_path fails, then descend_first_byte", vec![], k(&[b"ab"]), vec![DescendFirstKPath(3), DescendFirstByte]),
        ("R1b to_next_k_path exhausted, then to_next_step", vec![], k(&[&[0,0,0,1,0,2,2,2,1,2,1,0,3]]), vec![ToNextVal, ToNextKPath(5), ToNextStep]),
        ("R1c descend_until, to_next_k_path exhausted, to_next_step", vec![124], k(&[&[124,157,12,28,95,232,130]]), vec![DescendUntil, ToNextKPath(5), ToNextStep]),
        ("R1d to_next_k_path exhausted in subtree, then to_next_val skips subtree", vec![], k(&[&[1,2,1,0,0,0,2,1,1,1,2,3,1,2],&[2,2,1,2,3,2,3],&[3,3,3,2,3,0,0,3]]), vec![DescendIndexedByte(1), DescendToExistingByte(2), ToNextKPath(1), ToNextVal]),
        ("R1e exhausted k-path at root then to_next_val (also fails on master)", vec![5,7], k(&[&[5,7,3,4]]), vec![ToNextVal, ToNextKPath(2), ToNextVal]),
        ("R1f exhausted k-path then to_next_val wrong path (also master?)", vec![], k(&[&[0,1,0,0,1,2,1,1,2,1,2,1,1,0,0,1],&[2,1,1,2,2,0,0,2,1,1,0,0,0]]), vec![ToNextVal, ToNextKPath(5), ToNextVal]),
        ("R1g failed to_next_k_path then to_next_sibling_byte", vec![], k(&[&[1],&[2,0],&[2,2],&[3]]), vec![DescendTo(vec![2,2]), ToNextKPath(1), ToNextSibling]),
        // --- R2: reset() leaves the token when there are no ancestors
        ("R2 to_next_step, reset, descend_first_byte", vec![], k(&[&[24]]), vec![ToNextStep, Reset, DescendFirstByte]),
        ("R2b to_next_step to end, reset, to_next_step", vec![], k(&[&[24]]), vec![ToNextStep, Reset, ToNextStep]),
        // --- R3: k_path_internal pops an ancestor whose stored token is INVALID
        ("R3a descend_to then to_next_k_path across node boundary", vec![], k(&[&[0,0,1,1],&[0,1,0,1,0,0],&[0,1,1,0,0,0,1,0]]), vec![DescendTo(vec![0,1,1]), ToNextKPath(2)]),
        ("R3b move_to_path then to_next_k_path", vec![], k(&[&[3,2,2],&[3,2,3,1,2,3,0],&[3,2,3,3]]), vec![MoveToPath(vec![3,2,3,3]), ToNextKPath(4)]),
        ("R3c descend_to, descend_until, to_next_k_path", vec![], k(&[&[0,0,0,0,1,0,1],&[0,1,1,1]]), vec![DescendTo(vec![0,1]), DescendUntil, ToNextKPath(4)]),
        ("R3d to_next_step, descend_first_byte, descend_to, to_next_k_path", vec![], k(&[&[0,0,0,0,2,1,3,1,1,2,0,3,2,3],&[0,0,0,1,1,2],&[0,2,2,3,0,3,3],&[0,3,3,2,1]]), vec![ToNextStep, DescendFirstByte, DescendTo(vec![0,1]), ToNextKPath(2)]),
        // --- R4: nonexistent focus + descend_first_byte stores a lower-bound token; later ascent misuses it
        ("R4a LineList: nonexistent path, descend_first_byte, ascend_byte, to_next_step -> panic", vec![14,5], k(&[&[0],&[7],&[14,5]]), vec![DescendToByte(11), DescendToByte(13), DescendFirstByte, AscendByte, ToNextStep]),
        ("R4b LineList: nonexistent path, descend_first_byte, ascend_until_branch -> panic", vec![1,12,4,5,4], k(&[&[1,12,4,5,4],&[13,9,5,15,5,0,11,14,13,3,12,0,4],&[15,3,14,15,0,8,7]]), vec![DescendTo(vec![12,12]), DescendTo(vec![173,37,23]), DescendFirstByte, AscendUntilBranch]),
        ("R4c LineList: nonexistent path before key0, descend_first_byte, ascend_byte -> panic", vec![], k(&[b"b", b"c"]), vec![DescendTo(vec![b'a']), DescendFirstByte, AscendByte]),
        ("R4d LineList: nonexistent path after key1, descend_first_byte, ascend_byte, descend_first_byte", vec![], k(&[b"ab", b"wxyz"]), vec![DescendTo(vec![b'z']), DescendFirstByte, AscendByte, DescendFirstByte]),
        ("R4e nonexistent, descend_first_byte, ascend(1), to_next_val escapes", vec![7,167,36,166,110], k(&[&[7,167,36,166,110]]), vec![DescendTo(vec![45,47,220]), DescendFirstByte, Ascend(1), ToNextVal]),
        ("R4f to_next_val, nonexistent byte, descend_first_byte, ascend_until, to_next_val goes backwards", vec![], k(&[&[3,1,1,1,1,1,1,1,2,1,3,2,1,3,1],&[3,2,1,3,1,3,2,0,1,0,2,3,3,0,3,3]]), vec![ToNextVal, DescendToByte(1), DescendFirstByte, AscendUntil, ToNextVal]),
        ("R4g Dense: nonexistent below leaf, descend_first_byte, ascend_byte, to_next_sibling_byte", vec![], k(&[&[10],&[20],&[30]]), vec![DescendTo(vec![10,99]), DescendFirstByte, AscendByte, ToNextSibling]),
        ("R4h Dense: nonexistent multi-byte, to_next_sibling_byte, ascend(2) -> debug assert", vec![], k(&[&[24],&[49,69],&[54],&[73,209,145,207],&[124]]), vec![MoveToPath(vec![133,52,64,90]), ToNextSibling, Ascend(2)]),
        // --- N: cases minimized on head 679a9b7
        ("N1 k-path base-mismatch exit: to_next_val then to_next_k_path then to_next_val", vec![], k(&[&[0,0,0,0,0,0,1],&[2]]), vec![ToNextVal, ToNextKPath(2), ToNextVal]),
        ("N1b k-path base-mismatch exit: then descend_first_byte", vec![], k(&[&[0,0,0,0,0,0,1],&[2]]), vec![ToNextVal, ToNextKPath(2), DescendFirstByte]),
        ("N1c rooted zipper: failed descend_first_k_path then descend_first_byte", vec![2,1], k(&[&[2,1,3,1,3],&[2,5,5]]), vec![DescendFirstKPath(4), DescendFirstByte]),
        ("N2 to_next_val, reset, to_next_val (rooted, single node)", vec![1,2,1,1,0,1,2,0,0,3,0,2,1,3,1,2,1], k(&[&[1,2,1,1,0,1,2,0,0,3,0,2,1,3,1,2,1,3]]), vec![ToNextVal, Reset, ToNextVal]),
        ("N2b to_next_val, reset, to_next_val (unrooted)", vec![], k(&[&[5,6,7]]), vec![ToNextVal, Reset, ToNextVal]),
        ("N2c to_next_val, reset, descend_first_byte", vec![2,1,1,3,1,3,0,0,0,0,1,2,3,1,2], k(&[&[2,1,1,3,1,3,0,0,0,0,1,2,3,1,2,0,2,3,3,0]]), vec![ToNextVal, Reset, DescendFirstByte]),
        ("N2d nonexistent, to_next_sibling, reset, to_next_val", vec![], k(&[&[154,215,144,75,136],&[255,150,104]]), vec![DescendTo(vec![164,8,42,235]), ToNextSibling, Reset, ToNextVal]),
        ("N2e steps then reset then to_next_step", vec![], k(&[&[3,1,2,0],&[3,1,4,2,5],&[4,1,4,2,3,5,2,2]]), vec![ToNextVal, ToNextStep, DescendUntil, ToNextStep, Reset, ToNextStep]),
        ("N3 dense: nonexistent sibling attempt, move_to_path(root), to_next_val", vec![], k(&[&[5,187,244,139,52],&[16,166,208,106,161,75],&[19],&[249,172,195,103,211,34]]), vec![ToNextVal, ToNextVal, ToNextStep, DescendToByte(255), ToNextSibling, MoveToPath(vec![]), ToNextVal]),
        ("N3b dense: descend_to nonexistent, to_next_sibling, move_to_path(root), to_next_val", vec![], k(&[&[5,187,244,139,52],&[16,166,208,106,161,75],&[19],&[249,172,195,103,211,34]]), vec![DescendTo(vec![19,255]), ToNextSibling, MoveToPath(vec![]), ToNextVal]),
        ("N3c dense: descend_to nonexistent, to_next_sibling, ascend(2), to_next_val", vec![], k(&[&[5,187,244,139,52],&[16,166,208,106,161,75],&[19],&[249,172,195,103,211,34]]), vec![DescendTo(vec![19,255]), ToNextSibling, Ascend(2), ToNextVal]),
        ("N3d dense: descend_to nonexistent, to_next_sibling, reset, to_next_val", vec![], k(&[&[5,187,244,139,52],&[16,166,208,106,161,75],&[19],&[249,172,195,103,211,34]]), vec![DescendTo(vec![19,255]), ToNextSibling, Reset, ToNextVal]),
        ("N4 k-path duplicate after ascend_until (seed 1651)", vec![], k(&[&[2,4,0],&[4,3],&[4,3,0,3,2,4]]), vec![ToNextVal, ToNextVal, DescendToByte(0), AscendUntil, ToNextKPath(2)]),
        ("N4b k-path wrong path (seed 1020)", vec![], k(&[&[0,1,1,1,1],&[1],&[1,0,0],&[1,0,0,1],&[1,0,0,1,1],&[1,0,1,1,1,0]]), vec![ToNextVal, ToNextVal, ToNextVal, ToNextVal, DescendToByte(1), AscendByte, ToNextKPath(2)]),
        ("N5 to_next_step after exhausted k-path, two keys (seed 19)", vec![], k(&[&[0,0,0,1,0,2,2,2,1,2,1,0,3],&[0,0,3,1,1]]), vec![ToNextVal, ToNextKPath(5), ToNextStep]),
        // --- P: pre-existing on master (for reference)
        ("P1 k-path duplicate when key0 is a prefix of key1", vec![], k(&[b"a", b"abcd"]), vec![DescendFirstKPath(1), ToNextKPath(1)]),
        ("P1b k-path duplicate via to_next_val then to_next_k_path", vec![], k(&[&[1],&[1,2]]), vec![ToNextVal, ToNextKPath(1)]),
        ("P1c k-path duplicate (seed 705)", vec![], k(&[&[3,11,14,15,14,7],&[5,6,2,5,7,10,9,9,0],&[6,8],&[6,8,11,13,8,6],&[15,14,0,4,11,3,13,15]]), vec![DescendFirstByte, ToNextSibling, DescendUntil, ToNextStep, DescendFirstByte, ToNextKPath(2)]),
        ("P1d k-path duplicate (seed 824)", vec![], k(&[&[0,1,1,0,0,0,0,0,1],&[0,1,1,1,0,1,1],&[0,1,1,1,0,1,1,1,1,1,0,0,0,1]]), vec![ToNextVal, ToNextVal, ToNextKPath(2)]),
        ("P2 to_next_sibling_byte escapes zipper root", vec![4], k(&[&[4],&[5]]), vec![ToNextSibling]),
        ("P2b to_prev_sibling_byte escapes zipper root", vec![15], k(&[&[14],&[15]]), vec![ToPrevSibling]),
        ("P3 to_prev_sibling_byte debug overflow in dense node", vec![], k(&[&[0,0,2],&[0,1],&[1],&[1,2],&[2],&[2,0,1],&[2,2,1],&[2,2,2]]), vec![DescendFirstKPath(1), ToPrevSibling]),
        // --- M: master-only (fixed by PR)
        ("M1 descend_first_byte, to_next_step, to_next_val", vec![], k(&[&[2,0,0,1],&[2,2,1,1]]), vec![DescendFirstByte, ToNextStep, ToNextVal]),
        ("M2 to_next_val, ascend(2), to_next_val", vec![], k(&[&[11,8,6,10,15,6,4,8,11,6,5,6,1,15,11,0,10],&[11,8,7,6,2,0,13,2]]), vec![ToNextVal, Ascend(2), ToNextVal]),
        ("M3 to_next_step, to_prev_sibling, to_next_sibling", vec![], k(&[&[1,0,2,0],&[3,1,3,3]]), vec![DescendToExistingByte(1), DescendTo(vec![0,2,0]), ToNextStep, ToPrevSibling, ToNextSibling]),
        ("M4 to_next_step, ascend_byte, descend_last_byte, to_next_k_path", vec![], k(&[&[1,3,13,0,14,15,13,2,7,8,5,13],&[13,7],&[15,0,6,6,0,11,12]]), vec![ToNextStep, AscendByte, DescendLastByte, ToNextKPath(1)]),
        ("M5 to_next_val false, descend_first_byte, to_next_val", vec![5,0,4,1], k(&[&[5,0,4,1,0,4,4]]), vec![DescendToByte(241), ToNextVal, DescendFirstByte, ToNextVal]),
    ]
}

#[test]
fn replay_minimized_cases() {
    std::panic::set_hook(Box::new(|_| {}));
    let mut fails = 0;
    let filter = std::env::var("FUZZ_CASE_FILTER").unwrap_or_default();
    for (name, root, keys, ops) in minimized_cases() {
        if !name.contains(&filter) { continue }
        let case = Case { keys, dangling: vec![], root, ops, owned: false, flavor: 0 };
        match replay(&case) {
            Ok(()) => println!("CASE PASS  {name}"),
            Err((i, e)) => { fails += 1; println!("CASE FAIL  {name}  -- op {i} {:?}: {}", case.ops[i], e.replace('\n', " ")); }
        }
    }
    let _ = std::panic::take_hook();
    println!("CASES: {fails} failing of {}", minimized_cases().len());
}

// ---- Targeted scenarios ----

fn two_key_map() -> PathMap<u64> {
    let mut map = PathMap::<u64>::new();
    map.insert(b"ab", 1);
    map.insert(b"wxyz", 2);
    map
}

#[test]
fn descend_first_byte_after_exhausted_k_path_at_root() {
    let map = two_key_map();
    let mut z = map.read_zipper();
    assert!(z.descend_first_k_path(1));
    assert_eq!(z.path(), b"a");
    assert!(z.to_next_k_path(1));
    assert_eq!(z.path(), b"w");
    assert!(!z.to_next_k_path(1));
    assert_eq!(z.path(), b"");
    assert_eq!(z.descend_first_byte(), Some(b'a'), "descend_first_byte after exhausted k-path walk");
}

#[test]
fn to_next_val_after_exhausted_k_path_at_root() {
    let map = two_key_map();
    let mut z = map.read_zipper();
    assert!(z.descend_first_k_path(1));
    assert!(z.to_next_k_path(1));
    assert!(!z.to_next_k_path(1));
    assert_eq!(z.path(), b"");
    assert!(z.to_next_val(), "to_next_val after exhausted k-path walk");
    assert_eq!(z.path(), b"ab");
}

#[test]
fn ascend_after_exhausted_k_path_in_node_interior() {
    let map = two_key_map();
    let mut z = map.read_zipper();
    z.descend_to(b"w");
    assert!(z.descend_first_k_path(1));
    assert_eq!(z.path(), b"wx");
    assert!(!z.to_next_k_path(1));
    assert_eq!(z.path(), b"w");
    assert!(z.ascend_byte());
    assert_eq!(z.path(), b"");
    assert_eq!(z.descend_first_byte(), Some(b'a'));
}

#[test]
fn to_next_val_after_failed_k_path_from_interior_focus() {
    let map = two_key_map();
    let mut z = map.read_zipper();
    z.descend_to(b"a");
    assert!(z.descend_first_k_path(1));
    assert_eq!(z.path(), b"ab");
    assert!(!z.to_next_k_path(1));
    assert_eq!(z.path(), b"a");
    assert!(z.to_next_val());
    assert_eq!(z.path(), b"ab", "to_next_val from 'a' must find 'ab' first");
}

#[test]
fn ascend_after_descend_first_byte_on_nonexistent_path_before_key0() {
    let mut map = PathMap::<u64>::new();
    map.insert(b"b", 1);
    map.insert(b"c", 2);
    let mut z = map.read_zipper();
    z.descend_to(b"a");
    assert!(!z.path_exists());
    assert_eq!(z.descend_first_byte(), None);
    assert!(z.ascend_byte());
    assert_eq!(z.path(), b"");
    assert_eq!(z.descend_first_byte(), Some(b'b'));
}

#[test]
fn ascend_after_descend_first_byte_on_nonexistent_path_after_key1() {
    let map = two_key_map();
    let mut z = map.read_zipper();
    z.descend_to(b"z");
    assert_eq!(z.descend_first_byte(), None);
    assert!(z.ascend_byte());
    assert_eq!(z.path(), b"");
    assert_eq!(z.descend_first_byte(), Some(b'a'));
}

#[test]
fn ascend_after_descend_first_byte_on_nonexistent_extension() {
    let mut map = PathMap::<u64>::new();
    map.insert(b"ab", 1);
    let mut z = map.read_zipper();
    z.descend_to(b"abc");
    assert_eq!(z.descend_first_byte(), None);
    assert!(z.ascend_byte());
    assert_eq!(z.path(), b"ab");
    assert_eq!(z.to_next_sibling_byte(), None);
    assert!(z.ascend_byte());
    assert_eq!(z.path(), b"a");
    assert_eq!(z.descend_first_byte(), Some(b'b'));
}

#[test]
fn k_path_no_duplicates_when_key0_is_prefix_of_key1() {
    let mut map = PathMap::<u64>::new();
    map.insert(b"a", 1);
    map.insert(b"abcd", 2);
    let mut z = map.read_zipper();
    let mut seen = vec![];
    assert!(z.descend_first_k_path(1));
    seen.push(z.path().to_vec());
    while z.to_next_k_path(1) { seen.push(z.path().to_vec()); }
    assert_eq!(seen, vec![b"a".to_vec()]);
}
