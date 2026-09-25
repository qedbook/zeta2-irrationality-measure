# μ(ζ(2)) ≤ 5.0495243, machine-checked in Lean 4

This repository contains a complete, machine-checked proof that the irrationality measure of
ζ(2) = π²/6 is at most **5.0495243**. The previous published bound was 5.095412 (Zudilin, 2014),
which improved 5.441243 (Rhin–Viola, 1996).

The theorem, as stated in Lean:

```lean
theorem Zeta2Target.zeta2_not_liouvilleWith : ¬ LiouvilleWith (5.0495243 : ℝ) zeta2
theorem Zeta2Target.zeta2_irrationality_measure_le :
    ∀ p : ℝ, 5.0495243 ≤ p → ¬ LiouvilleWith p zeta2
theorem Zeta2Unconditional.zeta2_rational_approximation :
    ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ m : ℤ, zeta2 ≠ m / n → C / (n : ℝ) ^ (5.0495243 : ℝ) ≤ |zeta2 - m / n|
```

where `zeta2 : ℝ := Real.pi ^ 2 / 6`, pinned in the same development to Mathlib's `riemannZeta 2`
and to `∑' n, 1 / (n + 1) ^ 2`, and `LiouvilleWith` is Mathlib's. The proof has **no `sorry`** and
**no axiom beyond Lean's three** (`propext`, `Classical.choice`, `Quot.sound`) anywhere in its
import closure.

## What is proved, and what is not

- **Proved:** the three statements above, unconditionally.
- **The constant.** The certified value of the construction is 5.04952429053…, and the theorem
  states the rounded-up literal 5.0495243. The sharper-looking figure 5.04952429 that a search
  score prints is *not* proved and the development contains a theorem pinning that it is
  strictly below the certified value.
- **The prime number theorem** enters through PrimeNumberTheoremAnd's `MediumPNT`, whose full
  import cone is vendored under `src/PrimeNumberTheoremAnd/` and `src/Architect/` at the commit
  where it was attested, with two one-line tactic repairs for the newer toolchain
  (`THIRD_PARTY/PROVENANCE.md` records both diffs and the errors they fix). It is kernel-checked
  here like everything else; nothing is imported as an axiom.

## How to check it

Requirements: [elan](https://github.com/leanprover/elan), the pinned toolchain
(`leanprover/lean4:v4.34.0-rc2`, installed automatically by elan from `lean-toolchain`), roughly
13 GB of disk (Mathlib's prebuilt cache is about 8 GB; this build adds 4.8 GB), and about
4 GB of RAM per parallel job (the 559 generated modules each peak at 3.5–4 GB; the two
assembly modules that import them peak near 18 GB). Lake runs one job per hardware thread
unless `LEAN_NUM_THREADS` bounds it, so on a 16 GB machine set `LEAN_NUM_THREADS=2`.
The build that produced `receipts/this-machine.txt` took 12.6 CPU-hours: 2 h 32 min of wall
clock with 7 concurrent jobs on a 12-thread / 62 GB server that was carrying other load
(`receipts/build-stats.txt`); an idle machine of that size should finish in under two hours.

```sh
git clone https://github.com/qedbook/zeta2-irrationality-measure
cd zeta2-irrationality-measure
scripts/verify.sh
```

`verify.sh` fetches Mathlib's prebuilt cache for the pinned commit, builds every module below
`Zeta2Target`, elaborates `src/Receipts.lean`, and refuses unless each headline theorem's
`#print axioms` reads exactly `[propext, Classical.choice, Quot.sound]` and no `sorryAx` or
`error` appears. Its output on the machine that made this release is `receipts/this-machine.txt`.

Two things to read by eye, because a kernel cannot: that `Zeta2Defs.zeta2` and `LiouvilleWith`
mean what the README says (both are `#print`ed by `Receipts.lean`), and that the literal is the
one claimed.

## Layout

| path | what |
|---|---|
| `src/Zeta2*.lean`, `src/*.lean` (flat names) | the chain: definitions, the arithmetic layer, the analytic layer, the assembly (166 modules, 91,672 lines) |
| `src/StarForallCandt{1,2}{Base,Assemble,K*}.lean` | 559 **generated** modules: the creative-telescoping certificate as exact integer data, one kernel-checked evaluation per shard |
| `src/PrimeNumberTheoremAnd/`, `src/Architect*` | vendored third-party code (Apache-2.0), see `THIRD_PARTY/` |
| `generators/star/` | the generator that wrote the STAR modules, its inputs, and the sha256 manifests; `verify_manifests.sh` re-checks every generated file against them |
| `receipts/` | the receipts of record from the source repository: axiom prints with `#check` types, the whole-closure sorry census, falsifier runs |
| `scripts/` | `verify.sh` and the receipt checker |

## How the proof goes

The construction is Zudilin's: a Mellin–Barnes integral of a ratio of Gamma functions with
parameters (13, 11, 9, 15; 26), which written one way is a small number and written the other
way is an integer combination q_n·ζ(2) − p_n. Three growth rates — the decay of the form, the
growth of q_n, and the size of a common factor that divides both — feed a standard criterion that
turns them into the exponent 1 + (42.034 + 15.019)/(29.108 − 15.019).

The member (13, 11, 9, 15; 26) was found by a computational search in **qedbook**, a computer
algebra system developed by the author, over the parameter box of Zudilin's construction, made
tractable per member by Marcovecchio's pairing theorem. qedbook also produced the exact
certificates and the coefficient data the formal proof consumes. Nothing computed there is
trusted: every emitted value enters the proof as data that Lean's kernel re-verifies.

The formal development fills several gaps Mathlib does not cover: an explicit complex Binet bound
for log Γ, a partial-fraction theorem, a linear-forms criterion for `¬ LiouvilleWith`, a
Poincaré-type growth bound for three-term recurrences, and the p-adic analysis of the profile
function that gives the common factor.

## Provenance and authorship

The Lean text was written by Claude (Anthropic) sessions directed by Jonathan Kleid, who also
designed the search program and the verification discipline (every gate proven able to go red
before its green was accepted). The mathematics rests on Zudilin, *Two hypergeometric tales and a new irrationality
measure of ζ(2)*, Ann. Math. Québec 38 (2014), and on Marcovecchio's pairing theorem; PNT+ is by
Alex Kontorovich, Terence Tao and contributors.

## Licence

Apache License 2.0 for this repository's own files (`LICENSE`, `NOTICE`). The vendored code keeps
its upstream licences in `THIRD_PARTY/`.
