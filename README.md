# μ(ζ(2)) ≤ 5.0495243, machine-checked in Lean 4

This repository contains a complete, machine-checked proof that the irrationality measure of
ζ(2) = π²/6 is at most **5.0495243**. The best published bound is 5.095412 (Zudilin, 2014), which
improved 5.441243 (Rhin–Viola, 1996). A smaller bound, 5.0193784 (Niedbala Giraudin, 2026), is given in the
preprint arXiv:2610.02912 by David Niedbala Giraudin, which uses Zudilin's two constructions at a new
choice of parameters, with numerical constants certified in ball arithmetic.

The main theorems, as stated in Lean:

```lean
theorem Zeta2Target.zeta2_not_liouvilleWith : ¬ LiouvilleWith (5.0495243 : ℝ) zeta2
theorem Zeta2Target.zeta2_irrationality_measure_le :
    ∀ p : ℝ, 5.0495243 ≤ p → ¬ LiouvilleWith p zeta2
theorem Zeta2Unconditional.zeta2_rational_approximation :
    ∀ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ m : ℤ, zeta2 ≠ m / n → C / (n : ℝ) ^ (5.0495243 : ℝ) ≤ |zeta2 - m / n|
```

Here `LiouvilleWith` is Mathlib's, and `zeta2` is defined as π²/6; the development proves it equal to
Mathlib's `riemannZeta` at two and to the series:

```lean
def Zeta2Defs.zeta2 : ℝ := Real.pi ^ 2 / 6
theorem Zeta2Final.zeta2_eq_riemannZeta_two : ((zeta2 : ℝ) : ℂ) = riemannZeta 2
theorem Zeta2Final.zeta2_eq_tsum_from_one : zeta2 = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2
```

The headline theorems depend on no axiom beyond Lean's three (`propext`, `Classical.choice`,
`Quot.sound`). No module in this repository, the vendored ones included, declares an axiom, and no
constant declared by the modules below `Zeta2Target` uses `sorryAx`, Mathlib, the packages it depends on
and Lean's own libraries aside (`receipts/out_sorry_census.txt`).

## What is proved, and what is not

- **Proved:** the three statements above, unconditionally.
- **The constant.** The construction's exponent is 5.04952429053…, computed outside Lean from the
  construction's rate constants. The theorem `Zeta2TWire.certified_value_is_strictly_between_the_two_literals`
  checks, by arithmetic on those archived constants, that the value lies strictly between the literals
  5.04952429 and 5.0495243. What the proof establishes about the exponent is the upper bound 5.0495243:
  its three rates (*How the proof goes*) are one-sided bounds, rounded outward, and the criterion applied
  to them gives a value below 5.0495243 that is not the exponent itself.
- **The prime number theorem**, in the form ψ(x) = x + O(x exp(−c (log x)^δ)) with δ one tenth, comes
  from the PrimeNumberTheoremAnd project (PNT+), as its theorem `MediumPNT`. That theorem and everything it
  imports beyond Mathlib, Batteries and Lean are copied in: PNT+'s own modules into
  `src/PrimeNumberTheoremAnd/`, from a fixed PNT+ commit and with two one-line tactic repairs for the newer
  toolchain (`THIRD_PARTY/PROVENANCE.md` records both diffs and the errors they fix), and the LeanArchitect
  package PNT+ imports into `src/Architect/` and `src/Architect.lean`, from the commit PNT+ pins
  (`THIRD_PARTY/PROVENANCE.md` names both). It is kernel-checked
  here like everything else; nothing is imported as an axiom.

## How to check it

Requirements: [elan](https://github.com/leanprover/elan), the pinned toolchain
(`leanprover/lean4:v4.34.0-rc2`, installed automatically by elan from `lean-toolchain`), git and curl
(Lake fetches packages with git, Mathlib's cache tool downloads with curl), python3 (for
`scripts/check_receipts.py`), disk for 12.7 GiB after the build (Mathlib's prebuilt cache 7.9 GiB of disk,
this build 4.7 GiB of disk), and
memory for the largest single process, which peaks at 19.9 GiB (the largest process the sampler saw was
`Zeta2CarryFull`, at 19.8 GiB of memory).
Memory decides how many modules can build at once: up to 6 concurrent lean processes ran, and their
combined memory peaked at 47.6 GiB; `LEAN_NUM_THREADS` bounds how many build at once
(`receipts/build-stats.txt` has the ten largest processes with the module each was compiling).
The build that produced `receipts/this-machine.txt` ran with `LEAN_NUM_THREADS=6` on 12 logical CPUs
and 62.7 GiB of memory and took 2:14:29 of wall clock and 11.08 CPU-hours.

```sh
git clone https://github.com/qedbook/zeta2-irrationality-measure
cd zeta2-irrationality-measure
scripts/verify.sh
```

`verify.sh` fetches Mathlib's prebuilt cache for the pinned commit, builds every module below
`Zeta2Target`, elaborates `src/Receipts.lean`, and fails unless each headline theorem's
`#print axioms` reads exactly `[propext, Classical.choice, Quot.sound]` and no `sorryAx` or
`error` appears. Its output on the machine that made this release is `receipts/this-machine.txt`.

Two things to read by eye, because a kernel cannot: that `Zeta2Defs.zeta2` and `LiouvilleWith`
mean what the README says (both are `#print`ed by `Receipts.lean`), and that the literal is the
one claimed.

## Layout

| path | what |
|---|---|
| `src/Zeta2*.lean`, `src/*.lean` (flat names) | the proof chain: definitions, the arithmetic layer, the analytic layer, the assembly (165 modules, 73,092 lines) |
| `src/StarForallCandt{1,2}{Base,Assemble,K*}.lean` | 559 **generated** modules: the creative-telescoping certificate as exact integer data, one kernel-checked evaluation per piece |
| `src/PrimeNumberTheoremAnd/`, `src/Architect*` | vendored third-party code (Apache-2.0), see `THIRD_PARTY/` (23 modules, 13,184 lines) |
| `generators/star/` | the generator that wrote the generated modules, its inputs, and the sha256 manifests; `verify_manifests.sh` re-checks every generated file against them |
| `receipts/` | the output of the private development repository's own checks — the printed axioms and types of the headline theorems and a count of `sorry` over every module, each labelled in `PROVENANCE.txt` with the commit it was read at, and two runs in which deliberately altered statements and proofs are refused, which name no commit — plus this tree's own build output (`this-machine.txt`, `build-stats.txt`), the counts of `src/` (`COUNTS.json`) and the sha256 of every file of `src/` (`SOURCES.sha256`) |
| `scripts/` | `verify.sh`, the receipt checker `check_receipts.py`, and `measure_build.py`, which ran the build and wrote `receipts/build-stats.txt` |

**Reading the sources.** Module header comments are working notes from the proof's development.
They name steps of an internal proof plan and files of the private development repository, where the
search lives (the search code is not published; checking the proof does not need it); the generated
modules' headers name their generator by its path there. What each
module proves is its theorem statements; the claim as a whole is what `src/Receipts.lean` prints.

## How the proof goes

The construction is Zudilin's: a Mellin–Barnes integral of a ratio of Gamma functions with
parameters (13, 11, 9, 15; 26) — in Zudilin's notation a = (13n+1, 11n+1, 9n+1, 15n+1),
b = (1, 2n+1, 4n+1, 26n+2) — which is small and equals q_n·ζ(2) − p_n, where q_n is an integer and
p_n is a rational number whose denominator divides D_{16n}·D_{15n} (D_k is the least common
multiple of the integers up to k). Each of his two constructions of the same q_n and p_n bounds the
power of every prime in q_n and in D_{16n}·D_{15n}·p_n; taking the larger exponent prime by prime
gives a common factor Φ̃_n of both. Three rates feed a standard criterion, each in the form of the
bound the formal proof uses: the form decays at rate at least 29.10787127, q_n grows at rate at most
42.03361581, and D_{16n}·D_{15n}/Φ̃_n grows at rate at most 15.01912095 (the rate of D_{16n}·D_{15n}
less the common factor's own rate). The criterion turns them into the exponent
1 + (42.03361581 + 15.01912095)/(29.10787127 − 15.01912095), which is below 5.0495243.

These parameters were found by a computer search over Zudilin's family, which ranked each choice by
the exponent it gives with the common factor from both constructions. A second search, written
separately in qedbook, a computer algebra system developed by Jonathan Kleid, found the same
parameters. That the two constructions agree is a theorem of Marcovecchio under
hypotheses these parameters satisfy; the formal proof does not use it and re-proves the agreement
for this member from a common recurrence. qedbook also produced the exact certificates and the
coefficient data the formal proof consumes. Nothing computed there is trusted: every emitted value
enters the proof as data that Lean's kernel re-verifies.

The development proves several results that Mathlib, at the pinned commit, does not have: an explicit complex Binet bound
for log Γ, an explicit partial-fraction decomposition with simple and double poles (Mathlib has the
general form for coprime denominators), a linear-forms criterion for `¬ LiouvilleWith`, a
Poincaré-type growth bound for third-order recurrences, and the p-adic analysis of the profile
function that gives the common factor.

## Provenance and authorship

The search and the Lean proof were produced by Anthropic's Claude models, working under Jonathan
Kleid's direction and using qedbook, a computer algebra system he develops. The mathematics is that of Zudilin, *Two
hypergeometric tales and a new irrationality measure of ζ(2)*, Ann. Math. Québec 38 (2014), at new
parameters. That its two constructions agree, under hypotheses these parameters satisfy, is due to
Marcovecchio, *Two integral transformations related to ζ(2)*,
Mosc. J. Comb. Number Theory 9 (2020). PNT+ is by Alex Kontorovich, Terence Tao and contributors.

## Licence

Apache License 2.0 for this repository's own files (`LICENSE`, `NOTICE`). The vendored code keeps
its upstream licences in `THIRD_PARTY/`.
