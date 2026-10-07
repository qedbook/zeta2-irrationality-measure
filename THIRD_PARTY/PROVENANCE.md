# The `MediumPNT` import cone of PrimeNumberTheoremAnd, vendored onto this development's Mathlib

The ζ(2) development proves its one analytic input, `Zeta2LegA.psiErrorBoundStatement` (an error
bound for Chebyshev's `ψ`), from `PrimeNumberTheoremAnd.MediumPNT`, in `Zeta2Hpsi`. So that this
proof is checked by the same kernel and against the same Mathlib as the rest of the development,
the modules `MediumPNT` imports are copied here and adapted to this development's toolchain.

The vendored files are a **third-party copy**. The code is not ours. Both upstreams are licensed
under Apache-2.0, and their licence texts are shipped unchanged beside this file:

| upstream | URL | commit | files here | licence |
|---|---|---|---|---|
| PrimeNumberTheoremAnd (PNT+) | https://github.com/AlexKontorovich/PrimeNumberTheoremAnd | `a5154676af9aa3095150ee410cdda80555aa0642` (2026-08-30, "fix(Dusart): make corollary_5_3_a a strict inequality (#1708)") | `PrimeNumberTheoremAnd/**` (14 files, 12,114 lines upstream) | `LICENSE.PrimeNumberTheoremAnd` (Apache-2.0) |
| LeanArchitect | https://github.com/hanwenzhu/LeanArchitect | `d9013cc08bd2b5483e837368dfa4cc7ead92a5c2` (PNT+'s `lake-manifest.json` pin at the commit above, inputRev `v4.32.0-rc1`) | `Architect.lean`, `Architect/**` (9 files, 1,068 lines) | `LICENSE.LeanArchitect` (Apache-2.0) |

Neither upstream ships a `NOTICE` file at these commits. The copyright headers inside each
source file are kept verbatim.

**Why this commit.** The argument in `Zeta2Hpsi` was written against this commit of PNT+.
Upstream `main` has since moved to Lean v4.33.1 (`55270df`) and rewritten `MediumPNT.lean` by
+569/−694 lines. That tree also elaborates on our pin, with one error: P1 below. We port the
older text so that the argument stays the one already checked.

**What is here.** Here is the whole file-level import cone of `PrimeNumberTheoremAnd.MediumPNT`, minus
Mathlib, Batteries and Lean core. Two methods independently give the same 23 modules: a
source-import walk, and the olean header (`env.header.moduleNames`). Module paths are
preserved: `PrimeNumberTheoremAnd.ZetaBounds` is `PrimeNumberTheoremAnd/ZetaBounds.lean`.

**Verification that the copy is faithful.** Before the patches were applied, each of the 23 files
was compared byte-for-byte against `git show <commit>:<path>` of its upstream,
and 23 of 23 were identical. The ONLY differences from upstream are the two patches below, plus the
one-line `-- MODIFIED for this port` comment at each patch site. That comment is the notice that
the file was changed, which section 4(b) of the Apache License 2.0 requires.

## The two patches

Our pin is toolchain `leanprover/lean4:v4.34.0-rc2` with mathlib `5aedf732`, where upstream's is v4.32.2
with mathlib `905b9581`. Against our pin the cone produced exactly two errors across 13,182 lines,
and both are **tactic-behaviour changes**. There were no renamed lemmas, changed signatures, missing API
or timeouts. There are also 31 deprecation warnings, which are not errors: the `Set.setOf_*` → `Set.ofPred_*`
rename accounts for 28 of them. They are left alone, so that the diff stays exactly the set of edits
that were required.

### P1 — `PrimeNumberTheoremAnd/MellinCalculus.lean` (upstream line 1296)

```diff
@@ -1293,6 +1293,7 @@
       · apply MeasureTheory.Measure.restrict_mono' SsubT.eventuallyLE le_rfl
       have : volume.restrict (Tx ×ˢ Ty) = (volume.restrict Tx).prod (volume.restrict Ty) := by
         rw [Measure.prod_restrict, MeasureTheory.Measure.volume_eq_prod]
+      change Integrable _ (volume.restrict (Tx ×ˢ Ty))
       conv => rw [this]; lhs; intro; rw [mul_comm]
```

Error on our pin, without the patch:

```
MellinCalculus.lean:1296:18-1296:22: error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  volume.restrict (Tx ×ˢ Ty)
in the target expression
  Integrable (fun x => f x.2 * ↑x.1 ^ (s - 1)) (volume.restrict {p | p.1 ∈ Tx ∧ p.2 ∈ Ty})
```

Why: on our pin, the earlier `simp only [IntegrableOn, Measure.restrict_restrict_of_subset SsubI]`
leaves the product set unfolded as the set-builder `{p | p.1 ∈ Tx ∧ p.2 ∈ Ty}`. The syntactic
`rw [this]` then no longer finds `Tx ×ˢ Ty`. The two sets are definitionally equal (`Set.prod`
is that set-builder), so `change` restates the goal in the old form, and the rest of upstream's
proof runs unchanged. This fixes a tactic-behaviour change; the mathematics is unchanged. Upstream's `main`
(`55270df`, v4.33.1) still carries this error on our pin.

### P2 — `PrimeNumberTheoremAnd/MediumPNT.lean` (upstream line 2450)

```diff
@@ -2447,7 +2447,6 @@
         apply intervalIntegral.integral_congr
         intro x hx
         simp
-        rfl
       rw [change_int_power, integral]
```

Error on our pin, without the patch:

```
MediumPNT.lean:2450:8-2450:11: error: No goals to be solved
```

Why: on our pin, `simp` closes the pointwise goal `1 / x ^ 2 = x ^ (-2 : ℤ)` outright. The
trailing `rfl` then had no goal left, which is an error. Deleting it keeps the proof
identical. This is a tactic-behaviour change. Upstream's rewrite of this file on `main` avoids it.

## Kept although unused by `MediumPNT`'s proof term

A constant-level trace follows `MediumPNT`'s type and value transitively down to the
Mathlib boundary. It uses 324 of the cone's 750 declarations, and **no** declaration of LeanArchitect
(`Architect*`), `PrimeNumberTheoremAnd.Sobolev`, or `PrimeNumberTheoremAnd.Tactic.AdditiveCombination`.
The last of these is still an elaboration-time dependency, because the `additive_combination` tactic is
invoked in `ResidueCalcOnRectangles`. All of them elaborate cleanly on our pin.

The vendored `Architect/Load.lean` sets `debug.skipKernelTC` inside `runEnvOfImports`, a helper
used only by the blueprint-export functions `latexOutputOfImportModule` and `jsonOfImportModule`,
which nothing in the shipped sources calls. It is the only kernel-bypass construct a search of
the shipped sources finds (`skipKernelTC`, `native_decide`, `ofReduceBool`, `implemented_by`,
`trustCompiler`).

Dropping Architect would mean stripping 106 `@[blueprint …]` attributes across 7 files plus
the `import Architect` lines. Dropping Sobolev would mean deleting its one importer's
`import` (in `Fourier`) and whatever of `Fourier` uses it. That is over a hundred further edits to vendored text,
compared with the 2 edits the port actually needs, and it would buy nothing a reviewer can check more easily. They
are therefore kept.

## Re-deriving

The file-level cone is the import closure of `PrimeNumberTheoremAnd.MediumPNT` minus Mathlib,
Batteries and Lean core. The declaration counts above come from tracing `MediumPNT`'s type and
value through the elaborated environment down to the Mathlib boundary.
