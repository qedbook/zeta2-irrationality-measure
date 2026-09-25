# pnt_port — the `MediumPNT` import cone of PrimeNumberTheoremAnd, vendored onto our Mathlib pin

Owner ruling 2026-09-24 (docs/reference/owner-rulings.md) funds porting the `MediumPNT` dependency
cone onto our Mathlib pin, so that the ζ(2) chain's hypothesis `Zeta2LegA.psiErrorBoundStatement`
is discharged in the same kernel (`external_tests/zeta2_arith/Zeta2Hpsi.lean`).

This directory is a **third-party copy**. The code is not ours. Both upstreams are licensed under
Apache-2.0, and their licence texts sit beside it unchanged:

| upstream | URL | commit | files here | licence |
|---|---|---|---|---|
| PrimeNumberTheoremAnd (PNT+) | https://github.com/AlexKontorovich/PrimeNumberTheoremAnd | `a5154676af9aa3095150ee410cdda80555aa0642` (2026-08-30, "fix(Dusart): make corollary_5_3_a a strict inequality (#1708)") | `PrimeNumberTheoremAnd/**` (14 files, 12,114 lines upstream) | `LICENSE.PrimeNumberTheoremAnd` (Apache-2.0) |
| LeanArchitect | https://github.com/hanwenzhu/LeanArchitect | `d9013cc08bd2b5483e837368dfa4cc7ead92a5c2` (PNT+'s `lake-manifest.json` pin at the commit above, inputRev `v4.32.0-rc1`) | `Architect.lean`, `Architect/**` (9 files, 1,068 lines) | `LICENSE.LeanArchitect` (Apache-2.0) |

Neither upstream ships a `NOTICE` file at these commits. The copyright headers inside each
source file are kept verbatim.

**Why this commit.** `a5154676` is the commit on which `PsiErrorBound.psi_error_bound` was
attested (`external_tests/zeta2_binet_design/out_hpsi_settlement.txt`). Upstream `main` has moved
since then: on 2026-09-24 it bumped to v4.33.1 in `55270df`, and it rewrote `MediumPNT.lean` by
+569/−694 lines. That tree also elaborates on our pin, with one error: P1 below. We port the
attested text so that the discharge is the one already audited.

**What is here.** Here is the whole file-level import cone of `PrimeNumberTheoremAnd.MediumPNT`, minus
Mathlib, Batteries and Lean core. Two methods independently give the same 23 modules: a
source-import walk, and the olean header (`env.header.moduleNames`). Module paths are
preserved, so this directory is a Lean source root: `PrimeNumberTheoremAnd.ZetaBounds` is
`PrimeNumberTheoremAnd/ZetaBounds.lean`.

**Verification that the copy is faithful.** Before the patches were applied, each of the 23 files
was compared byte-for-byte against `git show <commit>:<path>` of its upstream on the buildbox,
and 23 of 23 were identical. The ONLY differences from upstream are the two patches below, plus the
one-line `-- MODIFIED for the CAS port` comment at each patch site. That comment is Apache-2.0
§4(b)'s notice that the file was changed.

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

The constant-level cone probe traces `MediumPNT`'s type and value transitively down to the
Mathlib boundary. It uses 324 of the cone's 750 declarations, and **no** declaration of LeanArchitect
(`Architect*`), `PrimeNumberTheoremAnd.Sobolev`, or `PrimeNumberTheoremAnd.Tactic.AdditiveCombination`.
The last of these is still an elaboration-time dependency, because the `additive_combination` tactic is
invoked in `ResidueCalcOnRectangles`. All of them elaborate cleanly on our pin.

Dropping Architect would mean stripping 106 `@[blueprint …]` attributes across 7 files plus
the `import Architect` lines. Dropping Sobolev would mean deleting its one importer's
`import` (in `Fourier`) and whatever of `Fourier` uses it. That is over a hundred further edits to vendored text,
compared with the 2 edits the port actually needs, and it would buy nothing a reviewer can check more easily. They
are therefore kept. A later pruning is possible and is recorded as optional in the port map.

## Re-deriving

The census, the harness that measured it, and the map are archived in the port-map scratch
(`MAP.md`, 2026-09-24). The clean-store build of this cone goes through
`external_tests/zeta2_arith/clean_close/` (hierarchical module paths supported since this
landing).
