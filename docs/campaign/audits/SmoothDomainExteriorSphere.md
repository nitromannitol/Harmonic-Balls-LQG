# Uniform exterior sphere for smooth bounded open sets (audit)

Task: `general-green-uniform-exterior-sphere` (worker z3, round 47, EFFORT max). Owned files:
`HarmonicBalls/Proofs/Potential/SmoothDomainExteriorSphere.lean` (301 lines) and this audit.

Source: `notes/wpn-steps4/steps4-r2.tex`, SECTION1 only (lines 29-283; sha256
`3fc457109868aa94234b0a2c19ac522b9117d79b0203d4fbf8a546db5d74a913`, checked). Geometry: lines 138-151 (one uniform
exterior sphere of radius `2d` with centre `z + 2d n_z`; `w_z = z + d n_z`; the half-radius bound
`|x - w_z|² ≥ d² + ½|x - z|²` on `closure O`). Independent audit: `AUDIT-steps4-t1-r2.md`, VERDICT CORRECT.
The barrier comparison (lines 151-160) and the Green identification are not part of this task.

## Lean statements (exact)

- `HarmonicBalls.SmoothDomainExteriorSphere.exists_uniform_exterior_ball_of_isSmoothBoundedOpen`
  (file line 168):
  `{O : Set ℂ} (hO : IsSmoothBoundedOpen O) : ∃ R : ℝ, 0 < R ∧ ∀ z ∈ frontier O, ∃ a : ℂ, dist a z = R ∧ ∀ x ∈ closure O, R ≤ dist a x`
- `HarmonicBalls.SmoothDomainExteriorSphere.exists_half_radius_geometry_of_isSmoothBoundedOpen`
  (file line 268):
  `{O : Set ℂ} (hO : IsSmoothBoundedOpen O) : ∃ d : ℝ, 0 < d ∧ ∀ z ∈ frontier O, ∃ w : ℂ, dist w z = d ∧ ∀ x ∈ closure O, d ^ 2 + (1 / 2 : ℝ) * dist x z ^ 2 ≤ dist x w ^ 2`
  Witnesses: `d = R / 2`, `w = z + (1/2 : ℝ) • (a - z)` where `a` is the centre of the first theorem.

## Hypotheses

The only hypothesis is `hO : IsSmoothBoundedOpen O`, the actual global predicate of `Draft/Section2.lean:138-140`:
`Bornology.IsBounded O ∧ ∃ ρ : ℂ → ℝ, ContDiff ℝ ∞ ρ ∧ O = {z | ρ z < 0} ∧ ∀ z, ρ z = 0 → fderiv ℝ ρ z ≠ 0`.
No connectedness, no boundary-measure assumption, no Proposed or External input, no edit of any frozen definition.
Empty `O` and empty `frontier O` are covered (the first theorem is then vacuous in `z`; the gradient bound uses `g = 1`).
The module imports `HarmonicBalls.Draft.Section2` (for the predicate) and Mathlib only.

## Route (written argument, global defining function)

1. `frontier O ⊆ {ρ = 0}`: `closure O ⊆ {ρ ≤ 0}` (`closure_lt_subset_le`), `O` open (`isOpen_lt`), so a point of
   `frontier O = closure O \ interior O` is not in `O`, hence `ρ ≥ 0`. `frontier O` is compact (closed, bounded).
2. `exists_hessian_bound` (line 82): `M₀ ≥ 0` bounds `‖fderiv ℝ (fderiv ℝ ρ) y‖` on `cthickening 1 (frontier O)`, which
   contains `closedBall z 1` for every `z ∈ frontier O`. Source of uniformity: compactness plus continuity of the second
   derivative. This replaces the finite implicit-function charts of lines 140-150.
3. `exists_gradC_lower_bound` (line 71): `g > 0` with `g ≤ ‖gradC ρ z‖` on `frontier O`, where
   `gradC ρ z = dρ(z)(1) + dρ(z)(i) · i` (line 36) represents the differential (`fderiv_apply_eq_gradC`, line 46).
   Nonvanishing of `dρ` on `{ρ = 0}` gives positivity (`gradC_ne_zero`, line 55).
4. `norm_fderiv_sub_le` (line 95): `‖dρ(y) - dρ(z)‖ ≤ M ‖y - z‖` on `closedBall z 1`
   (`Convex.norm_image_sub_le_of_norm_fderiv_le`, Mathlib `Analysis/Calculus/MeanValue.lean:500`).
5. `abs_sub_sub_fderiv_le` (line 105): Taylor's inequality `|ρ(z+v) - ρ z - dρ(z) v| ≤ M‖v‖²/2` for `‖v‖ ≤ 1`, via the
   one-variable remainder `F(s) = ρ(z + s v) - ρ z - s dρ(z)v` and `image_norm_le_of_norm_deriv_right_le_deriv_boundary`
   (`MeanValue.lean:299`) with bound `M‖v‖² s²/2`.
6. `exterior_core` (line 152): algebra `L ≤ M₀N/2`, `c n = R`, `g ≤ n`, `R M₀ ≤ g` ⊢ `2cL ≤ N`.
7. Main theorem (line 168): `R = min (1/2) (g/(2(M₀+1)))`, `G = gradC ρ z`, `c = R/‖G‖`, centre `a = z + c G`.
   `dist a z = R` since `‖cG‖ = R`. For `x ∈ closure O` put `v = x - z`:
   - `‖v‖ ≤ 1` (near): `ρ x ≤ 0` and step 5 give `L := dρ(z) v ≤ M₀‖v‖²/2`; with `‖cG - v‖² = c²|G|² - 2cL + ‖v‖²`
     and `c²|G|² = R²`, step 6 gives `R² ≤ ‖cG - v‖²`.
   - `‖v‖ > 1` (far): `‖cG - v‖ ≥ ‖v‖ - R > 1 - 1/2 ≥ R`.
8. Half-radius (line 268): with `w = (z + a)/2`, `|x - w|² = (|x - z|² + |x - a|²)/2 - |a - z|²/4` (parallelogram identity,
   checked in coordinates by `ring`), `|a - z| = R`, `|x - a| ≥ R`, so `|x - w|² ≥ |x - z|²/2 + R²/4 = d² + |x - z|²/2`
   with `d = R/2`.

Mathematical content is the written argument of `steps4-r2.tex` lines 138-151 with the uniform bounds obtained from the
global defining function. No new premise and no unsourced claim is used. No connectedness is used.

## Declared route difference

The written argument obtains uniformly bounded second derivatives from finitely many implicit-function charts and then
shrinks the radius so that the balls stay in each chart. Because `IsSmoothBoundedOpen` supplies one global `C^∞`
defining function, the same uniform bounds come from compactness of `cthickening 1 (frontier O)` and the chart
restriction becomes `‖v‖ ≤ 1`. No implicit-function theorem and no chart construction is needed. This is a
re-route of the same estimate, not a new hypothesis.

## Checks

- `lc` on `HarmonicBalls/Proofs/Potential/SmoothDomainExteriorSphere.lean` (warnings as errors): CHECK OK, log
  `050744-3728431`.
- `lb HarmonicBalls.Proofs.Potential.SmoothDomainExteriorSphere`: BUILD OK, log `050828-3800232`.
- `#print axioms` (probe `scratch/z3probe/AxiomsSDES.lean`, untracked, lc log `050954-3951780`): all ten declarations
  depend only on `[propext, Classical.choice, Quot.sound]`.
- Raw scan of the file for `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, `extern`, `implemented_by`,
  `maxHeartbeats`, `maxRecDepth`, `set_option`, `decide`: 0 hits.
- Import closure (`scratch/z3probe/closure.py`): 9 project modules, 0 Lattice or Bonanno modules, so no Bonanno
  credit line is required.
- Mathlib lemma names were located by grep and then verified by the compile (no new axiom or input). Main ones:
  `Metric.isCompact_of_isClosed_isBounded`, `IsCompact.cthickening`, `Metric.mem_cthickening_of_dist_le`,
  `IsCompact.exists_isMinOn`, `sq_le_sq₀`, `le_div_iff₀`, `closure_lt_subset_le`, `ContDiff.fderiv_right`,
  `ContDiff.continuous_fderiv`.

## Not touched

`Draft/*`, `FROZEN`, `Defs/*`, `External/*`, `Proposed/*`, the paper, `HarmonicBalls.lean`, and other workers' files.
The consumers `Steps/Sec2/GreenPotentialGeneral.lean:24-31` and `Proofs/Sec2/GreenPotentialGeneral.lean:18` are not
wired to these theorems by this task. Still separate: the Dirichlet harmonic extension, the quantitative barrier
comparison (`steps4-r2.tex` lines 151-160), and the Green identification.
