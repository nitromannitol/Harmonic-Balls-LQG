# Audit: GreenRowUniformIntegrability (task green-row-uniform-absolute-continuity, worker q2)

Module: `HarmonicBalls/Proofs/Potential/GreenRowUniformIntegrability.lean` (new, 126 lines, namespace `HarmonicBalls`).
Carrier: `ℂ` with `volume`. The row is `greenFunction U x : ℂ → ℝ` (`Defs/Green.lean:70`), the literal zero-extended Green row (value `0` off `U`).
Hypotheses of the main theorem: `IsOpen U` and `Bornology.IsBounded U` only. No `External` or `Proposed` module is imported; no literature input.

## Declarations

| Line | Declaration | Statement (binders, abbreviated) |
|---|---|---|
| 31 | `greenFunction_row_abs_eq` | `(hUb : IsBounded U) (x y : ℂ) : \|G_U(x,y)\| = G_U(x,y)` (nonnegativity, `greenFunction_nonneg`) |
| 37 | `greenFunction_row_integrableOn` | `(hU : IsOpen U) (hUb) (x : ℂ) (A : Set ℂ) : IntegrableOn (greenFunction U x) A`; the global row theorem restricted to `A` |
| 44 | `setIntegral_greenFunction_row_le_ball_add_compl` | `{R C : ℝ} (hR : 0 < R) (hsub : U ⊆ ball 0 R) (hloc : uniform local volume bound with constant C) {r} (hr : 0 < r) (x : ℂ) {A} (hAfin : volume A < ⊤)`: `∫_A G_U(x,·) ≤ C r² (1 + \|log r\|) + (2π)⁻¹ log⁺(2R/r) · (volume A).toReal` |
| 89 | `greenFunction_row_uniform_absolute_continuity` | `(hU : IsOpen U) (hUb : IsBounded U) : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ A : Set ℂ, MeasurableSet A → volume A < ENNReal.ofReal δ → ∀ x : ℂ, (∫ y in A, \|greenFunction U x y\|) < ε` |

The main theorem's `δ` is fixed before `A` and `x` are introduced. It depends only on `ε`, `R` and `C` from `U`, and the chosen radius `r`.

## Route (the written estimate of `GreenPoleL1Continuity.lean:11-16`)

1. `|G| = G` everywhere (nonnegativity), so the integrand is rewritten and the absolute value disappears.
2. Split `A = (A ∩ B(x,r)) ⊔ (A \ B(x,r))` with `integral_inter_add_sdiff`. Integrability on `A` comes from `integrable_greenFunction_pole`.
3. Disc part: `∫_{A∩B} G ≤ ∫_B G ≤ C r²(1+|log r|)` by `setIntegral_mono_set` (nonnegativity) and the uniform local bound `exists_greenFunction_local_volume_bound`.
4. Off-disc part: for `‖y-x‖ ≥ r`, `G(x,y) ≤ (2π)⁻¹ log⁺(2R/‖y-x‖) ≤ (2π)⁻¹ log⁺(2R/r)` (`greenFunction_le_posLog_div_norm`, `Real.posLog_le_posLog`). Then `norm_setIntegral_le_of_norm_le_const` gives `≤ M · volume(A).toReal`, where `M = (2π)⁻¹ log⁺(2R/r)`.
5. Choice: `r` with `C r²(1+|log r|) < ε/2` from `tendsto_sq_mul_one_add_abs_log` (`Tendsto.eventually_lt_const`, `self_mem_nhdsWithin`, `Eventually.exists`). Then `δ = ε/(2(M+1))`, so `(M+1)δ = ε/2` and `Mδ < ε/2`. `ENNReal.toReal_lt_of_lt_ofReal` turns `volume A < ofReal δ` into `(volume A).toReal < δ`.

The constant `C` is uniform in the pole `x` and in the centre (`exists_greenFunction_local_volume_bound`), and `M` depends only on `R, r`. So `δ` is uniform in `x` and `A`.

## Providers (all committed at or before b7d689b; none is an active task's file)

- `HarmonicBalls.greenFunction_nonneg` (`HarmonicBalls/Defs/Green.lean:134`).
- `HarmonicBalls.integrable_greenFunction_pole` (`Proofs/Potential/GreenPoleL1Continuity.lean:62`, commit 7b9c811). This is the global-row theorem used for restriction.
- `HarmonicBalls.greenFunction_le_posLog_div_norm` (`GreenPoleL1Continuity.lean:30`).
- `HarmonicBalls.exists_greenFunction_local_volume_bound` (`Proofs/Potential/GreenLocalVolumeBound.lean:185`, commit 7007db1).
- `HarmonicBalls.tendsto_sq_mul_one_add_abs_log` (`GreenLocalVolumeBound.lean:196`).
- Mathlib: `MeasureTheory.integral_inter_add_sdiff` (`Integral/Bochner/Set.lean:114`; the `integral_inter_add_diff` alias is deprecated), `setIntegral_mono_set` (`Set.lean:739`), `norm_setIntegral_le_of_norm_le_const` (`Set.lean:615`), `ENNReal.toReal_lt_of_lt_ofReal` (`Basic/ENNReal/Real.lean:293`), `ENNReal.toReal_mono` (`Real.lean:67`), `Real.posLog_le_posLog` (`Analysis/SpecialFunctions/Log/PosLog.lean:116`), `div_le_div_of_nonneg_left` (`Algebra/Order/GroupWithZero/Basic.lean:1270`), `measurableSet_ball`.
- Deprecated names avoided: `Set.diff_subset` (use `Set.sdiff_subset`), `integral_inter_add_diff`, `HasSubset.Subset.eventuallyLE`.

## Import closure

- Direct import: `HarmonicBalls.Proofs.Potential.GreenPoleL1Continuity` only.
- Measured with `#eval` on `env.header.moduleNames` in a scratch file outside the repository (`/tmp/q2-ax/Closure.lean`, lc log `logs/lc/014634-3314019.log`): total 11,796 modules; HarmonicBalls 352 (this module adds one); Mathlib 8,537; MarkovProcess 152; LatticeProb 2 (`LatticeProb.Prob.Birkhoff`, `LatticeProb.Prob.MaximalErgodic`); others 2,753; forbidden names (`BoundedDensityGreen*`, `GreenRowL1Continuous`, `GreenPotentialLInfinityFunctional`) 0.
- Independence at b7d689b: the HarmonicBalls closure of `GreenPoleL1Continuity` and `Defs.Green` as of b7d689b has 351 modules. None of the 7 HarmonicBalls files changed in `b7d689b..HEAD` (`BoundedDensityGreenContinuity`, `BoundedDensityGreenStability`, `GreenPotentialLInfinityFunctional`, and four Sec11 files) lies in that closure.

## Checks

- `lc`: CHECK OK (`logs/lc/014259-2951495.log`). The first run failed only on the deprecated `Set.diff_subset`, and it was fixed.
- `lb HarmonicBalls.Proofs.Potential.GreenRowUniformIntegrability`: BUILD OK (`logs/lb/014336-3015134.log`).
- Printed axioms (scratch file, `logs/lc/014443-3128580.log`): all four declarations depend only on `[propext, Classical.choice, Quot.sound]`.
- Raw scan of the owned file for `sorry|axiom|admit|native_decide|maxHeartbeats|set_option`: 0 hits (comments included). No `set_option`.

## Credit

The module docstring credits Leonardo Bonanno. His code reaches this file only through the pinned Lattice-Probability (lean-v4.35) port (the `LatticeProb.Prob.*` modules above). The Green function is the one of Armitage–Gardiner (`Defs/Green.lean`).

## Remaining consumers

None in HarmonicBalls at this commit. The names are new, and `grep` finds no other use. The queued task `q2.next.md` states that it must not import or depend on this active file; no reuse by it is claimed here.

## Not claimed

No normal representative of `G_U`, no boundary regularity, no singular-source representative, no general-domain reciprocity, no compact-pole divergence (reserved to h2), no E51 or numbered closure, no physical exponent, no metric moment, no Pfeffer Def 1.6 membership or Prop 4.6, no literature input.
