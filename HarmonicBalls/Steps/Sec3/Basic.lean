import HarmonicBalls.Steps.SecA.AppendixA
import HarmonicBalls.Proofs.Potential.Fundamental
import HarmonicBalls.Draft.Section3

/-!
# Section 3 from Appendix A: the almost sure event and the substitution

Shared material for the reductions of Lemmas 3.1-3.5 (subsec:basic-properties, lines 612-662) to Appendix A
(sec:obstacle-appendix, lines 3522-3900): "these results are standard but for completeness are proved in Appendix A"
(line 614).

## The paper's reduction

* **The almost sure event** (lines 3525-3530). Appendix A works with any Radon measure `μ` satisfying the volume
  growth condition eq:volume-growth on `B_R`; "this implies the results in Section 3.2 as the Liouville measure is
  a.s. a Radon measure which satisfies eq:volume-growth", by Lemma 2.4 and the scaling properties of `h`, `μ_h`. In
  Lean: Input I2 (`LQGVolumeGrowthAllScalesStmt`, Draft/Section2.lean) and the Radon property of `IsLQGMeasureOfField`
  give ONE event of probability 1 on which `μ_h` is Radon and satisfies eq:volume-growth on every `B_R`, with exponents
  fixed in the ranges of [C1] (`ae_isLocallyFiniteMeasure_volumeGrowth`). Since the Appendix A statements are
  deterministic in `μ`, the Section 3 statements hold on that event for all `t, r, z` simultaneously.
* **The substitution** (lines 3574-3578): `v_{B_r;z}(t) = ṽ_t - q_{B_r}`, `Λ_{B_r;z}(t) = Λ_t`, `u_{B_r;z}(t) = v_t`
  ("each of the lemmas in Section 3.2 will follow via this substitution"). This is
  `ObstacleCompatibilityShiftStep` (Steps/SecA/ObstacleCompatibility.lean), consumed here as an explicit step.

## Gap (general radius and pole)

Appendix A proves Lemmas A.1-A.5 "for notational simplicity" with `R = 1` and pole `z = 0` only (lines 3545-3546),
and Lemma A.6 with pole `0` (lines 3838-3853), while Lemmas 3.1-3.5 concern `B_r` with every pole `z ∈ B_r`
(lines 621-659). The printed statements A.1-A.6 (Draft/SectionA.lean) therefore do not imply Lemmas 3.1-3.5:
rescaling by `r` handles the radius, but for `z ≠ 0` the obstacle `-t G_{B_r}(z,·)` is not the image of
`-t G_{B_1}(0,·)` under any similarity of `B_r`, and the disc automorphism moving `z` to `0` changes `μ` into its
pushforward (with distorted volume growth near `∂B_1`) and needs the conformal covariance of the distributional
Laplacian, none of which is in the paper. The reductions of this directory consume the general forms
(`...General`, any `R > 0` and pole `z ∈ B_R`; the carving of Appendix A proves them from general steps) and, for
Lemma A.6, the general-pole steps `ObstacleCompatibilityPoleStep1/2` of ClusterCompatibility.lean.

## Contents

* `ae_isLocallyFiniteMeasure_volumeGrowth` — the almost sure event (proved from I2).
* `mem_shiftedSupersolutions_of_eqOn`, `HasLaplacian.congr_eqOn` — membership in `S̃(t)` and distributional
  identities depend only on values on the closed ball, resp. on `U`.
* `HasLaplacian.sub_const_mul_greenFunction` — `Δ (u - t G_{B_r}(z,·)) = Δu + t δ_z`, from Prop 2.3.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Laplacian

/-! ## The almost sure event -/

/-- Exponents in the ranges of [C1] (Lemma 2.4, line 497) exist: `β⁺ ∈ (0, min {(2-γ)²/2, γ(Q-α₀)})` and
`β⁻ > max {(2+γ)²/2, γ(Q-α₀)}`. -/
theorem exists_volumeGrowth_exponents {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) :
    ∃ βplus βminus : ℝ, 0 < βplus ∧ βplus < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) ∧
      max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < βminus ∧ 0 < βminus := by
  have h1 : 0 < (2 - γ) ^ 2 / 2 := by
    have : 0 < 2 - γ := by linarith
    positivity
  have h2 : 0 < γ * (lqgQ γ - α₀) := mul_pos hγ (sub_pos.2 hα)
  have hm : 0 < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) := lt_min h1 h2
  refine ⟨min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) / 2, max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) + 1,
    half_pos hm, half_lt_self hm, lt_add_one _, ?_⟩
  exact (h2.trans_le (le_max_right _ _)).trans (lt_add_one _)

universe u

/-- **The almost sure event of Section 3.2** (lines 3528-3530). For `0 < γ < 2` and `α₀ < Q`, there are exponents
`β⁻, β⁺` such that almost surely `μ_h` is a Radon measure satisfying the volume growth condition eq:volume-growth
(with [C2]) on every ball `B_R`, `R > 0`. From Input I2 (`LQGVolumeGrowthAllScalesStmt`) and the Radon property in
`IsLQGMeasureOfField`. -/
theorem ae_isLocallyFiniteMeasure_volumeGrowth (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) {γ α₀ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∃ βminus βplus : ℝ, ∀ᵐ ω ∂P,
      IsLocallyFiniteMeasure (μ ω) ∧ ∀ R : ℝ, 0 < R → VolumeGrowth (μ ω) R βminus βplus := by
  obtain ⟨βp, βm, hβp, hβp', hβm, hβm0⟩ := exists_volumeGrowth_exponents hγ hγ2 hα
  refine ⟨βm, βp, ?_⟩
  filter_upwards [hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ, hμ] with ω hω hlim
  refine ⟨hlim.isLocallyFiniteMeasure, fun R hR => ?_⟩
  obtain ⟨r₀, hr₀, h⟩ := hω R hR βp βm hβp hβp' hβm
  exact ⟨hβm0, hβp, r₀, hr₀, h⟩

/-! ## Congruence lemmas -/

/-- Membership in `S̃(t)` (eq:shifted-supersolutions, line 3556) depends only on the values on the closed ball. -/
theorem mem_shiftedSupersolutions_of_eqOn {μ : Measure ℂ} {R t : ℝ} {z : ℂ} {w w' : ℂ → ℝ}
    (hw : w ∈ shiftedSupersolutions μ R z t) (heq : EqOn w w' (closedBall 0 R)) :
    w' ∈ shiftedSupersolutions μ R z t := by
  obtain ⟨hc, hΔ, hob⟩ := hw
  refine ⟨hc.congr heq.symm, hΔ.congr_eqOn measurableSet_ball (heq.mono ball_subset_closedBall),
    fun x hx hxz => ?_⟩
  rw [← heq hx]
  exact hob x hx hxz

/-- `Δw = μpos - μneg` in `U` depends only on the values of `w` on `U`. -/
theorem HasLaplacian.congr_eqOn {w w' : ℂ → ℝ} {μpos μneg : Measure ℂ} {U : Set ℂ}
    (h : HasLaplacian w μpos μneg U) (hU : MeasurableSet U) (heq : EqOn w w' U) :
    HasLaplacian w' μpos μneg U := by
  refine ⟨h.1.congr ((ae_restrict_iff' hU).2 (Eventually.of_forall heq)), fun φ hφ => ?_⟩
  have hfun : (fun x => w' x * Δ φ x) = fun x => w x * Δ φ x := by
    funext x
    by_cases hx : x ∈ U
    · rw [heq hx]
    · rw [laplacian_eq_zero_of_notMem_tsupport (fun hx' => hx (hφ.2.2 hx')), mul_zero, mul_zero]
  rw [hfun]
  exact h.2 φ hφ

/-! ## Laplacian of `u - t G_{B_r}(z,·)` -/

/-- A function locally integrable on an open `U` pairs integrably with the Laplacian of a test function on `U`
(named `_of_test` to avoid the clash with `integrable_mul_laplacian` of Proofs/SecA/Basic.lean). -/
theorem integrable_mul_laplacian_of_test {w : ℂ → ℝ} {U : Set ℂ} (hw : LocallyIntegrableOn w U) {φ : ℂ → ℝ}
    (hφ : IsTestFunction U φ) : Integrable (fun x => w x * Δ φ x) := by
  have hK : IsCompact (tsupport φ) := hφ.2.1
  have hwK : IntegrableOn w (tsupport φ) := hw.integrableOn_compact_subset hφ.2.2 hK
  have hΔ : Continuous (Δ φ) := continuous_laplacian_of_contDiff (hφ.1.of_le (by norm_cast))
  have hon : IntegrableOn (fun x => w x * Δ φ x) (tsupport φ) := hwK.mul_continuousOn hΔ.continuousOn hK
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 hon
  intro x hx
  by_contra hxK
  exact hx (show w x * Δ φ x = 0 by rw [laplacian_eq_zero_of_notMem_tsupport hxK, mul_zero])

/-- `Δu = μ - t δ_z` in `U` and `ΔG = -δ_z` in `U` give `Δ(u - t G) = μ` in `U` (`t ≥ 0`). Used for
`Δ v_{B_r;z}(t) = μ_h|_Λ + ν|_{∂Λ}` from the odometer identity, `v = u - t G_{B_r}(z,·)` (eq:limit-odometer). -/
theorem HasLaplacian.sub_const_mul {u G : ℂ → ℝ} {M : Measure ℂ} {U : Set ℂ} {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hu : HasLaplacian u M (ENNReal.ofReal t • Measure.dirac z) U) (hG : HasLaplacian G 0 (Measure.dirac z) U) :
    HasLaplacian (fun x => u x - t * G x) M 0 U := by
  refine ⟨hu.1.sub (hG.1.smul t), fun φ hφ => ?_⟩
  obtain ⟨hM, -, hu'⟩ := hu.2 φ hφ
  obtain ⟨-, -, hG'⟩ := hG.2 φ hφ
  refine ⟨hM, integrable_zero_measure, ?_⟩
  have i1 := integrable_mul_laplacian_of_test hu.1 hφ
  have i2 := (integrable_mul_laplacian_of_test hG.1 hφ).const_mul t
  have hfun : (fun x => (u x - t * G x) * Δ φ x) = fun x => u x * Δ φ x - t * (G x * Δ φ x) := by
    funext x; ring
  rw [hfun, integral_sub i1 i2, integral_const_mul, hu', hG', integral_smul_measure, integral_dirac,
    integral_zero_measure, ENNReal.toReal_ofReal ht]
  simp only [smul_eq_mul]
  ring

end HarmonicBalls
