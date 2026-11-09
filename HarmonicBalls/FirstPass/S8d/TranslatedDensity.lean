import HarmonicBalls.FirstPass.S8d.CriterionThreeTransfer
import HarmonicBalls.FirstPass.S8c.Locality

/-! # FIRST-PASS helper (fp-S8d, owner n4): the singular phase event as a translated very-good event

For a measure `η` and a phase `q`, the phase-shifted very-good event at the origin (`PhaseVeryGoodAnnulus`, scale `1`,
phase `q`) is the very-good event of the translated measure `η.map (· - q)` at the centre `-q`
(`isVeryGoodAnnulus_iff_phaseVeryGoodAnnulus_map`, FirstPass/S8c/Locality.lean:22). This file

* gives that identity as `phaseVeryGood_iff_isVeryGood_translate`;
* transports the Weyl relation off the origin, `lam s = ∫_s |z|^{γ²} dν` for `0 ∉ s`
  (`LocalLQGInsertionWeylOffOrigin`, FirstPass/Frozen/S8c.lean:59, taken as the hypothesis `hW`), to the translated
  measures on the annulus `D = 𝔸_{1/4,2}(-q)`: the restriction of the translated regular measure has the density
  `y ↦ |y + q|^{γ²}` with respect to the translated singular one, and this density lies in `[(1/4)^{γ²}, 2^{γ²}]` on `D`;
* gives the two measure inequalities `k₁ • lam'|_D ≤ ν'|_D ≤ k₂ • lam'|_D` with `k₁ = (2^{γ²})⁻¹`, `k₂ = ((1/4)^{γ²})⁻¹`
  (`DensityComparison.lean`), and hence the comparison of the very-good events of the two translated measures
  (`isVeryGoodAnnulus_of_density`, `CriterionThreeTransfer.lean`).

No new mathematics: the change of variables for pushforwards, the definition of `withDensity`, and the bounds on the
density. The Weyl identity enters only as the hypothesis `hW`. -/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

/-- The phase-shifted very-good event at the origin equals the very-good event of the translated measure. -/
theorem phaseVeryGood_iff_isVeryGood_translate (η : Measure ℂ) (β : ℝ) (q : ℂ) (N : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ) :
    PhaseVeryGoodAnnulus η β 1 0 N a b C₁m C₁p C₂m C₂p C₃ q ↔
      IsVeryGoodAnnulus (η.map (fun w : ℂ => w - q)) β 1 (-q) N a b C₁m C₁p C₂m C₂p C₃ := by
  have hmeas : Measurable (fun w : ℂ => w - q) := measurable_id.sub_const q
  have hmeas' : Measurable (fun w : ℂ => w - -q) := measurable_id.sub_const (-q)
  have h := isVeryGoodAnnulus_iff_phaseVeryGoodAnnulus_map (η.map (fun w : ℂ => w - q)) β 1 (-q) N a b
    C₁m C₁p C₂m C₂p C₃
  have hid : (η.map (fun w : ℂ => w - q)).map (fun w : ℂ => w - -q) = η := by
    rw [Measure.map_map hmeas' hmeas]
    have hfun : ((fun w : ℂ => w - -q) ∘ fun w : ℂ => w - q) = id := by
      funext w
      simp
    rw [hfun, Measure.map_id]
  rw [hid, neg_neg] at h
  exact h.symm

/-- The Weyl relation off the origin, translated: for measurable `s ⊆ 𝔸_{1/4,2}(-q)`, the translated regular measure
of `s` is the integral of `|y + q|^{γ²}` against the translated singular measure. -/
theorem translated_regular_eq_integral (ν lam : Measure ℂ) (γ : ℝ) (q : ℂ)
    (hW : ∀ s : Set ℂ, MeasurableSet s → (0 : ℂ) ∉ s →
      lam s = ∫⁻ z in s, ENNReal.ofReal (‖z‖ ^ (γ * γ)) ∂ν)
    (s : Set ℂ) (hs : MeasurableSet s) (hsD : s ⊆ annulus (-q) (1 / 4) (2 * 1)) :
    (lam.map (fun w : ℂ => w - q)) s =
      ∫⁻ y in s, ENNReal.ofReal (‖y + q‖ ^ (γ * γ)) ∂(ν.map (fun w : ℂ => w - q)) := by
  have hT : Measurable (fun w : ℂ => w - q) := measurable_id.sub_const q
  rw [Measure.map_apply hT hs]
  have h0 : (0 : ℂ) ∉ (fun w : ℂ => w - q) ⁻¹' s := by
    intro h
    have hm : (0 : ℂ) - q ∈ annulus (-q) (1 / 4) (2 * 1) := hsD h
    exact hm.2 (by simp)
  rw [hW _ (hT hs) h0]
  have hf : Measurable (fun y : ℂ => ENNReal.ofReal (‖y + q‖ ^ (γ * γ))) :=
    ENNReal.measurable_ofReal.comp ((measurable_id.add_const q).norm.pow_const _)
  rw [setLIntegral_map hs hf hT]
  refine setLIntegral_congr_fun (hT hs) fun x _ => ?_
  simp

/-- Monotonicity of a scalar multiple of a measure. -/
theorem measure_smul_mono (c : ℝ≥0∞) {X Y : Measure ℂ} (h : X ≤ Y) : c • X ≤ c • Y := by
  rw [Measure.le_iff] at h ⊢
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (h s hs) zero_le

/-- For `y` in the annulus `𝔸_{1/4,2}(-q)`, the modulus `‖y + q‖` lies in `(1/4, 2)`. -/
theorem norm_bounds_of_mem_annulus (q y : ℂ) (hy : y ∈ annulus (-q) (1 / 4) (2 * 1)) :
    1 / 4 < ‖y + q‖ ∧ ‖y + q‖ < 2 := by
  simp only [annulus, Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le] at hy
  obtain ⟨h1, h2⟩ := hy
  rw [dist_eq_norm, sub_neg_eq_add] at h1 h2
  constructor <;> linarith

/-- The translated regular and singular measures on `D = 𝔸_{1/4,2}(-q)`: the restriction of the translated regular
measure is the restriction of the translated singular one with density `y ↦ |y + q|^{γ²}`. -/
theorem translated_restrict_eq_withDensity (ν lam : Measure ℂ) (γ : ℝ) (q : ℂ)
    (hW : ∀ s : Set ℂ, MeasurableSet s → (0 : ℂ) ∉ s →
      lam s = ∫⁻ z in s, ENNReal.ofReal (‖z‖ ^ (γ * γ)) ∂ν) :
    (lam.map (fun w : ℂ => w - q)).restrict (annulus (-q) (1 / 4) (2 * 1)) =
      ((ν.map (fun w : ℂ => w - q)).restrict (annulus (-q) (1 / 4) (2 * 1))).withDensity
        (fun y => ENNReal.ofReal (‖y + q‖ ^ (γ * γ))) := by
  have hDm : MeasurableSet (annulus (-q) (1 / 4) (2 * 1)) :=
    measurableSet_ball.diff measurableSet_closedBall
  ext s hs
  rw [Measure.restrict_apply hs, withDensity_apply _ hs, Measure.restrict_restrict hs]
  exact translated_regular_eq_integral ν lam γ q hW (s ∩ annulus (-q) (1 / 4) (2 * 1)) (hs.inter hDm)
    Set.inter_subset_right

/-- The two-sided density bounds of the translated singular and regular measures on the annulus `D`, with constants
`k₁ = (2^{γ²})⁻¹` and `k₂ = ((1/4)^{γ²})⁻¹`: `k₁ • lam'|_D ≤ ν'|_D ≤ k₂ • lam'|_D`. -/
theorem translated_density_bounds (ν lam : Measure ℂ) (γ : ℝ) (q : ℂ)
    (hW : ∀ s : Set ℂ, MeasurableSet s → (0 : ℂ) ∉ s →
      lam s = ∫⁻ z in s, ENNReal.ofReal (‖z‖ ^ (γ * γ)) ∂ν) :
    ENNReal.ofReal (((2 : ℝ) ^ (γ * γ))⁻¹) • (lam.map (fun w : ℂ => w - q)).restrict (annulus (-q) (1 / 4) (2 * 1)) ≤
        (ν.map (fun w : ℂ => w - q)).restrict (annulus (-q) (1 / 4) (2 * 1)) ∧
      (ν.map (fun w : ℂ => w - q)).restrict (annulus (-q) (1 / 4) (2 * 1)) ≤
        ENNReal.ofReal ((((1 : ℝ) / 4) ^ (γ * γ))⁻¹) •
          (lam.map (fun w : ℂ => w - q)).restrict (annulus (-q) (1 / 4) (2 * 1)) := by
  set c1 : ℝ := ((1 : ℝ) / 4) ^ (γ * γ) with hc1
  set c2 : ℝ := (2 : ℝ) ^ (γ * γ) with hc2
  have hc1pos : 0 < c1 := Real.rpow_pos_of_pos (by norm_num) _
  have hc2pos : 0 < c2 := Real.rpow_pos_of_pos (by norm_num) _
  have hDm : MeasurableSet (annulus (-q) (1 / 4) (2 * 1)) :=
    measurableSet_ball.diff measurableSet_closedBall
  have hμ := translated_restrict_eq_withDensity ν lam γ q hW
  have hup : ∀ y ∈ annulus (-q) (1 / 4) (2 * 1),
      ENNReal.ofReal c1 ≤ ENNReal.ofReal (‖y + q‖ ^ (γ * γ)) := fun y hy =>
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (by norm_num) (norm_bounds_of_mem_annulus q y hy).1.le
      (mul_self_nonneg γ))
  have hlo : ∀ y ∈ annulus (-q) (1 / 4) (2 * 1),
      ENNReal.ofReal (‖y + q‖ ^ (γ * γ)) ≤ ENNReal.ofReal c2 := fun y hy =>
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) (norm_bounds_of_mem_annulus q y hy).2.le
      (mul_self_nonneg γ))
  have hA := restrict_le_smul_of_density (ν.map (fun w : ℂ => w - q))
    (lam.map (fun w : ℂ => w - q)) (annulus (-q) (1 / 4) (2 * 1)) hDm
    (fun y => ENNReal.ofReal (‖y + q‖ ^ (γ * γ))) (ENNReal.ofReal c2) hμ hlo
  have hB := smul_le_restrict_of_density (ν.map (fun w : ℂ => w - q))
    (lam.map (fun w : ℂ => w - q)) (annulus (-q) (1 / 4) (2 * 1)) hDm
    (fun y => ENNReal.ofReal (‖y + q‖ ^ (γ * γ))) (ENNReal.ofReal c1) hμ hup
  have e1 : ENNReal.ofReal ((c2)⁻¹) * ENNReal.ofReal c2 = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc2pos.le), inv_mul_cancel₀ hc2pos.ne', ENNReal.ofReal_one]
  have e2 : ENNReal.ofReal ((c1)⁻¹) * ENNReal.ofReal c1 = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc1pos.le), inv_mul_cancel₀ hc1pos.ne', ENNReal.ofReal_one]
  constructor
  · calc ENNReal.ofReal ((c2)⁻¹) • (lam.map (fun w : ℂ => w - q)).restrict (annulus (-q) (1 / 4) (2 * 1))
        ≤ ENNReal.ofReal ((c2)⁻¹) • (ENNReal.ofReal c2 •
            (ν.map (fun w : ℂ => w - q)).restrict (annulus (-q) (1 / 4) (2 * 1))) :=
          measure_smul_mono _ hA
      _ = (ENNReal.ofReal ((c2)⁻¹) * ENNReal.ofReal c2) •
            (ν.map (fun w : ℂ => w - q)).restrict (annulus (-q) (1 / 4) (2 * 1)) := smul_smul _ _ _
      _ = (ν.map (fun w : ℂ => w - q)).restrict (annulus (-q) (1 / 4) (2 * 1)) := by rw [e1, one_smul]
  · calc (ν.map (fun w : ℂ => w - q)).restrict (annulus (-q) (1 / 4) (2 * 1))
        = ENNReal.ofReal ((c1)⁻¹) • (ENNReal.ofReal c1 •
            (ν.map (fun w : ℂ => w - q)).restrict (annulus (-q) (1 / 4) (2 * 1))) := by
          rw [smul_smul, e2, one_smul]
      _ ≤ ENNReal.ofReal ((c1)⁻¹) • (lam.map (fun w : ℂ => w - q)).restrict (annulus (-q) (1 / 4) (2 * 1)) :=
          measure_smul_mono _ hB

#print axioms translated_density_bounds
#print axioms phaseVeryGood_iff_isVeryGood_translate

end HarmonicBalls
