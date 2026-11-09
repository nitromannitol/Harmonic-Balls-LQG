import HarmonicBalls.FirstPass.S8d.DensityComparison
import HarmonicBalls.Defs.Annuli

/-! # FIRST-PASS helper (fp-S8d, owner n4): comparison of the very-good criteria under a density

Let `lam` be the regular measure and `μ` the singular one of the same field, and suppose that on the annulus
`D = 𝔸_{ρ/4,2ρ}(x₀)` the restrictions satisfy `c₁ • lam|_D ≤ μ|_D ≤ c₂ • lam|_D`
(`DensityComparison.lean`). Every set in the very-good criteria at scale `ρ` lies in `D`: the balls
`B(z, r)` with `z ∈ 𝔸_{ρ/2,ρ}(x₀)` and `r < ρ/4`, and the annuli `𝔸(w,3r,5r)` used by the good-annulus event.
This file gives the comparison of the annulus-ball mass size `annulusBallMassSize` (Defs/Annuli.lean) and of the mass
ratio of Defs/Annuli.lean `IsVeryGoodAnnulus` (VG-i). The Green potential (VG-ii), the good-annulus event and the
count (VG-iii) are in the next step. No new mathematics: the ingredients are set inclusions, the definition of
`withDensity`, and monotonicity of infima and quotients in `ℝ≥0∞`. -/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

/-- A quotient lies in a closed interval with positive finite endpoints iff the numerator is comparable with the
denominator: `x / y ∈ [a, b]` iff `a * y ≤ x ≤ b * y`, for `0 < y < ∞`. -/
theorem div_mem_Icc_iff_mul (x y a b : ℝ≥0∞) (hy0 : y ≠ 0) (hyT : y ≠ ∞) :
    x / y ∈ Icc a b ↔ a * y ≤ x ∧ x ≤ b * y := by
  rw [Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(ENNReal.le_div_iff_mul_le (Or.inl hy0) (Or.inl hyT)).1 h1,
      (ENNReal.div_le_iff hy0 hyT).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(ENNReal.le_div_iff_mul_le (Or.inl hy0) (Or.inl hyT)).2 h1,
      (ENNReal.div_le_iff hy0 hyT).2 h2⟩

/-- If `x / y` lies in `[ofReal a, ofReal b]` with `0 < a`, then `0 < y < ∞`. -/
theorem denom_pos_finite_of_mem_Icc (x y : ℝ≥0∞) (a b : ℝ) (ha : 0 < a)
    (h : x / y ∈ Icc (ENNReal.ofReal a) (ENNReal.ofReal b)) : y ≠ 0 ∧ y ≠ ∞ := by
  rw [Set.mem_Icc] at h
  have hapos : (0 : ℝ≥0∞) < ENNReal.ofReal a := ENNReal.ofReal_pos.2 ha
  constructor
  · intro hy
    rw [hy] at h
    rcases eq_or_ne x 0 with hx | hx
    · rw [hx, ENNReal.zero_div] at h
      exact absurd h.1 (not_le.2 hapos)
    · rw [ENNReal.div_zero hx] at h
      exact absurd (top_le_iff.1 h.2) (ENNReal.ofReal_lt_top.ne)
  · intro hy
    rw [hy, ENNReal.div_top] at h
    exact absurd h.1 (not_le.2 hapos)

/-- Restricted comparison of measures on sets inside the annulus `D`: the two-sided bound
`c₁ * lam s ≤ μ s ≤ c₂ * lam s` for measurable `s ⊆ D`, from `c₁ • lam|_D ≤ μ|_D ≤ c₂ • lam|_D`. -/
theorem set_bounds_of_restrict (lam μ : Measure ℂ) (D : Set ℂ) (c₁ c₂ : ℝ≥0∞)
    (hlow : c₁ • lam.restrict D ≤ μ.restrict D) (hup : μ.restrict D ≤ c₂ • lam.restrict D)
    (s : Set ℂ) (hs : MeasurableSet s) (hsD : s ⊆ D) :
    c₁ * lam s ≤ μ s ∧ μ s ≤ c₂ * lam s := by
  have h1 := (Measure.le_iff.1 hlow) s hs
  have h2 := (Measure.le_iff.1 hup) s hs
  simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs,
    Set.inter_eq_left.2 hsD] at h1 h2
  exact ⟨h1, h2⟩

/-- Every ball `B(z, r)` with `z` in the outer annulus `𝔸_{ρ/2,ρ}(x₀)` and `r < ρ/4` lies in the annulus
`𝔸_{ρ/4,2ρ}(x₀)` (the set `D` of the density comparison). -/
theorem ball_subset_annulus_of_mem (x₀ z : ℂ) (ρ r : ℝ) (hz : z ∈ annulus x₀ (ρ / 2) ρ) (hr : r < ρ / 4) :
    ball z r ⊆ annulus x₀ (ρ / 4) (2 * ρ) := by
  intro w hw
  simp only [annulus, Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le] at hz hw ⊢
  obtain ⟨hz1, hz2⟩ := hz
  have t1 := dist_triangle w z x₀
  have t2 := dist_triangle z w x₀
  have t3 := dist_comm w z
  constructor <;> linarith

/-- The annulus-ball mass size is comparable with the one of the regular measure, with the constants of the density
comparison: `c₁ · M(lam) ≤ M(μ) ≤ c₂ · M(lam)` (VG-i numerator). -/
theorem annulusBallMassSize_comparable (lam μ : Measure ℂ) (x₀ : ℂ) (ρ βminus : ℝ) (c₁ c₂ : ℝ≥0∞)
    (hc₁ : c₁ ≠ 0) (hc₁' : c₁ ≠ ∞) (hc₂ : c₂ ≠ 0) (hc₂' : c₂ ≠ ∞)
    (hbd : ∀ s : Set ℂ, MeasurableSet s → s ⊆ annulus x₀ (ρ / 4) (2 * ρ) →
      c₁ * lam s ≤ μ s ∧ μ s ≤ c₂ * lam s) :
    c₁ * annulusBallMassSize lam βminus ρ x₀ ≤ annulusBallMassSize μ βminus ρ x₀ ∧
      annulusBallMassSize μ βminus ρ x₀ ≤ c₂ * annulusBallMassSize lam βminus ρ x₀ := by
  unfold annulusBallMassSize
  constructor
  · simp only [ENNReal.mul_iInf_of_ne hc₁ hc₁']
    refine iInf_mono fun z => iInf_mono fun hz => iInf_mono fun r => iInf_mono fun hr => ?_
    rw [← mul_div_assoc]
    exact ENNReal.div_le_div_right
      (hbd (ball z r) measurableSet_ball (ball_subset_annulus_of_mem x₀ z ρ r hz hr.2)).1 _
  · simp only [ENNReal.mul_iInf_of_ne hc₂ hc₂']
    refine iInf_mono fun z => iInf_mono fun hz => iInf_mono fun r => iInf_mono fun hr => ?_
    rw [← mul_div_assoc]
    exact ENNReal.div_le_div_right
      (hbd (ball z r) measurableSet_ball (ball_subset_annulus_of_mem x₀ z ρ r hz hr.2)).2 _

#print axioms annulusBallMassSize_comparable

end HarmonicBalls
