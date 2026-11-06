import HarmonicBalls.Proofs.Sec6.SingularFineGridCommonRadii

/-! # Common singular good-annulus radii in the middle annulus

The fine-grid count uses Leonardo Bonanno's annulus iteration in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal
universe u

/-- With polynomially high probability, every middle-annulus centre has a
nearby fine-grid centre with the same lower count of singular good radii.
The mesh factor may depend on the physical scale. -/
theorem exists_middleAnnulus_common_singular_goodAnnulus_fineGrid
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s →
      ∃ c : ℝ, 0 < c ∧ PolyHighProb P (fun ε => {ω |
        ∀ w ∈ annulus (0 : ℂ) (1/2) 1, ∃ z ∈ prevalenceGrid (c*ε),
        dist w z < δ * (s*ε) ∧
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus (μ ω) (s*r) z
              (a / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) (b/2) ∧
            IsGoodAnnulus (μ ω) (s*r) w
              ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b}.ncard : ℝ)}) := by
  obtain ⟨a, ha, δ, hδ, hgrid⟩ := exists_common_singular_goodAnnulus_fineGrid_smallTolerance
    hgrowth h hμ hμ₀ hAff hCC hγ hγ2 hα hb β hβ
  refine ⟨a, ha, δ, hδ, ?_⟩
  intro s hs
  let c : ℝ := min 1 (25*δ*s)
  have hc : 0 < c := lt_min zero_lt_one (by positivity)
  have hcsmall : c ≤ 25*δ*s := min_le_right _ _
  refine ⟨c, hc, ?_⟩
  let ε₀ : ℝ := min (1/(10000*c)) (1/(4*δ*s))
  have hε₀ : 0 < ε₀ := lt_min (by positivity) (by positivity)
  apply (hgrid c hc s hs).mono_of_small hε₀
  intro ε hε hεsmall ω hω w hw
  have hsmall : c*ε ≤ 1/10000 := by
    have ht : ε < 1/(10000*c) := hεsmall.trans_le (min_le_left _ _)
    have := (lt_div_iff₀ (show 0 < 10000*c by positivity)).1 ht
    nlinarith
  obtain ⟨z, hz, hdist⟩ := exists_prevalenceGrid_dist_lt (mul_pos hc hε) hsmall hw
  have hnear : dist w z < δ*(s*ε) := by
    apply hdist.trans_le
    have := mul_le_mul_of_nonneg_right hcsmall hε.le
    nlinarith
  have hwlo : (1/2 : ℝ) < ‖w‖ := by
    have hw' : ¬ dist w 0 ≤ (1/2 : ℝ) := hw.2
    simpa [dist_eq_norm] using (lt_of_not_ge hw')
  have hnear' : dist w z < 1/4 := by
    apply hnear.trans
    have ht : ε < 1/(4*δ*s) := hεsmall.trans_le (min_le_right _ _)
    have := (lt_div_iff₀ (show 0 < 4*δ*s by positivity)).1 ht
    nlinarith
  have hzlo : (1/4 : ℝ) ≤ ‖z‖ := by
    have ht := dist_triangle w z (0 : ℂ)
    simp only [dist_zero_right] at ht
    linarith
  exact ⟨z, hz, hnear, hω z hz w hzlo (by linarith) hnear⟩

end HarmonicBalls.Section6
