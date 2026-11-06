import HarmonicBalls.Proofs.Sec6.SeparatedPrevalenceGrid

/-! # Common singular good-annulus radii in the unit disc

The fine-grid count uses Leonardo Bonanno's annulus iteration in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal
universe u

/-- With polynomially high probability, every sufficiently separated unit-disc
centre has a nearby fine-grid centre sharing the singular good radii.
The separation bound shrinks with the window scale. -/
theorem exists_unitDisc_common_singular_goodAnnulus_fineGrid_separated
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
        ∀ w ∈ ball (0 : ℂ) 1,
        10 * Real.sqrt (c*ε) + 2 * ((c*ε)/100) +
          6*s*ε ^ (3 / 4 : ℝ) ≤ ‖w‖ → ∃ z ∈ prevalenceGrid (c*ε),
        dist w z < δ * (s*ε) ∧
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus (μ ω) (s*r) z
              (a / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) (b/2) ∧
            IsGoodAnnulus (μ ω) (s*r) w
              ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b}.ncard : ℝ)}) := by
  obtain ⟨a, ha, δ, hδ, hgrid⟩ := exists_common_singular_goodAnnulus_fineGrid_shrinkingOrigin
    hgrowth h hμ hμ₀ hAff hCC hγ hγ2 hα hb β hβ
  refine ⟨a, ha, δ, hδ, ?_⟩
  intro s hs
  let c : ℝ := min 1 (25*δ*s)
  have hc : 0 < c := lt_min zero_lt_one (by positivity)
  have hcsmall : c ≤ 25*δ*s := min_le_right _ _
  refine ⟨c, hc, ?_⟩
  apply (hgrid c hc s hs).mono_of_small zero_lt_one
  intro ε hε hεsmall ω hω w hw hsep
  have hR : 0 ≤ 6*s*ε ^ (3 / 4 : ℝ) := by positivity
  obtain ⟨z, hz, hdist, hzlo⟩ := exists_prevalenceGrid_dist_lt_of_separated
    (mul_pos hc hε) hR hw hsep
  have hnear : dist w z < δ*(s*ε) := by
    apply hdist.trans_le
    have := mul_le_mul_of_nonneg_right hcsmall hε.le
    nlinarith
  have hwlo : 6*s*ε ^ (3 / 4 : ℝ) ≤ ‖w‖ := by
    have hsqrt := Real.sqrt_nonneg (c*ε)
    nlinarith
  exact ⟨z, hz, hnear, hω z hz w hzlo hwlo hnear⟩

end HarmonicBalls.Section6
