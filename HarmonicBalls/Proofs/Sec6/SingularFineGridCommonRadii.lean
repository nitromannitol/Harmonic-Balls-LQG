import HarmonicBalls.Proofs.Sec6.FineGridCommonRadii
import HarmonicBalls.Proofs.Sec6.SingularMiddleAnnulusSmallTolerance

/-! # Common nearby-centre radii for singular LQG

The fine-grid count uses Leonardo Bonanno's annulus iteration in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal
universe u

/-- Away from the singularity, singular LQG has a common good-annulus count
at a fine-grid centre and every sufficiently nearby separated centre. -/
theorem exists_common_singular_goodAnnulus_fineGrid_smallTolerance
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
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧ ∀ c : ℝ, 0 < c → ∀ s : ℝ, 0 < s →
      PolyHighProb P (fun ε => {ω | ∀ z ∈ prevalenceGrid (c*ε), ∀ w : ℂ,
        (1/4 : ℝ) ≤ ‖z‖ → (1/4 : ℝ) ≤ ‖w‖ → dist w z < δ * (s*ε) →
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus (μ ω) (s*r) z
              (a / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) (b/2) ∧
            IsGoodAnnulus (μ ω) (s*r) w
              ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b}.ncard : ℝ)}) := by
  obtain ⟨a, ha, δ, hδ, hgrid⟩ := exists_common_goodAnnulus_fineGrid_smallTolerance
    hgrowth h hμ₀ hAff hCC hγ hγ2 hb β hβ
  refine ⟨a, ha, δ, hδ, ?_⟩
  intro c hc s hs
  obtain ⟨ε₀, hε₀, hsmall⟩ := exists_pos_forall_rpow_le
    (a := (3/4 : ℝ)) (c := 1 / (24*s)) (by norm_num) (by positivity)
  have hweight := ae_singular_lqg_eq_power_weight hgrowth hγ hγ2 hα h hμ hμ₀
  apply ((hgrid c hc s hs).inter_ae hweight).mono_of_small hε₀
  intro ε hε hε₀' ω hω z hz w hzlo hwlo hw
  have hsep : 6*s*ε ^ (3/4 : ℝ) ≤ (1/4 : ℝ) := by
    have hs' := hsmall ε hε hε₀'
    have hmul := mul_le_mul_of_nonneg_left hs' (show 0 ≤ 6*s by positivity)
    have heq : 6*s*(1/(24*s)) = (1/4 : ℝ) := by field_simp; norm_num
    linarith
  apply (hω.1 z hz w hw).trans
  norm_cast
  apply Set.ncard_le_ncard ?_ ?_
  · intro r hr
    refine ⟨hr.1, hr.2.1, ?_⟩
    have hrpos : 0 < s*r := mul_pos hs (hε.trans_le hr.1.1)
    have hdist : 6*(s*r) ≤ (1/4 : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hr.1.2 (show 0 ≤ 6*s by positivity)
      nlinarith
    constructor
    · apply isGoodAnnulus_of_singular_weight hrpos
        (annulus_separated_of_six_mul_le_norm hrpos (hdist.trans hzlo)) ?_ hr.2.2.1
      rw [hω.2]
    · apply isGoodAnnulus_of_singular_weight hrpos
        (annulus_separated_of_six_mul_le_norm hrpos (hdist.trans hwlo)) ?_ hr.2.2.2
      rw [hω.2]
  · apply finite_of_geometric (q := (7 : ℝ)⁻¹) (A := 1) (lo := ε)
      (by norm_num) (by norm_num) hε
    intro r hr
    obtain ⟨n, hn⟩ := hr.2.1
    exact ⟨hr.1.1, n, by simpa using hn⟩

end HarmonicBalls.Section6
