import HarmonicBalls.Proofs.Sec6.SingularRootCommonRadii
import HarmonicBalls.Proofs.Sec6.CommonWindowCount

/-! # A bounded fine-grid coefficient for singular roots

The annulus count uses Leonardo Bonanno's iteration in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

/-- With polynomially high probability, every sufficiently separated unit-disc
centre has a nearby fine-grid centre sharing the singular good radii.
The separation bound shrinks with the window scale. -/
theorem exists_unitDisc_common_singular_goodAnnulus_fineGrid_le_one
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
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ PolyHighProb P (fun ε => {ω |
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
  refine ⟨c, hc, min_le_left _ _, ?_⟩
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


/-- With polynomially high probability a normalized singular-mass root and
one nearby fine-grid centre share the same good-annulus radii. -/
theorem exists_singular_root_common_goodAnnulus_fineGrid_le_one
    (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s →
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ PolyHighProb
        (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
          (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        (fun ε => {p | ∃ z ∈ prevalenceGrid (c*ε),
          dist p.2 z < δ * (s*ε) ∧
          (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
            ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
              (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
              IsGoodAnnulus (μ p.1) (s*r) z
                (a / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) (b/2) ∧
              IsGoodAnnulus (μ p.1) (s*r) p.2
                ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b}.ncard : ℝ)}) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  let hgrowth := lqgVolumeGrowthAllScalesStmt_of_ballMass hball
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ α hγ hγ2 hα
    Ω P hC hcirc μ h hμ
  have hmass : ∀ᵐ ω ∂P, ((μ ω).withDensity (fun _ => 1)) (ball 0 1) ≠ 0 ∧
      ((μ ω).withDensity (fun _ => 1)) (ball 0 1) ≠ ∞ := by
    filter_upwards [hfull, hμ] with ω hf hloc
    let : IsLocallyFiniteMeasure (μ ω) := hloc.isLocallyFiniteMeasure
    simpa only [withDensity_const, one_smul] using
      (show μ ω (ball 0 1) ≠ 0 ∧ μ ω (ball 0 1) ≠ ∞ from
        ⟨(hf _ isOpen_ball ⟨0, mem_ball_self (by norm_num)⟩).ne', measure_ball_ne_top⟩)
  have hp := measurePreserving_fst_weightedRestriction_compProd P μ
    (h.aemeasurable_lqgMeasure hμ) (ball 0 1) measurableSet_ball
    (fun _ => 1) measurable_const hmass
  obtain ⟨a, ha, δ, hδ, hgrid⟩ :=
    exists_unitDisc_common_singular_goodAnnulus_fineGrid_le_one
      hgrowth h hμ hμ₀ hAff hCC hγ hγ2 hα hb β hβ
  refine ⟨a, ha, δ, hδ, ?_⟩
  intro s hs
  obtain ⟨c, hc, hc1, hcgrid⟩ := hgrid s hs
  refine ⟨c, hc, hc1, ?_⟩
  let A : ℝ := 10 * Real.sqrt c + c + 6*s + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hfield := polyHighProb_preimage_of_measurePreserving Prod.fst hp _ hcgrid
  have horigin := singular_root_away_from_origin_polyHighProb hball hγ hγ2 hα h hμ A hA
  have hroot := ae_mem_weightedRestriction_compProd P μ (h.aemeasurable_lqgMeasure hμ)
    (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const
  apply ((hfield.inter horigin).inter_ae hroot).mono_of_small zero_lt_one
  intro ε hε hε1 p hp'
  have hsq : ε ≤ Real.sqrt ε := by
    rw [Real.sqrt_eq_rpow]
    nth_rw 1 [← Real.rpow_one ε]
    exact Real.rpow_le_rpow_of_exponent_ge hε hε1.le (by norm_num)
  have hpow : ε ^ (3 / 4 : ℝ) ≤ Real.sqrt ε := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hε hε1.le (by norm_num)
  have hsep : 10 * Real.sqrt (c*ε) + 2*((c*ε)/100) +
      6*s*ε ^ (3 / 4 : ℝ) ≤ ‖p.2‖ := by
    rw [Real.sqrt_mul hc.le]
    have hsq0 := Real.sqrt_nonneg ε
    have h₁ := mul_le_mul_of_nonneg_left hsq hc.le
    have h₂ := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 6*s)
    have haway : (10 * Real.sqrt c + c + 6*s + 1) * Real.sqrt ε ≤ ‖p.2‖ := hp'.1.2
    have hce : 0 ≤ c * ε := by positivity
    nlinarith [haway]
  exact hp'.1.1 p.2 hp'.2 hsep


/-- At every positive physical scale, a normalized singular root and a
nearby centre on the prescribed grid share a logarithmic count of good radii
in the square-root window. The displacement constant may depend on the scale. -/
theorem exists_singular_root_common_goodAnnulus_prescribedGrid
    (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s →
      ∃ C : ℝ, 1 ≤ C ∧ PolyHighProb
        (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
          (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        (fun ε => {p | ∃ z ∈ prevalenceGrid ε,
          dist p.2 z < δ * (s*(C*ε)) ∧
          (β / 16) * Real.logb 7 (ε ^ (-(1 / 2 : ℝ))) ≤
            ({r : ℝ | r ∈ Icc ε (Real.sqrt ε) ∧
              (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
              IsGoodAnnulus (μ p.1) (s*r) z
                (a / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) (b/2) ∧
              IsGoodAnnulus (μ p.1) (s*r) p.2
                ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b}.ncard : ℝ)}) := by
  obtain ⟨a, ha, δ, hδ, hroot⟩ :=
    exists_singular_root_common_goodAnnulus_fineGrid_le_one
      hball h hμ hμ₀ hAff hCC hγ hγ2 hα hb β hβ
  refine ⟨a, ha, δ, hδ, ?_⟩
  intro s hs
  obtain ⟨c, hc, hc1, hprob⟩ := hroot s hs
  have hC : 1 ≤ c⁻¹ := (one_le_inv₀ hc).2 hc1
  obtain ⟨η, hη, hwindows⟩ := eventually_mul_window_inside_sqrt hC
  refine ⟨c⁻¹, hC, ?_⟩
  apply (hprob.comp_mul (inv_pos.mpr hc)).mono_of_small hη
  intro ε hε hεη p hp
  obtain ⟨z, hz, hdist, hcount⟩ := hp
  have hgrid : c * (c⁻¹ * ε) = ε := by rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  have hw := hwindows ε hε hεη
  refine ⟨z, ?_, hdist, ?_⟩
  · simpa only [hgrid] using hz
  · exact common_count_wider_window (div_nonneg hβ.1.le (by norm_num)) hε
      (mul_pos (inv_pos.mpr hc) hε) hw.1 hw.2.1 hw.2.2 hcount

end HarmonicBalls.Section6
