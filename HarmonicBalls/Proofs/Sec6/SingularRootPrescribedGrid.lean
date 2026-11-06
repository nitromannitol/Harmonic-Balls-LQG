import HarmonicBalls.Proofs.Sec6.SingularRootCommonRadii

/-! # Prescribed-grid common radii at singular roots

The annulus count uses Leonardo Bonanno's iteration in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

/-- At physical scales large enough for the displacement budget, a sampled
singular root and a nearby centre on the prescribed grid share good radii. -/
theorem exists_singular_root_common_goodAnnulus_prescribedGrid_largeScale
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
      1 ≤ 25*δ*s → PolyHighProb
        (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
          (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        (fun ε => {p | ∃ z ∈ prevalenceGrid ε,
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
    exists_common_singular_goodAnnulus_fineGrid_shrinkingOrigin
      hgrowth h hμ hμ₀ hAff hCC hγ hγ2 hα hb β hβ
  refine ⟨a, ha, δ, hδ, ?_⟩
  intro s hs hslarge
  have hfield := polyHighProb_preimage_of_measurePreserving Prod.fst hp _
    (hgrid 1 one_pos s hs)
  let A : ℝ := 12 + 6*s
  have hA : 0 < A := by dsimp [A]; positivity
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
  have hsep : 10 * Real.sqrt ε + 2*(ε/100) +
      6*s*ε ^ (3 / 4 : ℝ) ≤ ‖p.2‖ := by
    have hsq0 := Real.sqrt_nonneg ε
    have h₂ := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 6*s)
    have haway : (12 + 6*s) * Real.sqrt ε ≤ ‖p.2‖ := hp'.1.2
    nlinarith
  have hR : 0 ≤ 6*s*ε ^ (3 / 4 : ℝ) := by positivity
  obtain ⟨z, hz, hdist, hzlo⟩ := exists_prevalenceGrid_dist_lt_of_separated
    hε hR hp'.2 hsep
  have hnear : dist p.2 z < δ*(s*ε) := by
    apply hdist.trans_le
    have hh := mul_le_mul_of_nonneg_right hslarge hε.le
    nlinarith
  have hwlo : 6*s*ε ^ (3 / 4 : ℝ) ≤ ‖p.2‖ := by
    have hsqrt := Real.sqrt_nonneg ε
    nlinarith
  refine ⟨z, hz, hnear, ?_⟩
  simpa only [one_mul] using hp'.1.1 z (by simpa only [one_mul] using hz) p.2 hzlo hwlo hnear

end HarmonicBalls.Section6
