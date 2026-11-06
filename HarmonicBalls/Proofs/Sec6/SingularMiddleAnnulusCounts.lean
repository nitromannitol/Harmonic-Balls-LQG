import HarmonicBalls.Proofs.Sec6.FineGridNearbyCounts
import HarmonicBalls.Proofs.Sec6.SingularRootSeparatedTail
import HarmonicBalls.Proofs.Sec6.LocalizedSingularRootNormalization

/-! # Simultaneous singular good-annulus counts in a middle annulus

The zero-strength count uses Leonardo Bonanno's annulus iteration in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

/-- At every centre in the middle annulus, singular LQG has a positive
fraction of good scales with polynomially high probability. The exponent
and small-scale threshold may depend on the physical scale. -/
theorem exists_all_middleAnnulus_singular_goodAnnulus_counts
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
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ, 0 < s →
      PolyHighProb P (fun ε => {ω | ∀ w ∈ annulus (0 : ℂ) (1/2) 1,
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus (μ ω) (s*r) w
              ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) (b+1)}.ncard : ℝ)}) := by
  obtain ⟨a, ha, hgrid⟩ := exists_all_middleAnnulus_goodAnnulus_counts
    hgrowth h hμ₀ hAff hCC hγ hγ2 hb β hβ
  refine ⟨a, ha, ?_⟩
  intro s hs
  obtain ⟨ε₀, hε₀, hsmall⟩ := exists_pos_forall_rpow_le
    (a := (3/4 : ℝ)) (c := 1 / (12*s)) (by norm_num) (by positivity)
  have hweight := ae_singular_lqg_eq_power_weight hgrowth hγ hγ2 hα h hμ hμ₀
  apply ((hgrid s hs).inter_ae hweight).mono_of_small hε₀
  intro ε hε hε₀' ω hω w hw
  have hwlo : (1/2 : ℝ) < ‖w‖ := by
    have hw' : ¬ dist w 0 ≤ (1/2 : ℝ) := hw.2
    simpa [dist_eq_norm] using (lt_of_not_ge hw')
  have hsep : 6*s*ε ^ (3/4 : ℝ) ≤ (1/2 : ℝ) := by
    have hs' := hsmall ε hε hε₀'
    have hmul := mul_le_mul_of_nonneg_left hs' (show 0 ≤ 6*s by positivity)
    have heq : 6*s*(1/(12*s)) = (1/2 : ℝ) := by field_simp; norm_num
    linarith
  apply (hω.1 w hw).trans
  norm_cast
  apply Set.ncard_le_ncard ?_ ?_
  · intro r hr
    refine ⟨hr.1, hr.2.1, ?_⟩
    have hrpos : 0 < s*r := mul_pos hs (hε.trans_le hr.1.1)
    have hdist : 6*(s*r) ≤ ‖w‖ := by
      have h := mul_le_mul_of_nonneg_left hr.1.2 (show 0 ≤ 6*s by positivity)
      nlinarith
    apply isGoodAnnulus_of_singular_weight hrpos
      (annulus_separated_of_six_mul_le_norm hrpos hdist) ?_ hr.2.2
    rw [hω.2]
  · apply finite_of_geometric (q := (7 : ℝ)⁻¹) (A := 1) (lo := ε)
      (by norm_num) (by norm_num) hε
    intro r hr
    obtain ⟨n, hn⟩ := hr.2.1
    exact ⟨hr.1.1, n, by simpa using hn⟩


/-- Projection along a measure-preserving map preserves polynomially high
probability, including events for which measurability has not been shown. -/
theorem polyHighProb_preimage_of_measurePreserving
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {Q : Measure X} {P : Measure Y} (f : X → Y) (hf : MeasurePreserving f Q P)
    (E : ℝ → Set Y) (hE : PolyHighProb P E) :
    PolyHighProb Q (fun ε => f ⁻¹' E ε) := by
  obtain ⟨q, hq, C, ε₀, hε₀, htail⟩ := hE
  refine ⟨q, hq, C, ε₀, hε₀, ?_⟩
  intro ε hε hε₀'
  calc
    Q (f ⁻¹' E ε)ᶜ ≤ Q (f ⁻¹' (toMeasurable P (E ε)ᶜ)) :=
      measure_mono (preimage_mono (subset_toMeasurable P (E ε)ᶜ))
    _ = P (toMeasurable P (E ε)ᶜ) :=
      hf.measure_preimage (measurableSet_toMeasurable P (E ε)ᶜ).nullMeasurableSet
    _ = P (E ε)ᶜ := measure_toMeasurable (μ := P) (E ε)ᶜ
    _ ≤ ENNReal.ofReal (C * ε ^ q) := htail ε hε hε₀'

/-- The simultaneous singular count also holds under the actual normalized
singular-mass root law on the middle annulus. It applies to every centre,
including the sampled root, without a rooted-field recentering identity. -/
theorem exists_rooted_middleAnnulus_singular_goodAnnulus_counts
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
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ, 0 < s →
      PolyHighProb (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (annulus 0 (1/2) 1) (measurableSet_ball.diff measurableSet_closedBall)
        (fun _ => 1) measurable_const)
      (fun ε => {p | ∀ w ∈ annulus (0 : ℂ) (1/2) 1,
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus (μ p.1) (s*r) w
              ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) (b+1)}.ncard : ℝ)}) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  obtain ⟨a, ha, hcounts⟩ := exists_all_middleAnnulus_singular_goodAnnulus_counts
    hgrowth h hμ hμ₀ hAff hCC hγ hγ2 hα hb β hβ
  refine ⟨a, ha, ?_⟩
  intro s hs
  exact polyHighProb_preimage_of_measurePreserving Prod.fst
    (measurePreserving_fst_singular_lqg_middle_annulus hgrowth hγ hγ2 hα h hμ 0
      (show 0 < (1 : ℝ) by norm_num)) _ (hcounts s hs)


/-- A root sampled from normalized singular mass on the middle annulus
inherits the singular good-annulus count with polynomially high probability. -/
theorem exists_middleAnnulus_singular_root_goodAnnulus_counts
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
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ, 0 < s →
      PolyHighProb (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (annulus 0 (1/2) 1) (measurableSet_ball.diff measurableSet_closedBall)
        (fun _ => 1) measurable_const)
      (fun ε => {p |
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus (μ p.1) (s*r) p.2
              ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) (b+1)}.ncard : ℝ)}) := by
  obtain ⟨a, ha, hcounts⟩ := exists_rooted_middleAnnulus_singular_goodAnnulus_counts
    hgrowth h hμ hμ₀ hAff hCC hγ hγ2 hα hb β hβ
  refine ⟨a, ha, ?_⟩
  intro s hs
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hroot := ae_mem_weightedRestriction_compProd P μ (h.aemeasurable_lqgMeasure hμ)
    (annulus (0 : ℂ) ((1 : ℝ)/2) 1) (measurableSet_ball.diff measurableSet_closedBall)
    (fun _ => 1) measurable_const
  exact ((hcounts s hs).inter_ae hroot).mono fun ε p hp => hp.1 p.2 hp.2

end HarmonicBalls.Section6
