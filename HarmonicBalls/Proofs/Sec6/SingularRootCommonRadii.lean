import HarmonicBalls.Proofs.Sec6.SingularUnitDiscCommonRadii
import HarmonicBalls.Proofs.Sec6.SingularRootPolynomialOrigin

/-! # Common good radii for a singular LQG root and a fine-grid centre

The annulus count uses Leonardo Bonanno's iteration in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

/-- A singular LQG root is polynomially unlikely to lie within a fixed
multiple of the square root of the window parameter from the origin. -/
theorem singular_root_away_from_origin_polyHighProb
    (hball : LiouvilleBallMassBoundStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (A : ℝ) (hA : 0 < A) :
    PolyHighProb (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
      (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
      (fun ε => {p | A * Real.sqrt ε ≤ ‖p.2‖}) := by
  obtain ⟨k, hk, D, hD, t₀, ht₀, hnear⟩ :=
    exists_singular_unitDisc_root_origin_polynomial_bound hball hγ hγ2 hα h hμ
  obtain ⟨ε₀, hε₀, hsmall⟩ := exists_pos_forall_rpow_le
    (a := (1 / 2 : ℝ)) (c := t₀ / (2 * A)) (by norm_num) (by positivity)
  refine ⟨(1 / 2 : ℝ) * k, by positivity, D * A ^ k, ε₀, hε₀, ?_⟩
  intro ε hε hε₀'
  have ht : A * Real.sqrt ε < t₀ := by
    have hh := hsmall ε hε hε₀'
    rw [← Real.sqrt_eq_rpow] at hh
    have hh' := (le_div_iff₀ (by positivity : 0 < 2 * A)).mp hh
    nlinarith
  have hn := hnear (A * Real.sqrt ε) (by positivity) ht
  have heq : (univ ×ˢ ball (0 : ℂ) (A * Real.sqrt ε)) =
      {p : Ω × ℂ | ‖p.2‖ < A * Real.sqrt ε} := by
    ext p
    simp only [mem_prod, mem_univ, true_and, mem_ball, dist_zero_right, mem_ofPred_eq]
  rw [heq] at hn
  simp only [compl_ofPred, not_le]
  convert hn using 1
  rw [Real.mul_rpow hA.le (Real.sqrt_nonneg ε), Real.sqrt_eq_rpow,
    ← Real.rpow_mul hε.le]
  ring_nf

/-- With polynomially high probability a normalized singular-mass root and
one nearby fine-grid centre share the same good-annulus radii. -/
theorem exists_singular_root_common_goodAnnulus_fineGrid
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
      ∃ c : ℝ, 0 < c ∧ PolyHighProb
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
    exists_unitDisc_common_singular_goodAnnulus_fineGrid_separated
      hgrowth h hμ hμ₀ hAff hCC hγ hγ2 hα hb β hβ
  refine ⟨a, ha, δ, hδ, ?_⟩
  intro s hs
  obtain ⟨c, hc, hcgrid⟩ := hgrid s hs
  refine ⟨c, hc, ?_⟩
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

end HarmonicBalls.Section6
