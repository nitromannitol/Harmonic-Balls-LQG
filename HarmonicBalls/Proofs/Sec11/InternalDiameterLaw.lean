import HarmonicBalls.Steps.Sec11.InternalDiameterDecoder
import HarmonicBalls.Steps.Sec11.NormalizedDiameterDilation
import HarmonicBalls.Steps.Sec11.ExactScalePunctureCriterion
import HarmonicBalls.Proofs.Sec11.LQGBaseMetricObservable

/-! # Universality and scaling of internal-diameter moments

The fixed-domain internal diameter is a common measurable observable of the
base metric, and hence has the same law for any two whole-plane GFFs.
-/

namespace HarmonicBalls

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- The internal diameter of the base LQG metric has a realization-independent
law for fixed sets inside an open domain. -/
theorem IsWholePlaneGFF.identDistrib_baseMetric_internalDiameter
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc')
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {U K : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U) :
    IdentDistrib (fun ω => ⨆ x ∈ K, ⨆ y ∈ K, internalMetric (𝔇 (hC ω)) U x y)
      (fun ω => ⨆ x ∈ K, ⨆ y ∈ K, internalMetric (𝔇 (hC' ω)) U x y) P P' := by
  obtain ⟨F, hF, hF_eq⟩ := exists_measurable_internalDiameter_decoder hU hKU
  obtain ⟨G, hG, hG_eq⟩ := h𝔇.exists_common_continuous_observable
  have hzero (T : (ℂ → ℝ) → ℝ) : addFunPairing T (fun _ => 0) = T := by
    funext φ
    simp [addFunPairing]
  have hm := (h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) h
    (by intro ω; fun_prop) (by intro x; fun_prop)).ae_isEuclideanLengthMetric
  have hm' := (h𝔇.satisfiesLQGMetricAxioms Ω' P' hC' hcirc' (fun _ _ => 0) h'
    (by intro ω; fun_prop) (by intro x; fun_prop)).ae_isEuclideanLengthMetric
  simp only [hzero] at hm hm'
  let O : (GFFObservable.Admissible → ℝ) → ℝ≥0∞ := F ∘ G
  have hd := (h.identDistrib_observables_across_spaces h').comp (hF.comp hG)
  have heq : ∀ᵐ ω ∂P,
      O (fun o => o.1.eval (hC ω) (hcirc ω)) =
        ⨆ x ∈ K, ⨆ y ∈ K, internalMetric (𝔇 (hC ω)) U x y := by
    filter_upwards [hm] with ω hω
    change F (G (fun o => o.1.eval (hC ω) (hcirc ω))) = _
    rw [hG_eq _ _ hω.continuous_pair]
    exact hF_eq ⟨fun p => 𝔇 (hC ω) p.1 p.2, hω.continuous_pair⟩ hω
  have heq' : ∀ᵐ ω ∂P',
      O (fun o => o.1.eval (hC' ω) (hcirc' ω)) =
        ⨆ x ∈ K, ⨆ y ∈ K, internalMetric (𝔇 (hC' ω)) U x y := by
    filter_upwards [hm'] with ω hω
    change F (G (fun o => o.1.eval (hC' ω) (hcirc' ω))) = _
    rw [hG_eq _ _ hω.continuous_pair]
    exact hF_eq ⟨fun p => 𝔇 (hC' ω) p.1 p.2, hω.continuous_pair⟩ hω
  exact ((IdentDistrib.of_ae_eq hd.aemeasurable_fst heq).symm.trans hd).trans
    (IdentDistrib.of_ae_eq hd.aemeasurable_snd heq')

/-- Exact-power normalized diameters at every positive scale have the same
first moment as the fixed-domain diameter of the original base metric. -/
theorem IsWholePlaneGFF.lintegral_scaledCompactInternalDiameter_eq
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {U K : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U) {r : ℝ} (hr : 0 < r) :
    (∫⁻ ω, scaledCompactInternalDiameter (fun ω => 𝔇 (hC ω)) hcirc ξ K U r
      (ENNReal.ofReal (r ^ (ξ * lqgQ γ))) ω ∂P) =
      ∫⁻ ω, ⨆ x ∈ K, ⨆ y ∈ K, internalMetric (𝔇 (hC ω)) U x y ∂P := by
  have haff : IsWholePlaneGFF P (affinePairing hC hcirc (r : ℂ) 0)
      (affineCircle hcirc (r : ℂ) 0) :=
    hAff h (r : ℂ) (by exact_mod_cast hr.ne') 0
  calc
    _ = ∫⁻ ω, ⨆ x ∈ K, ⨆ y ∈ K,
        internalMetric (𝔇 (affinePairing hC hcirc (r : ℂ) 0 ω)) U x y ∂P :=
      lintegral_congr_ae (h.ae_scaledCompactInternalDiameter_eq_affine hAff 𝔇 h𝔇 K U hr)
    _ = _ := (haff.identDistrib_baseMetric_internalDiameter h 𝔇 h𝔇 hU hKU).lintegral_eq

/-- Puncture removal reduces to finiteness of fixed-scale compact internal
first moments, with no uniformity assumption over small scales. -/
theorem IsWholePlaneGFF.exists_puncture_criterion_of_fixed_diameter_moments
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (E : Ω → ℂ → ℂ → ℝ) (s α : ℝ)
    (hs : 0 ≤ s) (hξ : 0 < ξ) (hα : 0 ≤ α) (hαQ : α < lqgQ γ)
    (V : Set ℂ) (hball : Metric.ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V)
    (hmeasD : ∀ x y, Measurable fun ω => 𝔇 (hC ω) x y)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hDnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ 𝔇 (hC ω) x y)
    (hEnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ E ω x y)
    (hzero : ∀ᵐ ω ∂P, ∀ x y,
      weylScaling (𝔇 (hC ω)) ξ 0 x y = ENNReal.ofReal (𝔇 (hC ω) x y))
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y) :
    ∃ (ε : ℝ) (N : ℕ) (c : ℕ → ℂ), 0 < ε ∧
      ((∀ i, i ≤ N → (∫⁻ ω, ⨆ x ∈ Metric.closedBall (c i) ε,
        ⨆ y ∈ Metric.closedBall (c i) ε,
          internalMetric (𝔇 (hC ω)) (Metric.ball (c i) (2 * ε)) x y ∂P) ≠ ∞) →
        ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
          internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y) := by
  obtain ⟨ε, N, c, hε, hcriterion⟩ :=
    exists_scaled_ball_criterion_of_exact_scale_moments P hC hcirc h (fun ω => 𝔇 (hC ω)) E
      s γ ξ α hs hξ hα hαQ V hball hmeasD hD hE hDnonneg hEnonneg hzero hscale
  refine ⟨ε, N, c, hε, ?_⟩
  intro hmom
  apply hcriterion
  intro i hi
  refine ⟨∫⁻ ω, ⨆ x ∈ Metric.closedBall (c i) ε,
    ⨆ y ∈ Metric.closedBall (c i) ε,
      internalMetric (𝔇 (hC ω)) (Metric.ball (c i) (2 * ε)) x y ∂P, hmom i hi, ?_⟩
  intro n
  exact (h.lintegral_scaledCompactInternalDiameter_eq hAff 𝔇 h𝔇 Metric.isOpen_ball
    (closedBall_compact_connected_subset_double (c i) hε).2.2.1
    (r := Real.exp (-(s + n))) (Real.exp_pos _)).le


end HarmonicBalls
