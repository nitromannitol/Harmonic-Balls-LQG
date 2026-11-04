import HarmonicBalls.Proofs.Sec11.LQGNormalizedJointDilation
import HarmonicBalls.Proofs.Sec11.PinchStationaritySourceMetric

/-! # Pinch-indicator stationarity from normalized LQG dilation -/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

/-- The positive mixture of a GFF and its normalized affine image supplies
its original singular metric's length property. The mixture metric-field
hypothesis is staged and remains pending source checking. -/
theorem IsWholePlaneGFF.ae_lengthMetric_of_affine_mixture
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → C(ℂ × ℂ, ℝ)}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ)
    {k : ℝ} (hk : 0 < k)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω (u, v) ∧
      ENNReal.ofReal (D ω (u, v)) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (haxioms : LQGMetricFieldAxioms (mixMeasure.prod (P.prod P)) γ ξ α
      (fun x => if x.1 = 0 then hC x.2.1 else affinePairing hC hcirc (k : ℂ) 0 x.2.2)
      (fun x => if x.1 = 0 then hcirc x.2.1 else affineCircle hcirc (k : ℂ) 0 x.2.2)) :
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y => D ω (x, y)) := by
  let _ := h.isProbabilityMeasure
  have haff : IsWholePlaneGFF P (affinePairing hC hcirc (k : ℂ) 0)
      (affineCircle hcirc (k : ℂ) 0) :=
    hAff h (k : ℂ) (by exact_mod_cast hk.ne') 0
  let H : ℕ → Ω × Ω → (ℂ → ℝ) → ℝ := fun j x =>
    if j = 0 then hC x.1 else affinePairing hC hcirc (k : ℂ) 0 x.2
  let C : ℕ → Ω × Ω → ℝ → ℂ → ℝ := fun j x =>
    if j = 0 then hcirc x.1 else affineCircle hcirc (k : ℂ) 0 x.2
  have hg : ∀ j, IsWholePlaneGFF (P.prod P) (H j) (C j) := by
    intro j
    by_cases hj : j = 0
    · simpa only [H, C, hj, ite_true, Function.comp_def] using
        h.comp_measurePreserving (measurePreserving_fst (μ := P) (ν := P))
    · simpa only [H, C, hj, ite_false, Function.comp_def] using
        haff.comp_measurePreserving (measurePreserving_snd (μ := P) (ν := P))
  have hm := wholePlaneGFFMixtureStep_holds (Ω × Ω) (P.prod P) H C mixMeasure inferInstance hg
  have hlen := (haxioms hm hγ hγ₂ hα 𝔇 h𝔇).1
  have hslice := ae_slice_of_ae_mix (P := P.prod P)
    (p := fun j x => (∀ u v, weylScaling (𝔇 (H j x)) ξ
      (fun z => -α * Real.log ‖z‖) u v < ∞) ∧
      IsEuclideanLengthMetric (fun u v => (weylScaling (𝔇 (H j x)) ξ
        (fun z => -α * Real.log ‖z‖) u v).toReal)) hlen 0
  have hprod := Measure.ae_ae_of_ae_prod hslice
  filter_upwards [hprod, hD] with ω hω hd
  obtain ⟨ω', hω'⟩ := hω.exists
  have heq : (fun u v => D ω (u, v)) = fun u v =>
      (weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v).toReal := by
    funext u v
    rw [← (hd u v).2, ENNReal.toReal_ofReal (hd u v).1]
  rw [heq]
  simpa [H] using hω'.2

open Classical in
/-- The strengthened pinch indicators are stationary. The affine,
measure-coordinate and mixture metric hypotheses are staged inputs pending
source checking. -/
theorem IsWholePlaneGFF.identDistrib_pinchIndicators_of_normalizedLQG
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → C(ℂ × ℂ, ℝ)}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α hC hcirc)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω (u, v) ∧
      ENNReal.ofReal (D ω (u, v)) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (haxioms : LQGMetricFieldAxioms (mixMeasure.prod (P.prod P)) γ ξ α
      (fun x => if x.1 = 0 then hC x.2.1 else
        affinePairing hC hcirc (((2 : ℝ)⁻¹ : ℝ) : ℂ) 0 x.2.2)
      (fun x => if x.1 = 0 then hcirc x.2.1 else
        affineCircle hcirc (((2 : ℝ)⁻¹ : ℝ) : ℂ) 0 x.2.2))
    {U T Q V : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q V) (M : ℝ) :
    IdentDistrib
      (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (fun x y => D ω (x, y)) U T Q V M
        ((2 : ℝ)⁻¹ ^ n) 0 then (1 : ℝ) else 0)
      (fun ω n => if pinchPointEventWithInternalBounds (μ ω) (fun x y => D ω (x, y)) U T Q V M
        ((2 : ℝ)⁻¹ ^ (n + 1)) 0 then (1 : ℝ) else 0) P P := by
  have hmetric := h.ae_lengthMetric_of_affine_mixture hAff hγ hγ₂ hα
    (k := (2 : ℝ)⁻¹) (by norm_num) 𝔇 h𝔇 hD haxioms
  let k : ℝ := (2 : ℝ)⁻¹
  have hk : 0 < k := by dsimp [k]; norm_num
  let a : Ω → ℝ≥0∞ := fun ω =>
    (ENNReal.ofReal (Real.exp (γ * (lqgQ γ * Real.log k +
      fieldCircleAverage α (hcirc ω) k 0))))⁻¹
  let c : Ω → ℝ := fun ω => Real.exp (-ξ * (hcirc ω k 0 + lqgQ γ * Real.log k)) *
    Real.exp (ξ * (α * Real.log k))
  let D' := normalizedDilationMetric γ ξ α k hcirc D
  have ha : ∀ᵐ ω ∂P, a ω ≠ 0 ∧ a ω ≠ ∞ ∧ 0 < c ω := by
    filter_upwards with ω
    refine ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top,
      ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))), ?_⟩
    exact mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hD' : ∀ᵐ ω ∂P, ∀ x y, D' ω (x, y) = c ω * D ω (k • x, k • y) :=
    Filter.Eventually.of_forall fun _ _ _ => rfl
  have hdist := h.identDistrib_normalizedDilation_singularMetric hAff hCC hγ hγ₂ hα hμ hk
    𝔇 h𝔇 hD haxioms
  have hscale : IdentDistrib (fun ω => (μ ω, D ω))
      (fun ω => (a ω • (μ ω).map (fun x : ℂ => (2 : ℝ) • x), D' ω)) P P := by
    simpa only [normalizedPullbackMeasure, a, D', k, inv_inv, ENNReal.ofReal_inv_of_pos (Real.exp_pos _)] using hdist
  exact identDistrib_pinchIndicators_of_normalized_dilation_of_ae_lengthMetric P μ D D'
    hconfig M a c ha hD' hmetric hscale

#print axioms IsWholePlaneGFF.ae_lengthMetric_of_affine_mixture
#print axioms IsWholePlaneGFF.identDistrib_pinchIndicators_of_normalizedLQG

end HarmonicBalls
