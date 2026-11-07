import HarmonicBalls.Proofs.Sec11.CorrectedPinchUniformFirstShift
import HarmonicBalls.Proofs.Sec11.CorrectedPinchOpenThresholds
import HarmonicBalls.Steps.Sec11.WholePlaneWeylShift

/-! Positive-probability construction of the first shifted pinch event. -/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- For any positive-probability event, one deterministic nonnegative smooth
shift makes the first auxiliary event hold on a positive-probability subset.
The event in the conclusion still refers to the shifted metric; transfer of
its law is a separate step. -/
theorem IsCorrectedPinchConfiguration.exists_positive_wholePlane_first_shift
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω) (hA : 0 < P A)
    (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (hconn : IsConnected (T \ thickening (3 * δ) W)) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧ (∀ x, 0 ≤ f x) ∧
      (∀ x ∉ thickening δ Q ∪ ball 0 δ, f x = 0) ∧
      0 < P {ω | ω ∈ A ∧ pinchFirstEvent
        (𝔇 (addFunPairing (hC ω) f)) W T Q' Q δ} := by
  have hbase : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
    filter_upwards [ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 hgff
      (fun _ _ => 0) (by intro ω; fun_prop) (by intro x; fun_prop)] with ω hω
    exact hω.1
  obtain ⟨n, m, k, l, hn, hk, hp⟩ :=
    h.exists_open_first_certificate_thresholds P A (fun ω => 𝔇 (hC ω)) hA hbase hconn
  obtain ⟨f, hsm, hcomp, hnonneg, hsupp, hshift⟩ :=
    h.toIsPinchPointProofConfiguration.exists_uniform_first_event_shift hξ n m k l hn hk
  let B : Set Ω := {ω | ω ∈ A ∧
    (n : ℝ≥0∞)⁻¹ < ENNReal.ofReal (setDist (𝔇 (hC ω)) Q' (frontier Q)) ∧
    (⨆ y ∈ sphere (0 : ℂ) 5, internalMetric (𝔇 (hC ω))
      (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
        closure (thickening (2 * δ) W))) 0 y) < m ∧
    (k : ℝ≥0∞)⁻¹ < ENNReal.ofReal (setDist (𝔇 (hC ω)) {0} (sphere 0 (δ / 2))) ∧
    internalDiam (𝔇 (hC ω)) δ (T \ thickening (3 * δ) W) < l}
  let G : Set Ω := {ω | IsEuclideanLengthMetric (𝔇 (hC ω)) ∧
    IsEuclideanLengthMetric (𝔇 (addFunPairing (hC ω) f)) ∧
    (∀ x y, weylScaling (𝔇 (hC ω)) ξ 0 x y = ENNReal.ofReal (𝔇 (hC ω) x y)) ∧
    (∀ x y, ENNReal.ofReal (𝔇 (addFunPairing (hC ω) f) x y) =
      weylScaling (𝔇 (hC ω)) ξ f x y) ∧
    (∀ x y, weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ 0 x y =
      ENNReal.ofReal (𝔇 (addFunPairing (hC ω) f) x y)) ∧
    (∀ x y, ENNReal.ofReal (𝔇 (hC ω) x y) =
      weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -f z) x y)}
  have hG : ∀ᵐ ω ∂P, ω ∈ G :=
    ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 hgff
      (fun _ => f) (by intro ω; exact hsm.continuous) (by intro x; fun_prop)
  have heq : B =ᵐ[P] B ∩ G := by
    filter_upwards [hG] with ω hω
    simp only [mem_inter_iff, hω, and_true]
  have hp' : 0 < P (B ∩ G) := by rw [← measure_congr heq]; exact hp
  refine ⟨f, ⟨hsm, hcomp, subset_univ _⟩, hnonneg, hsupp, hp'.trans_le (measure_mono ?_)⟩
  intro ω hω
  obtain ⟨hD, hE, _, hforward, _, hreverse⟩ := hω.2
  have hEnonneg : ∀ x y, 0 ≤ 𝔇 (addFunPairing (hC ω) f) x y := by
    intro x y
    have ht := hE.triangle x y x
    rw [hE.self_eq_zero, hE.symm y x] at ht
    linarith
  exact ⟨hω.1.1, hshift _ _ hD hE hEnonneg hforward hreverse
    hω.1.2.1.le hω.1.2.2.1.le hω.1.2.2.2.1.le hω.1.2.2.2.2.le⟩

#print axioms IsCorrectedPinchConfiguration.exists_positive_wholePlane_first_shift

end HarmonicBalls
