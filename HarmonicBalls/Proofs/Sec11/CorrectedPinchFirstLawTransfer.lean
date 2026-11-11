import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstRepresentative

/-! Transfer of the first pinch certificate through equivalent metric laws. -/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- The two inequalities in the open-corridor certificate. -/
def correctedOpenFirstCertificate (D : ℂ → ℂ → ℝ) (W T Q' Q : Set ℂ) (δ : ℝ) : Prop :=
  (⨆ y ∈ sphere (0 : ℂ) 5, internalMetric D
    (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0 y) <
    ENNReal.ofReal (setDist D Q' (frontier Q)) ∧
  internalDiam D δ (T \ thickening (3 * δ) W) <
    ENNReal.ofReal (setDist D {0} (sphere 0 δ))

/-- Two continuous observations have one measurable representative for the
first certificate when both are almost surely length metrics. -/
theorem IsCorrectedPinchConfiguration.exists_common_open_first_representative
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D₀ D₁ : Ω → C(ℂ × ℂ, ℝ))
    (hD₀ : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y => D₀ ω (x, y)))
    (hD₁ : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y => D₁ ω (x, y))) :
    ∃ E : Set C(ℂ × ℂ, ℝ), MeasurableSet E ∧
      (∀ᵐ ω ∂P, correctedOpenFirstCertificate (fun x y => D₀ ω (x, y)) W T Q' Q δ ↔ D₀ ω ∈ E) ∧
      (∀ᵐ ω ∂P, correctedOpenFirstCertificate (fun x y => D₁ ω (x, y)) W T Q' Q δ ↔ D₁ ω ∈ E) := by
  let e₀ : Ω → Ω ⊕ Ω := Sum.inl
  let e₁ : Ω → Ω ⊕ Ω := Sum.inr
  have he₀ : MeasurableEmbedding e₀ := ⟨Sum.inl_injective, measurable_inl, fun {_} hs => hs.inl_image⟩
  have he₁ : MeasurableEmbedding e₁ := ⟨Sum.inr_injective, measurable_inr, fun {_} hs => hs.inr_image⟩
  let S : Measure (Ω ⊕ Ω) := P.map e₀ + P.map e₁
  let D : Ω ⊕ Ω → C(ℂ × ℂ, ℝ) := Sum.elim D₀ D₁
  have hD : ∀ᵐ s ∂S, IsEuclideanLengthMetric (fun x y => D s (x, y)) := by
    apply ae_add_measure_iff.mpr
    exact ⟨he₀.ae_map_iff.mpr hD₀, he₁.ae_map_iff.mpr hD₁⟩
  obtain ⟨E, hE, heq⟩ := h.exists_open_first_representative S D hD
  have hh := ae_add_measure_iff.mp heq
  exact ⟨E, hE, he₀.ae_map_iff.mp hh.1, he₁.ae_map_iff.mp hh.2⟩

/-- Absolute continuity transfers positive probability of the certificate
from the second continuous metric observation to the first. -/
theorem IsCorrectedPinchConfiguration.positive_open_first_of_ac
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D₀ D₁ : Ω → C(ℂ × ℂ, ℝ)) (h₀ : Measurable D₀) (h₁ : Measurable D₁)
    (hD₀ : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y => D₀ ω (x, y)))
    (hD₁ : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y => D₁ ω (x, y)))
    (hac : P.map D₁ ≪ P.map D₀)
    (hp : 0 < P {ω | correctedOpenFirstCertificate (fun x y => D₁ ω (x, y)) W T Q' Q δ}) :
    0 < P {ω | correctedOpenFirstCertificate (fun x y => D₀ ω (x, y)) W T Q' Q δ} := by
  obtain ⟨E, hE, he₀, he₁⟩ := h.exists_common_open_first_representative P D₀ D₁ hD₀ hD₁
  have eq₀ : {ω | correctedOpenFirstCertificate (fun x y => D₀ ω (x, y)) W T Q' Q δ} =ᵐ[P] D₀ ⁻¹' E := by
    filter_upwards [he₀] with ω hω
    exact propext hω
  have eq₁ : {ω | correctedOpenFirstCertificate (fun x y => D₁ ω (x, y)) W T Q' Q δ} =ᵐ[P] D₁ ⁻¹' E := by
    filter_upwards [he₁] with ω hω
    exact propext hω
  rw [measure_congr eq₁, ← Measure.map_apply h₁ hE] at hp
  rw [measure_congr eq₀, ← Measure.map_apply h₀ hE]
  by_contra hn
  have hz : (P.map D₀) E = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hn)
  exact (ne_of_gt hp) (hac hz)


end HarmonicBalls
