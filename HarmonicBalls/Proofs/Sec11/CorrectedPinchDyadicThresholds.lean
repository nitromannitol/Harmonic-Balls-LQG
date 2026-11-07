import HarmonicBalls.Proofs.Sec11.CorrectedPinchCoreGeometry
import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstSecondNull

/-! # Dyadic conditional thresholds in the corrected pinch geometry

The dyadic core argument uses Leonardo Bonanno's smooth-shift formalization
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin`. -/

namespace HarmonicBalls
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

/-- A square inside the mass set gives all the strict conditional thresholds
for the second pinch event. Full support, square frontier continuity, and
the uniform dyadic diameter tail remain explicit. -/
theorem IsCorrectedPinchConfiguration.conditional_dyadic_thresholds
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {α γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hg : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hγ : 0 < γ) (hξ : 0 < ξ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (z : ℂ) (L : ℝ) (hL : 0 < L) (hSU : closedSquare z L ⊆ U)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (closedSquare z L)) = 0)
    (hfull : ∀ᵐ ω ∂P, ∀ A : Set ℂ, IsOpen A → A.Nonempty → 0 < μ ω A)
    (b : ℕ → ℝ≥0∞) (p : ℝ) (hp : 2 < p) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hsmall : ∀ a : ℝ, 0 < a → ∀ᶠ n in atTop, b n < ENNReal.ofReal a)
    (hbound : ∀ᶠ n in atTop, ∀ i, P {ω | b n * ENNReal.ofReal
      (Real.exp (ξ * hcirc ω 1 0)) < dyadicIntermediateInternalDiameter
        (fun ω => 𝔇 (hC ω)) z L n i ω} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n))) :
    ∀ n k : ℕ, 0 < n →
      NullMeasurableSet {ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U} P ∧
      ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U}).indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance]) ω := by
  intro n k hn
  have hδ : 0 < δ := h.δ₀_mem.1
  have hnull := hg.nullMeasurableSet_mass_internalDiam hμ hδ 𝔇 h𝔇 U V h.isOpen_U.measurableSet
    (k : ℝ≥0∞) (n : ℝ≥0∞)⁻¹
  refine ⟨by simpa only [and_comm] using hnull, ?_⟩
  obtain ⟨ψ, hψ, hψint⟩ := IsTestFunction.exists_integral_eq_one
    (isOpen_univ : IsOpen (univ : Set ℂ)) ⟨0, mem_univ _⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < (n : ℝ)⁻¹ / 4 := by positivity
  have hpos := hg.condExp_pinch_mass_diameter_pos_of_dyadic_cores hμ hγ hξ z L hL
    U V (closure W)ᶜ h.isOpen_U.measurableSet hSU
    (fun m x hx => h.mass_buffer m x (hSU hx)) hfront hδ h.outside_core.1
    𝔇 h𝔇 ψ hψ hψint (show (0 : ℝ) ≤ k by positivity) ha.le
    (show (n : ℝ)⁻¹ / 4 + (n : ℝ)⁻¹ / 4 < (n : ℝ)⁻¹ by linarith [inv_pos.mpr hn'])
    h.closure_V_core.1 h.closure_V_core.2.1 h.outside_core.2
    (hSU.trans h.closure_V_core.2.2) hfull b p hp e he (hsmall _ ha) hbound
  simpa only [ENNReal.ofReal_inv_of_pos hn', ENNReal.ofReal_natCast] using hpos

/-- The dyadic threshold estimate supplies the conditional input to joint
positivity of the first and second pinch events. -/
theorem IsCorrectedPinchConfiguration.positive_first_second_of_dyadic_thresholds
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} {m₀ : MeasurableSpace Ω} (P : Measure Ω) {α γ ξ : ℝ}
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hg : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hγ : 0 < γ) (hξ : 0 < ξ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (M : ℝ) (A : Set Ω)
    (hA : MeasurableSet[MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ)
      inferInstance] A)
    (hArep : A =ᵐ[P] {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ})
    (ha : @Measurable Ω ℝ≥0∞
      (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _
      (fun ω => ENNReal.ofReal (setDist (𝔇 (hC ω)) (sphere 0 δ) (sphere 0 (2 * δ)))))
    (hb : @Measurable Ω ℝ≥0∞
      (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _
      (fun ω => ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6))
    (hgreen : ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ∞)
    (z : ℂ) (L : ℝ) (hL : 0 < L) (hSU : closedSquare z L ⊆ U)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (closedSquare z L)) = 0)
    (hfull : ∀ᵐ ω ∂P, ∀ B : Set ℂ, IsOpen B → B.Nonempty → 0 < μ ω B)
    (b : ℕ → ℝ≥0∞) (p : ℝ) (hp : 2 < p) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hsmall : ∀ a : ℝ, 0 < a → ∀ᶠ n in atTop, b n < ENNReal.ofReal a)
    (hbound : ∀ᶠ n in atTop, ∀ i, P {ω | b n * ENNReal.ofReal
      (Real.exp (ξ * hcirc ω 1 0)) < dyadicIntermediateInternalDiameter
        (fun ω => 𝔇 (hC ω)) z L n i ω} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n))) :
    0 < P {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M} := by
  let : MeasurableSpace Ω := m₀
  have hm : MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance ≤ m₀ := by
    apply measurable_iff_comap_le.mp
    exact measurable_pi_iff.mpr fun φ =>
      (hg.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).sub_const _
  exact h.positive_wholePlane_first_second_null hξ P hC hcirc 𝔇 μ h𝔇 hg M _ hm A
    hA hArep ha hb hgreen
    (h.conditional_dyadic_thresholds hg hμ hγ hξ 𝔇 h𝔇 z L hL hSU hfront hfull
      b p hp e he hsmall hbound)

#print axioms IsCorrectedPinchConfiguration.conditional_dyadic_thresholds
#print axioms IsCorrectedPinchConfiguration.positive_first_second_of_dyadic_thresholds
end HarmonicBalls
