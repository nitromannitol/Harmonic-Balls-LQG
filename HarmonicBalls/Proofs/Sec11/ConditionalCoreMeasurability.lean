import HarmonicBalls.Proofs.Sec11.ConditionalCoreContainment
import HarmonicBalls.Proofs.Sec11.InternalDiameterLaw

/-! # Measurability of conditional mass and diameter events

The dyadic core result uses Leonardo Bonanno's smooth-shift formalization
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin`. -/

namespace HarmonicBalls
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

/-- The internal diameter of any fixed set is almost everywhere measurable
for the base LQG metric. -/
theorem IsWholePlaneGFF.aemeasurable_base_internalDiam
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ δ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hδ : 0 < δ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (K : Set ℂ) : AEMeasurable (fun ω => internalDiam (𝔇 (hC ω)) δ K) P := by
  exact (h.identDistrib_baseMetric_internalDiameter h 𝔇 h𝔇
    isOpen_thickening (self_subset_thickening hδ K)).aemeasurable_fst

/-- Fixed mass and internal-diameter threshold events are measurable after
completion of the probability space. -/
theorem IsWholePlaneGFF.nullMeasurableSet_mass_internalDiam
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {α γ ξ δ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hδ : 0 < δ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (S K : Set ℂ) (hS : MeasurableSet S) (c d : ℝ≥0∞) :
    NullMeasurableSet {ω | c < μ ω S ∧ internalDiam (𝔇 (hC ω)) δ K < d} P := by
  exact (nullMeasurableSet_lt aemeasurable_const
    ((Measure.measurable_coe hS).comp_aemeasurable (h.aemeasurable_lqgMeasure hμ))).inter
      (nullMeasurableSet_lt (h.aemeasurable_base_internalDiam hδ 𝔇 h𝔇 K) aemeasurable_const)

/-- A full-support dyadic core gives conditional positivity of the target
mass and diameter event when the ambient core is the closure of `V`. -/
theorem IsWholePlaneGFF.condExp_pinch_mass_diameter_pos_of_dyadic_cores
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ ξ δ a σ t : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hγ : 0 < γ) (hξ : 0 < ξ)
    (z : ℂ) (L : ℝ) (hL : 0 < L) (U V O : Set ℂ) (hU : MeasurableSet U)
    (hSU : closedSquare z L ⊆ U)
    (hbufferS : ∀ n x, x ∈ closedSquare z L → closedBall x (dyadicScale n) ⊆ ball 0 ε)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (closedSquare z L)) = 0)
    (hδ : 0 < δ) (hpin : sphere (0 : ℂ) 1 ⊆ O)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (ht : 0 ≤ t) (ha : 0 ≤ a) (hmargin : a + a < σ)
    (hKc : IsCompact (closure V)) (hK : IsConnected (closure V))
    (hKO : Disjoint (closure V) (closure O))
    (hSK : closedSquare z L ⊆ interior (closure V))
    (hfull : ∀ᵐ ω ∂P, ∀ W : Set ℂ, IsOpen W → W.Nonempty → 0 < μ ω W)
    (b : ℕ → ℝ≥0∞) (p : ℝ) (hp : 2 < p) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hsmall : ∀ᶠ n in atTop, b n < ENNReal.ofReal a)
    (hbound : ∀ᶠ n in atTop, ∀ i, P {ω | b n * ENNReal.ofReal
      (Real.exp (ξ * hcirc ω 1 0)) < dyadicIntermediateInternalDiameter
        (fun ω => 𝔇 (hC ω)) z L n i ω} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n))) :
    ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (𝔇 (hC ω)) δ V < ENNReal.ofReal σ ∧
      ENNReal.ofReal t < μ ω U}).indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap (localModConstPairings 0 hC O) inferInstance]) ω := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hS := h.nullMeasurableSet_mass_internalDiam hμ hδ 𝔇 h𝔇 (closedSquare z L)
    (closure V) (IsCompact.reProdIm isCompact_Icc isCompact_Icc).isClosed.measurableSet
    (ENNReal.ofReal t) (ENNReal.ofReal σ)
  have hT' := h.nullMeasurableSet_mass_internalDiam hμ hδ 𝔇 h𝔇 U V hU
    (ENNReal.ofReal t) (ENNReal.ofReal σ)
  have hT : NullMeasurableSet {ω | internalDiam (𝔇 (hC ω)) δ V < ENNReal.ofReal σ ∧
      ENNReal.ofReal t < μ ω U} P := by simpa only [and_comm] using hT'
  apply condExp_mass_diameter_pos_of_square_closure P _ (fun ω => 𝔇 (hC ω)) μ
    (closedSquare z L) U V δ (ENNReal.ofReal t) (ENNReal.ofReal σ) hSU hS hT
  exact h.condExp_mass_diameter_pos_of_full_support_dyadic_cores hμ hγ hξ z L hL
    (closure V) O hbufferS hfront hδ hpin 𝔇 h𝔇 ψ hψ hψint ht ha hmargin hKc hK
    hKO hSK hfull b p hp e he hsmall hbound

#print axioms IsWholePlaneGFF.aemeasurable_base_internalDiam
#print axioms IsWholePlaneGFF.nullMeasurableSet_mass_internalDiam
#print axioms IsWholePlaneGFF.condExp_pinch_mass_diameter_pos_of_dyadic_cores
end HarmonicBalls
