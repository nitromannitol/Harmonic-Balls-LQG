import HarmonicBalls.Proofs.Sec11.ConditionalAbsoluteMassDiameter
import HarmonicBalls.Proofs.Sec11.MassDiameterShiftPreservingOutside

/-! # Conditional mass and diameter from core contraction -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
namespace HarmonicBalls

/-- A positive-probability seed with protected mass and uniform tile bounds
inside every positive outside event gives conditional mass and diameter
positivity by a smooth core contraction away from the outside observation. -/
theorem IsWholePlaneGFF.condExp_absolute_mass_diameter_pos_of_core_seeds
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ ξ δ a σ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hξ : 0 < ξ)
    {ι : Type*} (S K U O O₀ O₁ C : Set ℂ) (H J : ι → Set ℂ)
    (hS : MeasurableSet S) (hbounded : Bornology.IsBounded S)
    (hbufferS : ∀ n z, z ∈ S → closedBall z (dyadicScale n) ⊆ ball 0 ε)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier S) = 0)
    (hδ : 0 < δ) (hpin : sphere (0 : ℂ) 1 ⊆ U)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (c : ℝ≥0∞) (ha : 0 ≤ a) (hmargin : a + a < σ)
    (hO : IsOpen O) (hO₀ : IsOpen O₀) (hO₀conn : IsConnected O₀)
    (hO₀O : O₀ ⊆ O) (hO₁ : IsOpen O₁)
    (hO₀compact : IsCompact (closure O₀)) (hO₀O₁ : closure O₀ ⊆ O₁)
    (hdisjoint : Disjoint O₁ S) (houtside : Disjoint O₁ U)
    (hJopen : ∀ i, IsOpen (J i)) (hJO : ∀ i, J i ⊆ O)
    (hCcompact : IsCompact C) (hCO₀ : C ⊆ O₀)
    (hbuffer : O ⊆ thickening δ K)
    (hcover : ∀ x ∈ K, x ∈ C ∨ ∃ i, x ∈ H i)
    (hattach : ∀ i, (H i ∩ C).Nonempty)
    (hseeds : ∀ F : Set Ω,
      MeasurableSet[MeasurableSpace.comap (localModConstPairings 0 hC U) inferInstance] F →
      0 < P F → ∃ A : Set Ω, A ⊆ F ∧ 0 < P A ∧ ∀ ω ∈ A,
        c < μ ω S ∧ ∀ i, ∀ x ∈ H i, ∀ y ∈ H i,
          internalMetric (𝔇 (hC ω)) (J i) x y ≤ ENNReal.ofReal a) :
    ∀ᵐ ω ∂P, 0 < (P[({ω | c < μ ω S ∧
      internalDiam (𝔇 (hC ω)) δ K < ENNReal.ofReal σ}).indicator
      (fun _ => (1 : ℝ)) | MeasurableSpace.comap (localModConstPairings 0 hC U) inferInstance]) ω := by
  apply h.condExp_absolute_mass_diameter_pos_of_shifts hμ S K U hS hbounded hbufferS
    hfront hδ hpin 𝔇 h𝔇 ψ hψ hψint c (ENNReal.ofReal σ)
  intro F hF hFp
  obtain ⟨A, hAF, hAp, hA⟩ := hseeds F hF hFp
  obtain ⟨g, hg, _, hgO, hp⟩ :=
    exists_positive_mass_small_diameter_wholePlane_shift_preserving_event P γ ξ hξ
      hC hcirc 𝔇 μ h𝔇 h ha hmargin hO hO₀ hO₀conn hO₀O hO₁ hO₀compact
      hO₀O₁ hdisjoint hS hJopen hJO hCcompact hCO₀ hbuffer hcover hattach A hAp hA
  refine ⟨g, hg, ?_, hp.trans_le (measure_mono ?_)⟩
  · intro z hz
    exact hgO z (fun hzO => Set.disjoint_left.mp houtside hzO hz)
  · intro ω hω
    exact ⟨hAF hω.1, hω.2⟩

#print axioms IsWholePlaneGFF.condExp_absolute_mass_diameter_pos_of_core_seeds
end HarmonicBalls
