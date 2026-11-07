import HarmonicBalls.Proofs.Sec11.ConditionalMassDiameterCore

/-! # Conditional mass and diameter with varying protected cores

The smooth-shift transfer uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization. -/

noncomputable section
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
namespace HarmonicBalls

/-- A different protected subset and contracting core may be selected for each
positive outside event. Mass retained on the protected subset gives the same
lower bound for the fixed target set. -/
theorem IsWholePlaneGFF.condExp_absolute_mass_diameter_pos_of_variable_core_seeds
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {ε α γ ξ δ a σ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hξ : 0 < ξ)
    (S K U : Set ℂ) (hS : MeasurableSet S) (hbounded : Bornology.IsBounded S)
    (hbufferS : ∀ n z, z ∈ S → closedBall z (dyadicScale n) ⊆ ball 0 ε)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier S) = 0)
    (hδ : 0 < δ) (hpin : sphere (0 : ℂ) 1 ⊆ U)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (c : ℝ≥0∞) (ha : 0 ≤ a) (hmargin : a + a < σ)
    (hseeds : ∀ F : Set Ω,
      MeasurableSet[MeasurableSpace.comap (localModConstPairings 0 hC U) inferInstance] F →
      0 < P F → ∃ (ι : Type) (S' O O₀ O₁ C : Set ℂ) (H J : ι → Set ℂ) (A : Set Ω),
        S' ⊆ S ∧ MeasurableSet S' ∧ A ⊆ F ∧ 0 < P A ∧
        IsOpen O ∧ IsOpen O₀ ∧ IsConnected O₀ ∧ O₀ ⊆ O ∧ IsOpen O₁ ∧
        IsCompact (closure O₀) ∧ closure O₀ ⊆ O₁ ∧ Disjoint O₁ S' ∧ Disjoint O₁ U ∧
        (∀ i, IsOpen (J i)) ∧ (∀ i, J i ⊆ O) ∧ IsCompact C ∧ C ⊆ O₀ ∧
        O ⊆ thickening δ K ∧ (∀ x ∈ K, x ∈ C ∨ ∃ i, x ∈ H i) ∧
        (∀ i, (H i ∩ C).Nonempty) ∧
        ∀ ω ∈ A, c < μ ω S' ∧ ∀ i, ∀ x ∈ H i, ∀ y ∈ H i,
          internalMetric (𝔇 (hC ω)) (J i) x y ≤ ENNReal.ofReal a) :
    ∀ᵐ ω ∂P, 0 < (P[({ω | c < μ ω S ∧
      internalDiam (𝔇 (hC ω)) δ K < ENNReal.ofReal σ}).indicator
      (fun _ => (1 : ℝ)) | MeasurableSpace.comap (localModConstPairings 0 hC U) inferInstance]) ω := by
  apply h.condExp_absolute_mass_diameter_pos_of_shifts hμ S K U hS hbounded hbufferS
    hfront hδ hpin 𝔇 h𝔇 ψ hψ hψint c (ENNReal.ofReal σ)
  intro F hF hFp
  obtain ⟨ι, S', O, O₀, O₁, C, H, J, A, hsub, hS', hAF, hAp,
    hO, hO₀, hO₀conn, hO₀O, hO₁, hcompact, hO₀O₁, hdisj, houtside,
    hJopen, hJO, hCcompact, hCO₀, hbuffer, hcover, hattach, hA⟩ := hseeds F hF hFp
  obtain ⟨g, hg, _, hgO, hpos⟩ :=
    exists_positive_mass_small_diameter_wholePlane_shift_preserving_event P γ ξ hξ
      hC hcirc 𝔇 μ h𝔇 h ha hmargin hO hO₀ hO₀conn hO₀O hO₁ hcompact
      hO₀O₁ hdisj hS' hJopen hJO hCcompact hCO₀ hbuffer hcover hattach A hAp hA
  refine ⟨g, hg, ?_, hpos.trans_le (measure_mono ?_)⟩
  · intro z hz
    exact hgO z (fun hzO => Set.disjoint_left.mp houtside hzO hz)
  · intro ω hω
    refine ⟨hAF hω.1, ?_, hω.2.2⟩
    exact hω.2.1.trans_le (measure_mono hsub)

#print axioms IsWholePlaneGFF.condExp_absolute_mass_diameter_pos_of_variable_core_seeds
end HarmonicBalls
