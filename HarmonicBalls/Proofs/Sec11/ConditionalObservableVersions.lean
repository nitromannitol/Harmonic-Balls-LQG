import HarmonicBalls.Proofs.Sec11.ConditionalObservableShift

/-! # Conditional positivity for almost-sure observable versions -/

namespace HarmonicBalls
open MeasureTheory Set Filter

/-- Conditional positivity transfers from shifted geometric events represented
almost surely by one measurable observable event. The representation may
have a different exceptional set for each chosen shift. -/
theorem condExp_indicator_pos_of_shifted_observable_versions
    {Ω E O : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace O]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → E) (hX : Measurable X) (W : E → O) (hW : Measurable W)
    (B : Set E) (hB : MeasurableSet B) (H : Set Ω)
    (hH : H =ᵐ[P] X ⁻¹' B)
    (hpos : ∀ F : Set Ω,
      MeasurableSet[MeasurableSpace.comap (W ∘ X) inferInstance] F → 0 < P F →
      ∃ (Y : Ω → E) (G : Set Ω), Measurable Y ∧ P.map Y ≪ P.map X ∧
        (∀ᵐ ω ∂P, W (Y ω) = W (X ω)) ∧ G =ᵐ[P] Y ⁻¹' B ∧
        0 < P (F ∩ G)) :
    ∀ᵐ ω ∂P, 0 < (P[H.indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap (W ∘ X) inferInstance]) ω := by
  have hp := condExp_indicator_pos_of_shifted_observables P X hX W hW B hB (by
    intro F hF hFp
    obtain ⟨Y, G, hY, hac, hpreserve, hG, hp⟩ := hpos F hF hFp
    refine ⟨Y, hY, hac, hpreserve, ?_⟩
    have heq : F ∩ G =ᵐ[P] {ω | ω ∈ F ∧ Y ω ∈ B} := by
      filter_upwards [hG] with ω hω
      have hω' : ω ∈ G ↔ Y ω ∈ B := iff_of_eq hω
      exact propext (and_congr_right (fun _ => hω'))
    rwa [← measure_congr heq])
  have hi : H.indicator (fun _ => (1 : ℝ)) =ᵐ[P]
      (X ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hH] with ω hω
    by_cases h : ω ∈ H
    · have h' : ω ∈ X ⁻¹' B := hω.mp h
      simp [h, h']
    · have h' : ω ∉ X ⁻¹' B := fun ht => h (hω.mpr ht)
      simp [h, h']
  filter_upwards [hp, condExp_congr_ae (m := MeasurableSpace.comap (W ∘ X)
    inferInstance) hi] with ω hp he
  rw [he]
  exact hp


/-- Conditional positivity for geometric events with a common
modulo-constant field representation under every fixed smooth shift. -/
theorem IsWholePlaneGFF.condExp_modConst_pos_of_interior_shift_versions
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (α : ℝ) (U : Set ℂ)
    (B : Set (LocalZeroMeanTest univ → ℝ)) (hB : MeasurableSet B)
    (H : Set Ω) (G : (ℂ → ℝ) → Set Ω)
    (hH : H =ᵐ[P] (localModConstPairings α hC univ) ⁻¹' B)
    (hG : ∀ g : ℂ → ℝ, IsTestFunction univ g → G g =ᵐ[P]
      (localModConstPairings α (fun ω => addFunPairing (hC ω) g) univ) ⁻¹' B)
    (hpos : ∀ F : Set Ω,
      MeasurableSet[MeasurableSpace.comap (localModConstPairings α hC U) inferInstance] F →
      0 < P F → ∃ g : ℂ → ℝ, IsTestFunction univ g ∧
        (∀ z ∈ U, g z = 0) ∧ 0 < P (F ∩ G g)) :
    ∀ᵐ ω ∂P, 0 < (P[H.indicator (fun _ => (1 : ℝ)) |
      MeasurableSpace.comap (localModConstPairings α hC U) inferInstance]) ω := by
  have hp := hh.condExp_modConst_pos_of_interior_shifts α U B hB (by
    intro F hF hFp
    obtain ⟨g, hg, hgU, hp⟩ := hpos F hF hFp
    refine ⟨g, hg, hgU, ?_⟩
    have heq : F ∩ G g =ᵐ[P] {ω | ω ∈ F ∧ localModConstPairings α
        (fun ω => addFunPairing (hC ω) g) univ ω ∈ B} := by
      filter_upwards [hG g hg] with ω hω
      have hω' : ω ∈ G g ↔ localModConstPairings α
          (fun ω => addFunPairing (hC ω) g) univ ω ∈ B := iff_of_eq hω
      exact propext (and_congr_right (fun _ => hω'))
    rwa [← measure_congr heq])
  have hi : H.indicator (fun _ => (1 : ℝ)) =ᵐ[P]
      ((localModConstPairings α hC univ) ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hH] with ω hω
    by_cases h : ω ∈ H
    · have h' : ω ∈ (localModConstPairings α hC univ) ⁻¹' B := hω.mp h
      simp [h, h']
    · have h' : ω ∉ (localModConstPairings α hC univ) ⁻¹' B := fun ht => h (hω.mpr ht)
      simp [h, h']
  filter_upwards [hp, condExp_congr_ae (m := MeasurableSpace.comap
    (localModConstPairings α hC U) inferInstance) hi] with ω hp he
  rw [he]
  exact hp

end HarmonicBalls
