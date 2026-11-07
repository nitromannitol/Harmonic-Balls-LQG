import HarmonicBalls.Proofs.Sec11.PinchOutsideOpenMetric

/-! # Outside locality of the buffered internal diameter

The local metric decoder uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- The internal diameter away from the core has an outside-field
measurable version for the whole-plane GFF base metric. -/
theorem IsCorrectedPinchConfiguration.exists_outside_baseMetric_buffered_diameter
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} [m₀ : MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∃ a : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞
      (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _ a ∧
      a =ᵐ[P] fun ω => internalDiam (𝔇 (hC ω)) δ (T \ thickening (3 * δ) W) := by
  let A : Set ℂ := T \ thickening (3 * δ) W
  by_cases hA : A.Nonempty
  · let F := thickening δ A
    have hδ := h.δ₀_mem.1
    have hsub : A ⊆ F := self_subset_thickening hδ A
    have hFout : F ⊆ (closure W)ᶜ := by
      intro x hx hxW
      obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
      have hw : x ∈ thickening δ W := (closure_subset_thickening hδ W) hxW
      obtain ⟨w, hwW, hxw⟩ := mem_thickening_iff.mp hw
      have hd : dist y w < 3 * δ := by
        have ht := dist_triangle y x w
        rw [dist_comm y x] at ht
        linarith
      exact hy.2 (mem_thickening_iff.mpr ⟨w, hwW, hd⟩)
    have hm : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
      have hh := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 hgff
        (fun _ _ => 0) (fun _ => continuous_const) (fun _ => measurable_const)
      exact hh.mono fun _ hh => hh.1
    obtain ⟨G, hG, hGe⟩ := h.exists_outside_internal_baseMetric_on_open hgff 𝔇 h𝔇 F
      isOpen_thickening (hA.mono hsub) hFout
    obtain ⟨a, ha, hae⟩ := @exists_local_iSup_internalMetric_representative Ω m₀ P
      (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance)
      (fun ω => 𝔇 (hC ω)) G F A A isOpen_thickening hsub hsub hm
      (fun x _ y _ => hG x y)
      (hGe.mono fun _ hw x hx y hy => hw x (hsub hx) y (hsub hy))
    refine ⟨a, ha, ?_⟩
    filter_upwards [hae] with ω he
    change a ω = ⨆ x ∈ A, ⨆ y ∈ A, internalMetric (𝔇 (hC ω)) F x y
    exact he.symm
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    refine ⟨fun _ => 0, measurable_const, ?_⟩
    apply Eventually.of_forall
    intro ω
    change 0 = internalDiam (𝔇 (hC ω)) δ A
    rw [he]
    simp [internalDiam]

#print axioms IsCorrectedPinchConfiguration.exists_outside_baseMetric_buffered_diameter
end HarmonicBalls
