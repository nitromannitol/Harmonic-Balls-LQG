import HarmonicBalls.Proofs.Sec11.PinchOutsideOpenMetric
import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstRepresentative

/-! # Outside locality of the pinch corridor crossing

The local metric decoder uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- The corridor crossing radius has an outside-field measurable version. -/
theorem IsCorrectedPinchConfiguration.exists_outside_baseMetric_corridor_crossing
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} [m₀ : MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∃ a : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞
      (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _ a ∧
      a =ᵐ[P] fun ω => ⨆ y ∈ sphere (0 : ℂ) 5, internalMetric (𝔇 (hC ω))
        (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
          closure (thickening (2 * δ) W))) 0 y := by
  let F : Set ℂ := ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))
  have hF : IsOpen F := isOpen_ball.sdiff (isClosed_closure.union isClosed_closure)
  have hs : sphere (0 : ℂ) 5 ⊆ F :=
    h.sphere_subset_six_component.trans (connectedComponentIn_subset F 0)
  obtain ⟨y, hy⟩ := NormedSpace.sphere_nonempty (x := (0 : ℂ)) |>.mpr (by norm_num : (0 : ℝ) ≤ 5)
  have hz : (0 : ℂ) ∈ F := connectedComponentIn_nonempty_iff.mp ⟨y, h.sphere_subset_six_component hy⟩
  have hFout : F ⊆ (closure W)ᶜ := by
    have hsub : closure W ⊆ closure (thickening (2 * δ) W) :=
      closure_mono (self_subset_thickening (by have := h.δ₀_mem.1; positivity) W)
    intro x hx hxW
    exact hx.2 (Or.inr (hsub hxW))
  have hm : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
    have hh := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 hgff
      (fun _ _ => 0) (fun _ => continuous_const) (fun _ => measurable_const)
    exact hh.mono fun _ hh => hh.1
  obtain ⟨G, hG, hGe⟩ := h.exists_outside_internal_baseMetric_on_open hgff 𝔇 h𝔇 F hF ⟨0, hz⟩ hFout
  obtain ⟨a, ha, hae⟩ := @exists_local_iSup_internalMetric_representative Ω m₀ P
    (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance)
    (fun ω => 𝔇 (hC ω)) G F {0} (sphere 0 5) hF (singleton_subset_iff.mpr hz) hs
    hm (fun x _ y _ => hG x y)
    (hGe.mono fun _ hw x hx y hy => hw x ((singleton_subset_iff.mpr hz) hx) y (hs hy))
  refine ⟨a, ha, ?_⟩
  filter_upwards [hae] with ω he
  simpa only [iSup_singleton] using he.symm

end HarmonicBalls
