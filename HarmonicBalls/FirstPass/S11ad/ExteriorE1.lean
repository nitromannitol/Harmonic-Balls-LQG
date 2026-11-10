import HarmonicBalls.FirstPass.S11ad.ExteriorA
import HarmonicBalls.FirstPass.S11k.ExteriorPairings
import HarmonicBalls.FirstPass.S11k.ExteriorDistances
import HarmonicBalls.FirstPass.S11h.LocalEvents

/-!
# Outside-W version of the local first event `E₁` (note §6.3)

`pinchFirstEventLocal (D ω) W T Q' Q δ = {A < L} ∩ {d₀ < a₀}` with `A = pinchLocalA` (`ExteriorA.lean`),
`L = D(Q̄', ∂Q)` (`ExteriorPairings.exists_exterior_ofReal_setDist_version`), `d₀ = diam^δ(K₀)` on the closed set
`K₀ = closure (T \ B_{3δ}(W))` and `a₀ = D({0}, ∂B_δ)` (`ExteriorDistances`). Each term has a version measurable for the
field outside `closure W`, because all the localized domains avoid `closure W`. The only input is `hAx` (locality).
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace HarmonicBalls
namespace S11ad

universe u

/-- Outside-W version of the local first event `E₁ = pinchFirstEventLocal` (note §6.3): there is a set `G` measurable for
the field outside `closure W`, almost surely equal to `{ω | E₁ (D ω)}`. -/
theorem pinchFirstEventLocal_exterior_version (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (U V W T Q' Q : Set ℂ) (δ : ℝ) (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (γ ξ α₀ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc) (hDm : IsLQGMetricOfField P γ ξ α₀ hC D)
    (hOmega : ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ) :
    ∃ G : Set Ω, MeasurableSet[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] G ∧
      ∀ᵐ ω ∂P, ω ∈ G ↔ pinchFirstEventLocal (D ω) W T Q' Q δ := by
  have hδ0 : 0 < δ := hG.delta_pos
  have hE : IsOpen (closure W)ᶜ := isClosed_closure.isOpen_compl
  have hsph1 : sphere (0 : ℂ) 1 ⊆ (closure W)ᶜ := sphere_one_subset_compl_closure hG
  obtain ⟨hmetric, hloc⟩ := metric_locality_of_frozen hAx γ ξ α₀ hγ0 hγ2 hα Ω P hC hcirc D hGFF hDm
  have hloc' : ∀ V' : Set ℂ, IsOpen V' → V' ⊆ (closure W)ᶜ → ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ z w, Measurable[fieldSigmaAlgebra α₀ hC V'] fun ω => G ω z w) ∧
        ∀ᵐ ω ∂P, ∀ z ∈ V', ∀ w ∈ V', internalMetric (D ω) V' z w = G ω z w :=
    fun V' hV' _ => hloc V' hV'
  -- the local sup `A`
  obtain ⟨Ya, hYam, hYaa⟩ :=
    pinchLocalA_exterior_version hAx U V W T Q' Q δ hG γ ξ α₀ hγ0 hγ2 hα Ω P hC hcirc D hGFF hDm hOmega
  -- the local length `L = D(Q̄', ∂Q)`: `Q` is open, `Q̄' ⊆ Q`, `Q̄ ⊆ (closure W)ᶜ`
  have hQ'ne : (closure Q').Nonempty := hG.isConnected_Q'.nonempty.closure
  have hQfront : (frontier Q).Nonempty := by
    rw [nonempty_frontier_iff]
    refine ⟨hG.isConnected_Q.nonempty, fun hQu => ?_⟩
    have h5 : (5 : ℂ) ∈ Q := by rw [hQu]; exact mem_univ _
    have h5' : (5 : ℂ) ∈ closure T :=
      hG.sphere_subset_closure_T (by rw [mem_sphere_zero_iff_norm]; norm_num)
    exact (hG.closure_Q_subset (subset_closure h5)).2 h5'
  have hQV : closure Q ⊆ (closure W)ᶜ := fun x hx hxW =>
    (hG.closure_Q_subset hx).2 (subset_closure (hG.closure_W_subset_T hxW))
  obtain ⟨Yl, hYlm, hYla⟩ := ExteriorPairings.exists_exterior_ofReal_setDist_version hGFF α₀ hE hsph1 hmetric
    hG.isOpen_Q hE subset_rfl hG.closure_Q'_subset_Q hQV hQ'ne hQfront (hloc' _ hE subset_rfl)
  -- the origin distance `a₀ = D({0}, ∂B_δ)`, on `B_{2δ}(0) ⊆ (closure W)ᶜ`
  have hBE : ball (0 : ℂ) (2 * δ) ⊆ (closure W)ᶜ := fun z hz hzW => by
    have h1 := BundleParts.closure_W_norm_gt_one hG hzW
    rw [mem_ball_zero_iff] at hz
    linarith [hG.delta_lt]
  obtain ⟨Yo, hYom, hYoa⟩ := ExteriorDistances.exists_exterior_setDist_origin hGFF α₀ hE hsph1 hmetric
    hloc' hδ0 hBE
  -- the diameter `d₀ = diam^δ(K₀)`, with `K₀ = closure (T \ B_{3δ}(W))`
  have hK0 : ∀ x ∈ closure (T \ thickening (3 * δ) W), x ∉ thickening (3 * δ) W := fun x hx =>
    closure_minimal (fun y hy => hy.2) isOpen_thickening.isClosed_compl hx
  obtain ⟨Yd, hYdm, hYda⟩ := ExteriorDistances.exists_exterior_internalDiam_version hGFF α₀ hE hsph1 hmetric
    hloc' hδ0 (A := closure (T \ thickening (3 * δ) W))
    (ExteriorDistances.thickening_subset_compl_closure hδ0 hK0)
  refine ⟨{ω | Ya ω < Yl ω ∧ Yd ω < Yo ω}, (measurableSet_lt hYam hYlm).inter (measurableSet_lt hYdm hYom), ?_⟩
  filter_upwards [hYaa, hYla, hYda, hYoa] with ω h1 h2 h3 h4
  simp only [pinchFirstEventLocal, pinchLocalL, h1, h2, h3, h4]

end S11ad
end HarmonicBalls
