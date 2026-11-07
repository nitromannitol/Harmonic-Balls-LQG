import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstMeasurable
import HarmonicBalls.Steps.Sec11.LocalExtremaRepresentatives

/-! A common observable representative of the first pinch certificate. -/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

/-- A set distance is measurable for a pointwise measurable family of
jointly continuous distance functions, even away from the metric event. -/
theorem measurable_ofReal_setDist_of_continuous
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ}
    {A B : Set ℂ} (hA : A.Nonempty) (hB : B.Nonempty)
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hcont : ∀ ω, Continuous fun p : ℂ × ℂ => D ω p.1 p.2) :
    Measurable fun ω => ENNReal.ofReal (setDist (D ω) A B) := by
  let f : A × B → Ω → ℝ≥0∞ := fun p ω => ENNReal.ofReal (D ω p.1 p.2)
  have hf (ω : Ω) : Continuous (fun p : A × B => f p ω) := by
    have hp : Continuous (fun p : A × B => ((p.1 : ℂ), (p.2 : ℂ))) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    exact ENNReal.continuous_ofReal.comp ((hcont ω).comp hp)
  have hm : Measurable (⨅ p : A × B, f p) :=
    measurable_iInf_of_upperSemicontinuous (fun p => (hD p.1 p.2).ennreal_ofReal)
      (fun ω => (hf ω).upperSemicontinuous)
  convert hm using 1
  ext ω
  rw [ofReal_setDist_eq_iInf hA hB]
  simp only [iInf_apply, f, iInf_subtype, iInf_prod]

/-- The open first certificate has a measurable representative on continuous
metric observations, simultaneously on the almost-sure length-metric event. -/
theorem IsCorrectedPinchConfiguration.exists_open_first_representative
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → C(ℂ × ℂ, ℝ))
    (hm : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y => D ω (x, y))) :
    ∃ E : Set C(ℂ × ℂ, ℝ), MeasurableSet E ∧ ∀ᵐ ω ∂P,
      (((⨆ y ∈ sphere (0 : ℂ) 5, internalMetric (fun x y => D ω (x, y))
        (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
          closure (thickening (2 * δ) W))) 0 y) <
            ENNReal.ofReal (setDist (fun x y => D ω (x, y)) Q' (frontier Q)) ∧
        internalDiam (fun x y => D ω (x, y)) δ (T \ thickening (3 * δ) W) <
          ENNReal.ofReal (setDist (fun x y => D ω (x, y)) {0} (sphere 0 δ))) ↔ D ω ∈ E) := by
  let m := MeasurableSpace.comap D inferInstance
  have hobs : Measurable[m] D := comap_measurable D
  have hd (x y : ℂ) : Measurable[m] (fun ω => D ω (x, y)) :=
    (ContinuousMap.measurable_eval (x, y)).comp hobs
  let F : Set ℂ := ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))
  let A : Set ℂ := T \ thickening (3 * δ) W
  have hF : IsOpen F := isOpen_ball.sdiff (isClosed_closure.union isClosed_closure)
  have hs : sphere (0 : ℂ) 5 ⊆ F :=
    h.sphere_subset_six_component.trans (connectedComponentIn_subset F 0)
  obtain ⟨y, hy⟩ := NormedSpace.sphere_nonempty (x := (0 : ℂ)) |>.mpr (by norm_num : (0 : ℝ) ≤ 5)
  have hz : (0 : ℂ) ∈ F := connectedComponentIn_nonempty_iff.mp ⟨y, h.sphere_subset_six_component hy⟩
  have hsub : A ⊆ thickening δ A := self_subset_thickening h.δ₀_mem.1 A
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℂ
  let : Countable S := hSc.to_subtype
  let G (V : Set ℂ) : Ω → ℂ → ℂ → ℝ≥0∞ := fun ω x y =>
    denseClearanceChainInf S V (fun a b => D ω (a, b)) x y
  have hG (V : Set ℂ) (x y : ℂ) : Measurable[m] (fun ω => G V ω x y) := by
    let : MeasurableSpace Ω := m
    exact measurable_denseClearanceChainInf x y hd (fun ω x =>
      (D ω).continuous.comp (continuous_const.prodMk continuous_id))
  have hGeq (V : Set ℂ) (hV : IsOpen V) : ∀ᵐ ω ∂P, ∀ x ∈ V, ∀ y ∈ V,
      internalMetric (fun a b => D ω (a, b)) V x y = G V ω x y := by
    filter_upwards [hm] with ω hω x hx y hy
    have hn (a b : ℂ) : 0 ≤ D ω (a, b) := by
      have ht := hω.triangle a b a
      rw [hω.self_eq_zero, hω.symm b a] at ht
      linarith
    exact hω.internalMetric_eq_denseClearanceChainInf hn hSd hV hx
  obtain ⟨Y₁, hY₁, heq₁⟩ := @exists_local_iSup_internalMetric_representative Ω mΩ P m
    (fun ω x y => D ω (x, y)) (G F) F {0} (sphere 0 5) hF
    (singleton_subset_iff.mpr hz) hs hm (fun x _ y _ => hG F x y)
    ((hGeq F hF).mono fun _ he x hx y hy => he x ((singleton_subset_iff.mpr hz) hx) y (hs hy))
  obtain ⟨Y₂, hY₂, heq₂⟩ := @exists_local_iSup_internalMetric_representative Ω mΩ P m
    (fun ω x y => D ω (x, y)) (G (thickening δ A)) (thickening δ A) A A isOpen_thickening
    hsub hsub hm (fun x _ y _ => hG (thickening δ A) x y)
    ((hGeq (thickening δ A) isOpen_thickening).mono fun _ he x hx y hy => he x (hsub hx) y (hsub hy))
  have hQ : Q'.Nonempty := h.toIsPinchPointProofConfiguration.toIsPinchPointConfiguration.isConnected_Q'.nonempty
  have hfront : (frontier Q).Nonempty := by
    have hp := h.toIsPinchPointProofConfiguration.toIsPinchPointConfiguration.setDist_frontier_pos isEuclideanLengthMetric_dist
    by_contra hn
    have he : frontier Q = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [he, setDist] at hp
  have hgap : Measurable[m] (fun ω => ENNReal.ofReal (setDist (fun x y => D ω (x, y)) Q' (frontier Q))) := by
    let : MeasurableSpace Ω := m
    exact measurable_ofReal_setDist_of_continuous hQ hfront hd (fun ω => (D ω).continuous)
  have hroot : Measurable[m] (fun ω => ENNReal.ofReal (setDist (fun x y => D ω (x, y)) {0} (sphere 0 δ))) := by
    let : MeasurableSpace Ω := m
    exact measurable_ofReal_setDist_of_continuous (singleton_nonempty (0 : ℂ))
      (NormedSpace.sphere_nonempty (x := (0 : ℂ)) |>.mpr h.δ₀_mem.1.le) hd (fun ω => (D ω).continuous)
  let B : Set Ω := {ω | Y₁ ω < ENNReal.ofReal (setDist (fun x y => D ω (x, y)) Q' (frontier Q)) ∧
    Y₂ ω < ENNReal.ofReal (setDist (fun x y => D ω (x, y)) {0} (sphere 0 δ))}
  have hB : MeasurableSet[m] B := by
    let : MeasurableSpace Ω := m
    exact (measurableSet_lt hY₁ hgap).inter (measurableSet_lt hY₂ hroot)
  obtain ⟨E, hE, he⟩ := MeasurableSpace.measurableSet_comap.mp hB
  refine ⟨E, hE, ?_⟩
  filter_upwards [heq₁, heq₂] with ω h₁ h₂
  have heω : D ω ∈ E ↔ ω ∈ B := by
    change ω ∈ D ⁻¹' E ↔ ω ∈ B
    rw [he]
  rw [heω]
  change _ ↔ (Y₁ ω < _ ∧ Y₂ ω < _)
  simp only [iSup_singleton] at h₁
  rw [h₁, ← h₂]
  rfl

#print axioms IsCorrectedPinchConfiguration.exists_open_first_representative

end HarmonicBalls
