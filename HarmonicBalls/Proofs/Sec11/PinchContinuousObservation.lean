import HarmonicBalls.Steps.Sec11.PinchLocalEvent
import HarmonicBalls.Steps.Sec11.CountableClearanceChains
import HarmonicBalls.Steps.Sec11.PinchGreenMeasurable

/-! # Measurable pinch events from continuous metric observations -/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

/-- For an almost surely Euclidean length metric, the pinch event has an
almost-surely equal representative measurable in the joint observation of
the measure and the continuous distance function. -/
theorem exists_pinchEvent_representative_of_continuous_observation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (D : Ω → C(ℂ × ℂ, ℝ))
    {U T Q V : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q V)
    (M : ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y => D ω (x, y))) :
    ∃ A : Set (Measure ℂ × C(ℂ × ℂ, ℝ)), MeasurableSet A ∧
      ∀ᵐ ω ∂P, (pinchPointEventWithInternalBounds (μ ω) (fun x y => D ω (x, y))
        U T Q V M r z ↔ (μ ω, D ω) ∈ A) := by
  let obs : Ω → Measure ℂ × C(ℂ × ℂ, ℝ) := fun ω => (μ ω, D ω)
  let m := MeasurableSpace.comap obs inferInstance
  have ho : Measurable[m] obs := comap_measurable obs
  have hμ : Measurable[m] μ := measurable_fst.comp ho
  have hd (x y : ℂ) : Measurable[m] (fun ω => D ω (x, y)) :=
    (ContinuousMap.measurable_eval (x, y)).comp (measurable_snd.comp ho)
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℂ
  let : Countable S := hSc.to_subtype
  let G : Ω → ℂ → ℂ → ℝ≥0∞ := fun ω x y =>
    denseClearanceChainInf S (ball z (6 * r)) (fun a b => D ω (a, b)) x y
  have hG (x y : ℂ) : Measurable[m] (fun ω => G ω x y) := by
    let : MeasurableSpace Ω := m
    exact measurable_denseClearanceChainInf x y hd (fun ω x =>
      (D ω).continuous.comp (continuous_const.prodMk continuous_id))
  have hGeq : ∀ᵐ ω ∂P, ∀ x ∈ ball z (6 * r), ∀ y ∈ ball z (6 * r),
      internalMetric (fun a b => D ω (a, b)) (ball z (6 * r)) x y = G ω x y := by
    filter_upwards [hD] with ω hω x hx y hy
    have hnonneg (a b : ℂ) : 0 ≤ D ω (a, b) := by
      have h := hω.triangle a b a
      rw [hω.self_eq_zero, hω.symm b a] at h
      linarith
    exact hω.internalMetric_eq_denseClearanceChainInf hnonneg hSd isOpen_ball hx
  have hg : Measurable[m] (fun ω => annulusGreenPotentialSup (μ ω) z (3 * r) (6 * r)) :=
    (measurable_annulusGreenPotentialSup z (3 * r) (6 * r)).comp hμ
  have hmass : Measurable[m] (fun ω => μ ω (rescaledSet U r z)) :=
    (Measure.measurable_coe (isOpen_rescaledSet hconfig.isOpen_U (ne_of_gt hr) z).measurableSet).comp hμ
  obtain ⟨E, hE, hEq⟩ := @exists_local_pinchEvent_representative Ω mΩ P m
    (fun ω x y => D ω (x, y)) μ G U T Q V hconfig M z r hr hD hG hGeq
    ⟨_, hg, Filter.Eventually.of_forall fun _ => rfl⟩
    ⟨_, hmass, Filter.Eventually.of_forall fun _ => rfl⟩
  obtain ⟨A, hA, hAE⟩ := MeasurableSpace.measurableSet_comap.mp hE
  refine ⟨A, hA, ?_⟩
  filter_upwards [hEq] with ω hω
  simpa only [← hAE, mem_preimage, obs] using hω

#print axioms exists_pinchEvent_representative_of_continuous_observation

end HarmonicBalls
