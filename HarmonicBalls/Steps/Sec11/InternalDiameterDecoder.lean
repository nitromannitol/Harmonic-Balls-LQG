import HarmonicBalls.Steps.Sec11.CountableClearanceChains
import HarmonicBalls.Steps.Sec11.InternalMetricContinuity

/-! # A common measurable decoder for internal diameters

Countable clearance chains give a measurable observable on the entire space
of continuous distance functions. On Euclidean length metrics it equals the
internal diameter of any fixed subset of the open domain.
-/

namespace HarmonicBalls

open Set MeasureTheory Filter Topology
open scoped ENNReal

/-- The internal diameter over a subset equals the supremum over a dense
subset, provided the set lies in the open internal domain. -/
theorem IsEuclideanLengthMetric.iSup_internalMetric_eq_of_dense_subset
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U K Q : Set ℂ} (hU : IsOpen U)
    (hKU : K ⊆ U) (hQK : Q ⊆ K) (hKQ : K ⊆ closure Q) :
    (⨆ x ∈ K, ⨆ y ∈ K, internalMetric D U x y) =
      ⨆ x ∈ Q, ⨆ y ∈ Q, internalMetric D U x y := by
  apply le_antisymm
  · refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
    obtain ⟨qx, hqx, hqxt⟩ := mem_closure_iff_seq_limit.mp (hKQ hx)
    obtain ⟨qy, hqy, hqyt⟩ := mem_closure_iff_seq_limit.mp (hKQ hy)
    have ht := (hD.continuousAt_internalMetric_pair hnonneg hU (hKU hx) (hKU hy)).tendsto.comp
      (hqxt.prodMk_nhds hqyt)
    apply le_of_tendsto ht
    filter_upwards [] with n
    exact le_iSup_of_le (qx n) (le_iSup_of_le (hqx n)
      (le_iSup_of_le (qy n) (le_iSup_of_le (hqy n) le_rfl)))
  · refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
    exact le_iSup_of_le x (le_iSup_of_le (hQK hx)
      (le_iSup_of_le y (le_iSup_of_le (hQK hy) le_rfl)))

/-- There is one measurable internal-diameter decoder for all continuous
Euclidean length metrics, independent of the probability realization. -/
theorem exists_measurable_internalDiameter_decoder {U K : Set ℂ}
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ F : C(ℂ × ℂ, ℝ) → ℝ≥0∞, Measurable F ∧
      ∀ (D : C(ℂ × ℂ, ℝ)), IsEuclideanLengthMetric (fun x y => D (x, y)) →
        F D = ⨆ x ∈ K, ⨆ y ∈ K, internalMetric (fun x y => D (x, y)) U x y := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℂ
  obtain ⟨Q, hQc, hQK, hKQ⟩ := TopologicalSpace.exists_countable_dense_subset K
  let : Countable S := hSc.to_subtype
  let : Countable Q := hQc.to_subtype
  let F : C(ℂ × ℂ, ℝ) → ℝ≥0∞ := fun D =>
    ⨆ x : Q, ⨆ y : Q, denseClearanceChainInf S U (fun x y => D (x, y)) x y
  have hm (x y : ℂ) : Measurable fun D : C(ℂ × ℂ, ℝ) =>
      denseClearanceChainInf S U (fun x y => D (x, y)) x y :=
    measurable_denseClearanceChainInf x y
      (fun x y => (continuous_eval_const (x, y)).measurable)
      (fun D x => D.continuous.comp (continuous_const.prodMk continuous_id))
  refine ⟨F, Measurable.iSup fun x => Measurable.iSup fun y => hm x y, ?_⟩
  intro D hD
  have hnonneg (x y : ℂ) : 0 ≤ D (x, y) := by
    have ht := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at ht
    linarith
  have heq (x y : Q) : denseClearanceChainInf S U (fun x y => D (x, y)) x y =
      internalMetric (fun x y => D (x, y)) U x y :=
    (hD.internalMetric_eq_denseClearanceChainInf hnonneg hSd hU (hKU (hQK x.property))).symm
  change (⨆ x : Q, ⨆ y : Q, denseClearanceChainInf S U (fun x y => D (x, y)) x y) = _
  simp_rw [heq]
  simp only [iSup_subtype]
  exact (hD.iSup_internalMetric_eq_of_dense_subset hnonneg hU hKU hQK hKQ).symm


end HarmonicBalls
