import HarmonicBalls.Steps.Sec11.InternalMetricContinuity
import HarmonicBalls.FirstPass.S11j.CertificateE1
import HarmonicBalls.FirstPass.S11h.OuterDiamFinite

/-!
# First pass, Lemma 11.17: the closed corridor is continuous on an open set inside it (fp-S11h, owner n2)

Coordinate 0 of `pinchScalars` is `⨆ y ∈ ∂B₅, D(0, y; C)` for the closed corridor `C = (B_{2δ}(Q ∪ W))ᶜ`
(Draft/Section11.lean lines 95-96; paper eq:first-event, line 3257). Here `C` is only a closed set, so
`D(·, ·; C)` is not a field-level decoder by itself; the formula `internalMetric_closed_eq_iInf_iSup` of
CHATGPT-cm-field-certificate.md (section 3.3) reduces it to open sets (NEW analytic step, not in this file).

This file proves the deterministic continuity part, which needs no closedness: for an open set `O ⊆ C`, the map
`y ↦ D(x, y; C)` is continuous on `O` (triangle inequality on `C`, and `D(·, · ; C) ≤ D(·, · ; O)` by monotonicity in the
set, Defs/LQGMetric.lean `internalMetric_anti`). Hence, for an open `O ⊆ C` containing the sphere `∂B_r`, the supremum
over the sphere is a supremum over a countable dense subset of the sphere (`iSup_sphere_eq_countable_of_subset`).
Source: the argument of Steps/Sec11/InternalMetricContinuity.lean (`continuousAt_internalMetric`), with `C` in place of `U`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

/-- For an open set `O` contained in a set `C`, the internal metric of `C` from a fixed point `x` is continuous at each
point of `O`: `D(x, t; C) ≤ D(x, y; C) + D(y, t; O)` and `D(x, y; C) ≤ D(x, t; C) + D(t, y; O)`, and `D(·, ·; O)` is
jointly continuous near `(y, y)` with value `0` on the diagonal. -/
theorem IsEuclideanLengthMetric.continuousAt_internalMetric_of_subset {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {C O : Set ℂ} (hO : IsOpen O) (hOC : O ⊆ C) (x : ℂ) {y : ℂ} (hy : y ∈ O) :
    ContinuousAt (fun t => internalMetric D C x t) y := by
  have hnonneg := hD.nonneg_apply
  have hself : internalMetric D O y y = 0 := hD.internalMetric_self_of_mem_open hnonneg hO hy
  have hdelta : Tendsto (fun t => internalMetric D O y t) (𝓝 y) (𝓝 0) := by
    have hh := hD.continuousAt_internalMetric_self hnonneg hO hy
    change Tendsto (fun t => internalMetric D O y t) (𝓝 y) (𝓝 (internalMetric D O y y)) at hh
    rw [hself] at hh
    exact hh
  have hadd (a : ℝ≥0∞) : Tendsto (fun t => a + internalMetric D O y t) (𝓝 y) (𝓝 a) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hdelta :
      Tendsto (fun t => a + internalMetric D O y t) (𝓝 y) (𝓝 (a + 0)))
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [(hadd a).eventually_lt_const ha] with t ht
    have htri := hD.internalMetric_triangle C x t y
    have hty : internalMetric D C t y ≤ internalMetric D O t y := internalMetric_anti D hOC t y
    rw [hD.internalMetric_symm O t y] at hty
    by_contra hnot
    have hle : internalMetric D C x t ≤ a := le_of_not_gt hnot
    have := add_le_add hle hty
    exact (not_le_of_gt ht) (htri.trans this)
  · intro a ha
    filter_upwards [(hadd (internalMetric D C x y)).eventually_lt_const ha] with t ht
    exact lt_of_le_of_lt ((hD.internalMetric_triangle C x y t).trans
      (add_le_add le_rfl (internalMetric_anti D hOC y t))) ht

/-- Continuity of `y ↦ D(x, y; C)` on an open set `O ⊆ C` (pointwise statement of
`continuousAt_internalMetric_of_subset`). -/
theorem IsEuclideanLengthMetric.continuousOn_internalMetric_of_subset {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {C O : Set ℂ} (hO : IsOpen O) (hOC : O ⊆ C) (x : ℂ) :
    ContinuousOn (fun t => internalMetric D C x t) O :=
  fun _ hy => (hD.continuousAt_internalMetric_of_subset hO hOC x hy).continuousWithinAt

/-- A countable subset of the sphere `∂B_r` which is dense in it. -/
theorem exists_countable_subset_sphere_dense (r : ℝ) :
    ∃ S : Set ℂ, S ⊆ sphere (0 : ℂ) r ∧ S.Countable ∧ sphere (0 : ℂ) r ⊆ closure S := by
  obtain ⟨s, hs, hdense⟩ := TopologicalSpace.exists_countable_dense (sphere (0 : ℂ) r)
  refine ⟨Subtype.val '' s, ?_, hs.image _, ?_⟩
  · rintro _ ⟨p, _, rfl⟩
    exact p.2
  · intro y hy
    have hmem : (⟨y, hy⟩ : sphere (0 : ℂ) r) ∈ closure s := hdense.closure_eq ▸ mem_univ _
    exact (closure_subtype.1 hmem)

/-- The supremum over the sphere `∂B_r` of `D(x, ·; C)` equals the supremum over a countable dense subset, when
the sphere lies in an open set `O ⊆ C`. -/
theorem iSup_sphere_eq_countable_of_subset {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {C O : Set ℂ} (hO : IsOpen O) (hOC : O ⊆ C) (r : ℝ) (hsph : sphere (0 : ℂ) r ⊆ O) (x : ℂ) :
    ∃ S : Set ℂ, S ⊆ sphere (0 : ℂ) r ∧ S.Countable ∧
      (⨆ y ∈ sphere (0 : ℂ) r, internalMetric D C x y) = ⨆ y ∈ S, internalMetric D C x y := by
  obtain ⟨S, hSK, hSc, hKS⟩ := exists_countable_subset_sphere_dense r
  exact ⟨S, hSK, hSc, iSup_eq_iSup_of_dense_of_continuousOn hO hsph hSK hKS
    (hD.continuousOn_internalMetric_of_subset hO hOC x)⟩

end HarmonicBalls
