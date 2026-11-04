import HarmonicBalls.Steps.Sec11.PinchThirdThresholds
import HarmonicBalls.Steps.Sec11.MetricConstantScaling

/-! # Local contraction of internal diameters

A pointwise comparison only on the neighborhood in which paths are measured
is enough to compare internal distances and prove the third auxiliary event.
The hypotheses compare ambient distances between every pair of points in the
neighborhood. A bump being constant there does not by itself establish this
comparison, since distance-minimizing paths may leave the neighborhood.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter
open scoped ENNReal

/-- Comparing distance values inside a set compares lengths of paths contained
in the set. -/
theorem pathLength_le_of_ofReal_le_on {D E : ℂ → ℂ → ℝ} {U : Set ℂ}
    (h : ∀ x ∈ U, ∀ y ∈ U, ENNReal.ofReal (D x y) ≤ ENNReal.ofReal (E x y))
    {x y : ℂ} (p : Path x y) (hp : ∀ t, p t ∈ U) :
    pathLength D p ≤ pathLength E p := by
  have hp' : ∀ t ∈ Icc (0 : ℝ) 1, p.extend t ∈ U := by
    intro t ht
    rw [Path.extend_apply _ ht]
    exact hp ⟨t, ht⟩
  unfold pathLength curveLength
  apply iSup_mono
  intro q
  apply Finset.sum_le_sum
  intro i hi
  exact h _ (hp' _ (q.2.2.2 _)) _ (hp' _ (q.2.2.2 _))

/-- Comparing distance values on a set compares its internal distances. -/
theorem internalMetric_le_of_ofReal_le_on {D E : ℂ → ℂ → ℝ} {U : Set ℂ}
    (h : ∀ x ∈ U, ∀ y ∈ U, ENNReal.ofReal (D x y) ≤ ENNReal.ofReal (E x y))
    (x y : ℂ) : internalMetric D U x y ≤ internalMetric E U x y := by
  unfold internalMetric
  apply iInf_mono
  intro p
  apply iInf_mono
  intro hp
  exact pathLength_le_of_ofReal_le_on h p hp

/-- A positive local contraction of distances contracts the corresponding
internal diameter by the same factor. -/
theorem internalDiam_le_const_mul_of_local_contraction {D E : ℂ → ℂ → ℝ}
    {c δ : ℝ} (hc : 0 < c) (A : Set ℂ)
    (hlocal : ∀ x ∈ thickening δ A, ∀ y ∈ thickening δ A,
      ENNReal.ofReal (E x y) ≤ ENNReal.ofReal (c * D x y)) :
    internalDiam E δ A ≤ ENNReal.ofReal c * internalDiam D δ A := by
  calc
    internalDiam E δ A ≤ internalDiam (fun x y => c * D x y) δ A := by
      unfold internalDiam
      apply iSup_mono
      intro x
      apply iSup_mono
      intro hx
      apply iSup_mono
      intro y
      apply iSup_mono
      intro hy
      exact internalMetric_le_of_ofReal_le_on hlocal x y
    _ = ENNReal.ofReal c * internalDiam D δ A := by
      unfold internalDiam
      simp_rw [internalMetric_const_mul D hc, ENNReal.mul_iSup]

/-- Strict E3 follows from local contraction and preservation of the sphere
separation. Both comparison hypotheses are explicit. -/
theorem pinchThirdEvent_of_local_contraction {D E : ℂ → ℂ → ℝ}
    {c δ : ℝ} (hc : 0 < c) (V W : Set ℂ)
    (hlocal : ∀ x ∈ thickening δ (thickening (3 * δ) W \ V),
      ∀ y ∈ thickening δ (thickening (3 * δ) W \ V),
        ENNReal.ofReal (E x y) ≤ ENNReal.ofReal (c * D x y))
    (hgap : ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) ≤
      ENNReal.ofReal (setDist E (sphere 0 (2 * δ)) (sphere 0 (3 * δ))))
    (hstrict : ENNReal.ofReal c * internalDiam D δ (thickening (3 * δ) W \ V) <
      ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))) :
    pinchThirdEvent E V W δ := by
  exact (internalDiam_le_const_mul_of_local_contraction hc _ hlocal).trans_lt (hstrict.trans_le hgap)

/-- Given local contraction and sphere-separation comparisons for each
positive contraction factor, deterministic threshold selection yields a
factor for which the third auxiliary event has positive mass. -/
theorem IsPinchPointProofConfiguration.exists_positive_measure_thirdEvent_of_local_contraction
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hconfig : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (D : Ω → ℂ → ℂ → ℝ) (E : ℝ → Ω → ℂ → ℂ → ℝ)
    (hA : 0 < P A) (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hcompare : ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ᵐ ω ∂P, ω ∈ A →
      (∀ x ∈ thickening δ (thickening (3 * δ) W \ V),
        ∀ y ∈ thickening δ (thickening (3 * δ) W \ V),
          ENNReal.ofReal (E c ω x y) ≤ ENNReal.ofReal (c * D ω x y)) ∧
      ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) ≤
        ENNReal.ofReal (setDist (E c ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < P {ω | ω ∈ A ∧ pinchThirdEvent (E c ω) V W δ} := by
  obtain ⟨c, hc, hc1, hp⟩ := hconfig.exists_positive_measure_third_contraction P A D hA hmetric
  let B : Set Ω := {ω | ω ∈ A ∧
    ENNReal.ofReal c * internalDiam (D ω) δ (thickening (3 * δ) W \ V) <
      ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}
  let G : Set Ω := {ω | ω ∈ A →
    (∀ x ∈ thickening δ (thickening (3 * δ) W \ V),
      ∀ y ∈ thickening δ (thickening (3 * δ) W \ V),
        ENNReal.ofReal (E c ω x y) ≤ ENNReal.ofReal (c * D ω x y)) ∧
    ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) ≤
      ENNReal.ofReal (setDist (E c ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}
  have heq : B =ᵐ[P] B ∩ G := by
    filter_upwards [hcompare c hc hc1] with ω hω
    have hg : ω ∈ G := hω
    simp only [mem_inter_iff, hg, and_true]
  have hp' : 0 < P (B ∩ G) := by rw [← measure_congr heq]; exact hp
  refine ⟨c, hc, hc1, hp'.trans_le (measure_mono ?_)⟩
  intro ω hω
  have hcomp := hω.2 hω.1.1
  exact ⟨hω.1.1, pinchThirdEvent_of_local_contraction hc V W hcomp.1 hcomp.2 hω.1.2⟩

end HarmonicBalls
