import HarmonicBalls.Steps.Sec11.PinchShortEdgeContraction

/-! # Uniform short-edge estimates on compact sets

A local two-point comparison on neighborhoods of a compact path yields one
short-edge threshold for that path.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter
open scoped ENNReal

private structure ComparisonPoint where
  val : ℂ

/-- Local two-point comparisons give a common short-edge threshold on a
compact set for any Euclidean length metric. -/
theorem IsEuclideanLengthMetric.exists_uniform_short_edge_comparison
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {K : Set ℂ}
    (hK : IsCompact K) (c : ℝ)
    (hlocal : ∀ x ∈ K, ∃ r : ℝ, 0 < r ∧ ∀ y z,
      D x y < r → D x z < r → E y z ≤ c * D y z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∀ y, D x y < ε → E x y ≤ c * D x y := by
  classical
  let : MetricSpace ComparisonPoint := {
    dist := fun x y => D x.val y.val
    dist_self := fun x => hD.self_eq_zero x.val
    dist_comm := fun x y => hD.symm x.val y.val
    dist_triangle := fun x y z => hD.triangle x.val y.val z.val
    eq_of_dist_eq_zero := by
      intro ⟨x⟩ ⟨y⟩ h
      exact congrArg ComparisonPoint.mk (hD.eq_of_eq_zero x y h) }
  have hmk : Continuous (fun x : ℂ => (⟨x⟩ : ComparisonPoint)) := by
    rw [Metric.continuous_iff]
    intro x ε hε
    obtain ⟨δ, hδ, hbound⟩ := (Metric.continuous_iff.mp (hD.continuous_left x)) x ε hε
    refine ⟨δ, hδ, ?_⟩
    intro y hy
    have h := hbound y hy
    simp only [hD.self_eq_zero, Real.dist_eq, sub_zero] at h
    change D y x < ε
    exact lt_of_le_of_lt (le_abs_self _) h
  let K' : Set ComparisonPoint := (fun x : ℂ => (⟨x⟩ : ComparisonPoint)) '' K
  have hK' : IsCompact K' := hK.image hmk
  let r : K → ℝ := fun x => Classical.choose (hlocal x x.property)
  have hr : ∀ x : K, 0 < r x ∧ ∀ y z,
      D x y < r x → D x z < r x → E y z ≤ c * D y z := by
    intro x
    exact Classical.choose_spec (hlocal x x.property)
  let C : K → Set ComparisonPoint := fun x => ball ⟨x.1⟩ (r x)
  have hcover : K' ⊆ ⋃ x : K, C x := by
    rintro _ ⟨x, hx, rfl⟩
    apply mem_iUnion.mpr
    refine ⟨⟨x, hx⟩, ?_⟩
    change D x x < r ⟨x, hx⟩
    rw [hD.self_eq_zero]
    exact (hr ⟨x, hx⟩).1
  obtain ⟨ε, hε, hLeb⟩ := lebesgue_number_lemma_of_metric hK'
    (fun x : K => isOpen_ball) hcover
  refine ⟨ε, hε, ?_⟩
  intro x hx y hxy
  obtain ⟨z, hz⟩ := hLeb ⟨x⟩ ⟨x, hx, rfl⟩
  have hxc : (⟨x⟩ : ComparisonPoint) ∈ C z := hz (mem_ball_self hε)
  have hyc : (⟨y⟩ : ComparisonPoint) ∈ C z := by
    apply hz
    change D y x < ε
    simpa only [hD.symm y x] using hxy
  change D x z.1 < r z at hxc
  change D y z.1 < r z at hyc
  exact (hr z).2 x y (by simpa only [hD.symm x z.1] using hxc)
    (by simpa only [hD.symm y z.1] using hyc)

/-- Local two-point estimates on an open set give pathwise short-edge
estimates, with a common threshold for each individual path. -/
theorem IsEuclideanLengthMetric.path_short_edge_comparison_of_local
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {U : Set ℂ} (c : ℝ)
    (hlocal : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ ∀ y z,
      D x y < r → D x z < r → E y z ≤ c * D y z)
    {x y : ℂ} (p : Path x y) (hp : ∀ t, p t ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      D (p.extend s) (p.extend t) < r →
        E (p.extend s) (p.extend t) ≤ c * D (p.extend s) (p.extend t) := by
  have hK : IsCompact (range p) := isCompact_range p.continuous
  have hlocal' : ∀ x ∈ range p, ∃ r : ℝ, 0 < r ∧ ∀ y z,
      D x y < r → D x z < r → E y z ≤ c * D y z := by
    rintro x ⟨t, rfl⟩
    exact hlocal (p t) (hp t)
  obtain ⟨r, hr, hbound⟩ := hD.exists_uniform_short_edge_comparison hK c hlocal'
  refine ⟨r, hr, ?_⟩
  intro s hs t ht hdist
  apply hbound (p.extend s) ?_ (p.extend t) hdist
  exact ⟨⟨s, hs⟩, (Path.extend_apply _ hs).symm⟩

/-- Local two-point comparison implies contraction of the internal diameter. -/
theorem IsEuclideanLengthMetric.internalDiam_le_const_mul_of_local_comparison
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hEnonneg : ∀ x y, 0 ≤ E x y)
    {c δ : ℝ} (hc : 0 < c) (A : Set ℂ)
    (hlocal : ∀ x ∈ thickening δ A, ∃ r : ℝ, 0 < r ∧ ∀ y z,
      D x y < r → D x z < r → E y z ≤ c * D y z) :
    internalDiam E δ A ≤ ENNReal.ofReal c * internalDiam D δ A := by
  apply hD.internalDiam_le_const_mul_of_short_edges hE hEnonneg hc A
  intro x y p hp
  exact hD.path_short_edge_comparison_of_local c hlocal p hp

/-- A local two-point contraction, a sphere-gap comparison, and a strict
margin imply the third auxiliary pinch event. -/
theorem IsEuclideanLengthMetric.pinchThirdEvent_of_local_comparison
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hEnonneg : ∀ x y, 0 ≤ E x y)
    {c δ : ℝ} (hc : 0 < c) (V W : Set ℂ)
    (hlocal : ∀ x ∈ thickening δ (thickening (3 * δ) W \ V),
      ∃ r : ℝ, 0 < r ∧ ∀ y z, D x y < r → D x z < r → E y z ≤ c * D y z)
    (hgap : ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) ≤
      ENNReal.ofReal (setDist E (sphere 0 (2 * δ)) (sphere 0 (3 * δ))))
    (hstrict : ENNReal.ofReal c * internalDiam D δ (thickening (3 * δ) W \ V) <
      ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))) :
    pinchThirdEvent E V W δ := by
  exact (hD.internalDiam_le_const_mul_of_local_comparison hE hEnonneg hc _ hlocal).trans_lt
    (hstrict.trans_le hgap)

/-- If each candidate contraction admits the local metric and sphere-gap
comparisons almost surely on a positive-mass event, one deterministic factor
makes the third auxiliary event occur on a positive-mass subevent. -/
theorem IsPinchPointProofConfiguration.exists_positive_measure_thirdEvent_of_local_comparison
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hconfig : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (D : Ω → ℂ → ℂ → ℝ) (E : ℝ → Ω → ℂ → ℂ → ℝ)
    (hA : 0 < P A) (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hcompare : ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ᵐ ω ∂P, ω ∈ A →
      IsEuclideanLengthMetric (D ω) ∧ IsEuclideanLengthMetric (E c ω) ∧
      (∀ x y, 0 ≤ E c ω x y) ∧
      (∀ x ∈ thickening δ (thickening (3 * δ) W \ V), ∃ r : ℝ, 0 < r ∧ ∀ y z,
        D ω x y < r → D ω x z < r → E c ω y z ≤ c * D ω y z) ∧
      ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) ≤
        ENNReal.ofReal (setDist (E c ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < P {ω | ω ∈ A ∧ pinchThirdEvent (E c ω) V W δ} := by
  obtain ⟨c, hc, hc1, hp⟩ := hconfig.exists_positive_measure_third_contraction P A D hA hmetric
  let B : Set Ω := {ω | ω ∈ A ∧
    ENNReal.ofReal c * internalDiam (D ω) δ (thickening (3 * δ) W \ V) <
      ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}
  let G : Set Ω := {ω | ω ∈ A →
    IsEuclideanLengthMetric (D ω) ∧ IsEuclideanLengthMetric (E c ω) ∧
    (∀ x y, 0 ≤ E c ω x y) ∧
    (∀ x ∈ thickening δ (thickening (3 * δ) W \ V), ∃ r : ℝ, 0 < r ∧ ∀ y z,
      D ω x y < r → D ω x z < r → E c ω y z ≤ c * D ω y z) ∧
    ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) ≤
      ENNReal.ofReal (setDist (E c ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}
  have heq : B =ᵐ[P] B ∩ G := by
    filter_upwards [hcompare c hc hc1] with ω hω
    have hg : ω ∈ G := hω
    simp only [mem_inter_iff, hg, and_true]
  have hp' : 0 < P (B ∩ G) := by rw [← measure_congr heq]; exact hp
  refine ⟨c, hc, hc1, hp'.trans_le (measure_mono ?_)⟩
  intro ω hω
  obtain ⟨hD, hE, hEnonneg, hlocal, hgap⟩ := hω.2 hω.1.1
  exact ⟨hω.1.1, hD.pinchThirdEvent_of_local_comparison hE hEnonneg hc V W hlocal hgap hω.1.2⟩

end HarmonicBalls
