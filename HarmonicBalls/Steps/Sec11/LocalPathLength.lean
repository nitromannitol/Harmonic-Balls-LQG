import HarmonicBalls.Steps.Sec11.ApproximatePaths
import Mathlib.Topology.Subpath

/-!
# Length of restricted paths

These lemmas support localizing metric barriers: an ordered subpath cannot
have greater length than the full path.
-/

namespace HarmonicBalls

open Set Topology Metric
open scoped ENNReal

/-- Restricting the parameter range by an increasing map cannot increase
curve length. -/
theorem curveLength_le_of_monotoneOn_reparam
    (D : ℂ → ℂ → ℝ) (p q : ℝ → ℂ) (φ : ℝ → ℝ)
    (hφ : MonotoneOn φ (Icc (0 : ℝ) 1))
    (hφmem : MapsTo φ (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hpq : ∀ t ∈ Icc (0 : ℝ) 1, q t = p (φ t)) :
    curveLength D q 0 1 ≤ curveLength D p 0 1 := by
  unfold curveLength
  refine iSup_le fun a => ?_
  let v : ℕ → ℝ := fun i => φ (a.2.1 i)
  have hvmono : Monotone v := fun i j hij => hφ (a.2.2.2 i) (a.2.2.2 j) (a.2.2.1 hij)
  have hvmem : ∀ i, v i ∈ Icc (0 : ℝ) 1 := fun i => hφmem (a.2.2.2 i)
  have hle := le_iSup (fun b : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc 0 1} =>
    ∑ i ∈ Finset.range b.1, ENNReal.ofReal (D (p (b.2.1 (i + 1))) (p (b.2.1 i))))
      ⟨a.1, ⟨v, hvmono, hvmem⟩⟩
  apply le_trans ?_ hle
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i hi
  simp only [v, hpq _ (a.2.2.2 _)]

/-- Any ordered subpath has no greater length than the original path. -/
theorem pathLength_subpath_le {x y : ℂ} (D : ℂ → ℂ → ℝ) (p : Path x y)
    (s t : unitInterval) (hst : s ≤ t) :
    pathLength D (p.subpath s t) ≤ pathLength D p := by
  let φ : ℝ → ℝ := fun u => (1 - u) * (s : ℝ) + u * (t : ℝ)
  have hφ : MonotoneOn φ (Icc (0 : ℝ) 1) := by
    intro a ha b hb hab
    dsimp [φ]
    have hst' : (s : ℝ) ≤ t := hst
    nlinarith
  have hφmem : MapsTo φ (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro u hu
    dsimp [φ]
    have hs0 := s.property.1
    have hs1 := s.property.2
    have ht0 := t.property.1
    have ht1 := t.property.2
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) hs0,
      mul_nonneg hu.1 ht0, mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hs1),
      mul_nonneg hu.1 (sub_nonneg.mpr ht1)]
  unfold pathLength
  apply curveLength_le_of_monotoneOn_reparam D p.extend (p.subpath s t).extend φ hφ hφmem
  intro u hu
  rw [Path.extend_apply _ hu, Path.extend_apply _ (hφmem hu)]
  rfl

/-- A path starting in an open set and ending on its frontier has a first
frontier time; before that time it stays in the set. -/
theorem path_first_frontier {x y : ℂ} (p : Path x y) {U : Set ℂ}
    (hU : IsOpen U) (hx : x ∈ U) (hy : y ∈ frontier U) :
    ∃ t : unitInterval, p t ∈ frontier U ∧
      ∀ s : unitInterval, s ≤ t → p s ∈ closure U := by
  let S : Set ℝ := Icc 0 1 ∩ p.extend ⁻¹' frontier U
  have hScompact : IsCompact S := isCompact_Icc.of_isClosed_subset
    (isClosed_Icc.inter (isClosed_frontier.preimage p.continuous_extend)) inter_subset_left
  have hSne : S.Nonempty := ⟨1, ⟨⟨zero_le_one, le_rfl⟩, by simpa using hy⟩⟩
  obtain ⟨t, ht⟩ := hScompact.exists_isLeast hSne
  let t' : unitInterval := ⟨t, ht.1.1⟩
  have htfront : p t' ∈ frontier U := by
    simpa [t', Path.extend_apply _ ht.1.1] using ht.1.2
  refine ⟨t', htfront, ?_⟩
  intro s hst
  by_cases hst' : s = t'
  · subst s
    exact frontier_subset_closure htfront
  · have hlt : (s : ℝ) < t := lt_of_le_of_ne hst (by
      intro heq
      apply hst'
      exact Subtype.ext heq)
    let A : Set ℂ := p.extend '' Icc (0 : ℝ) s
    have hAconn : IsPreconnected A := isPreconnected_Icc.image _ p.continuous_extend.continuousOn
    have hxA : x ∈ A := ⟨0, ⟨le_rfl, s.property.1⟩, p.extend_zero⟩
    have hA_sub : closure U ∩ A ⊆ U := by
      intro v hv
      by_contra hvU
      have hvfront : v ∈ frontier U := by
        rw [hU.frontier_eq]
        exact ⟨hv.1, hvU⟩
      obtain ⟨a, ha, rfl⟩ := hv.2
      have haS : a ∈ S := ⟨⟨ha.1, ha.2.trans s.property.2⟩, hvfront⟩
      have := ht.2 haS
      linarith [ha.2]
    have hAU : A ⊆ U := hAconn.subset_of_closure_inter_subset hU ⟨x, hxA, hx⟩ hA_sub
    have hsA : p s ∈ A := ⟨s, ⟨s.property.1, le_rfl⟩, by rw [Path.extend_apply _ s.property]⟩
    exact subset_closure (hAU hsA)

/-- A path from an open set to its frontier contains an initial path in any
neighborhood of the closure, of no greater length. -/
theorem exists_frontier_subpath {x y : ℂ} (D : ℂ → ℂ → ℝ) (p : Path x y)
    {U V : Set ℂ} (hU : IsOpen U) (hx : x ∈ U) (hy : y ∈ frontier U)
    (hUV : closure U ⊆ V) :
    ∃ y' ∈ frontier U, ∃ q : Path x y', (∀ u, q u ∈ V) ∧
      pathLength D q ≤ pathLength D p := by
  obtain ⟨t, htfront, htinside⟩ := path_first_frontier p hU hx hy
  let q := p.subpath 0 t
  have hq : ∀ u, q u ∈ V := by
    intro u
    have hmem : q u ∈ Set.range q := ⟨u, rfl⟩
    change q u ∈ Set.range (p.subpath 0 t) at hmem
    rw [Path.range_subpath_of_le p 0 t (show (0 : unitInterval) ≤ t from t.property.1)] at hmem
    obtain ⟨v, hv, hvq⟩ := hmem
    rw [← hvq]
    exact hUV (htinside v hv.2)
  have hlen : pathLength D q ≤ pathLength D p := pathLength_subpath_le D p 0 t (show (0 : unitInterval) ≤ t from t.property.1)
  refine ⟨p t, htfront, q.cast p.source.symm rfl, ?_, ?_⟩
  · simpa only [Path.cast_coe] using hq
  · simpa only [pathLength, Path.extend_cast] using hlen


/-- The distance from an interior set to the boundary is determined by the
internal metric of any set containing the closure. -/
theorem iInf_boundary_internalMetric_eq_global
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {A U V : Set ℂ} (hU : IsOpen U) (hAU : A ⊆ U) (hUV : closure U ⊆ V) :
    (⨅ x ∈ A, ⨅ y ∈ frontier U, internalMetric D V x y) =
      ⨅ x ∈ A, ⨅ y ∈ frontier U, ENNReal.ofReal (D x y) := by
  apply le_antisymm
  · refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
    rw [hD.ofReal_eq_internalMetric]
    refine le_iInf fun p => le_iInf fun _ => ?_
    obtain ⟨y', hy', q, hq, hlen⟩ := exists_frontier_subpath D p hU (hAU hx) hy hUV
    exact (iInf_le_of_le x (iInf_le_of_le hx (iInf_le_of_le y'
      (iInf_le_of_le hy' (iInf_le_of_le q (iInf_le _ hq)))))).trans hlen
  · refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
    apply (iInf_le_of_le x (iInf_le_of_le hx (iInf_le_of_le y (iInf_le _ hy)))).trans
    rw [hD.ofReal_eq_internalMetric]
    exact internalMetric_anti D (subset_univ V) x y

/-- For nonempty sets, the extended nonnegative set distance is the infimum
of the extended nonnegative point distances. -/
theorem ofReal_setDist_eq_iInf {D : ℂ → ℂ → ℝ} {A B : Set ℂ}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ENNReal.ofReal (setDist D A B) = ⨅ x ∈ A, ⨅ y ∈ B, ENNReal.ofReal (D x y) := by
  let : Nonempty A := ⟨⟨hA.choose, hA.choose_spec⟩⟩
  let : Nonempty B := ⟨⟨hB.choose, hB.choose_spec⟩⟩
  have himage : image2 D A B = Set.range (fun p : A × B => D p.1 p.2) := by
    ext z
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
    · rintro ⟨⟨x, y⟩, rfl⟩
      exact ⟨x, x.property, y, y.property, rfl⟩
  rw [setDist, himage, sInf_range, ENNReal.ofReal_iInf]
  simp only [iInf_prod, iInf_subtype]

/-- Distance from an interior set to a boundary is determined by the
internal metric on any neighborhood containing the domain closure. -/
theorem ofReal_setDist_boundary_eq_internalMetric
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {A U V : Set ℂ} (hU : IsOpen U) (hAU : A ⊆ U) (hUV : closure U ⊆ V)
    (hA : A.Nonempty) (hfront : (frontier U).Nonempty) :
    ENNReal.ofReal (setDist D A (frontier U)) =
      ⨅ x ∈ A, ⨅ y ∈ frontier U, internalMetric D V x y := by
  rw [ofReal_setDist_eq_iInf hA hfront]
  exact (iInf_boundary_internalMetric_eq_global hD hU hAU hUV).symm

/-- The global distance from the center to the radius-five sphere is
computed by the internal metric of the radius-six ball. -/
theorem ofReal_setDist_center_sphere_eq_internalMetric
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (setDist D {z} (sphere z (5 * r))) =
      ⨅ y ∈ sphere z (5 * r), internalMetric D (ball z (6 * r)) z y := by
  have h5 : 0 < 5 * r := by positivity
  have hfront : frontier (ball z (5 * r)) = sphere z (5 * r) := frontier_ball z h5.ne'
  have hsub : ({z} : Set ℂ) ⊆ ball z (5 * r) := by
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    simpa using h5
  have hclosure : closure (ball z (5 * r)) ⊆ ball z (6 * r) := by
    rw [closure_ball z h5.ne']
    intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball]
    nlinarith
  have hn : (frontier (ball z (5 * r))).Nonempty := by
    rw [hfront]
    exact NormedSpace.sphere_nonempty.mpr h5.le
  have h := ofReal_setDist_boundary_eq_internalMetric hD isOpen_ball hsub hclosure
    (Set.singleton_nonempty z) hn
  rw [hfront] at h
  simpa only [iInf_singleton] using h

end HarmonicBalls
