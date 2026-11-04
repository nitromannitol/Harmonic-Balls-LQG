import HarmonicBalls.Steps.Sec11.InternalMetricNear

/-! # Reversal of paths -/

namespace HarmonicBalls

open Set
open scoped ENNReal

/-- Reversing the parameter of a curve preserves its variation. -/
theorem eVariationOn_unitInterval_reverse {E : Type*} [PseudoEMetricSpace E]
    (f : ℝ → E) :
    eVariationOn (f ∘ fun t : ℝ => 1 - t) (Icc (0 : ℝ) 1) =
      eVariationOn f (Icc (0 : ℝ) 1) := by
  have hanti : AntitoneOn (fun t : ℝ => 1 - t) (Icc 0 1) := by
    intro a ha b hb hab
    linarith
  have himage : (fun t : ℝ => 1 - t) '' Icc 0 1 = Icc 0 1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      constructor <;> linarith [ht.1, ht.2]
    · intro hx
      refine ⟨1 - x, ?_, by ring⟩
      constructor <;> linarith [hx.1, hx.2]
  rw [eVariationOn.comp_eq_of_antitoneOn f _ hanti, himage]

/-- Variation of a curve obtained by traversing two curves in succession. -/
theorem eVariationOn_concat_le {E : Type*} [PseudoEMetricSpace E]
    (f g h : ℝ → E)
    (hleft : EqOn f (g ∘ fun t : ℝ => 2 * t) (Icc (0 : ℝ) (1 / 2)))
    (hright : EqOn f (h ∘ fun t : ℝ => 2 * t - 1) (Icc (1 / 2 : ℝ) 1)) :
    eVariationOn f (Icc (0 : ℝ) 1) ≤
      eVariationOn g (Icc (0 : ℝ) 1) + eVariationOn h (Icc (0 : ℝ) 1) := by
  have hsplit : eVariationOn f (Icc (0 : ℝ) (1 / 2)) +
      eVariationOn f (Icc (1 / 2 : ℝ) 1) = eVariationOn f (Icc (0 : ℝ) 1) := by
    simpa only [univ_inter] using eVariationOn.Icc_add_Icc f (s := univ)
      (a := (0 : ℝ)) (b := 1 / 2) (c := 1) (by norm_num) (by norm_num) (mem_univ _)
  have hleftle : eVariationOn f (Icc (0 : ℝ) (1 / 2)) ≤ eVariationOn g (Icc (0 : ℝ) 1) := by
    rw [eVariationOn.eq_of_eqOn hleft]
    apply eVariationOn.comp_le_of_monotoneOn g (fun t : ℝ => 2 * t)
    · intro a ha b hb hab
      linarith
    · intro a ha
      constructor <;> linarith [ha.1, ha.2]
  have hrightle : eVariationOn f (Icc (1 / 2 : ℝ) 1) ≤ eVariationOn h (Icc (0 : ℝ) 1) := by
    rw [eVariationOn.eq_of_eqOn hright]
    apply eVariationOn.comp_le_of_monotoneOn h (fun t : ℝ => 2 * t - 1)
    · intro a ha b hb hab
      linarith
    · intro a ha
      constructor <;> linarith [ha.1, ha.2]
  exact hsplit.symm.le.trans (add_le_add hleftle hrightle)

private structure LengthPoint where
  val : ℂ

/-- Reversing a path preserves its length. -/
theorem IsEuclideanLengthMetric.pathLength_symm
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {x y : ℂ} (p : Path x y) :
    pathLength D p.symm = pathLength D p := by
  let : MetricSpace LengthPoint := {
    dist := fun x y => D x.val y.val
    dist_self := fun x => hD.self_eq_zero x.val
    dist_comm := fun x y => hD.symm x.val y.val
    dist_triangle := fun x y z => hD.triangle x.val y.val z.val
    eq_of_dist_eq_zero := by
      intro ⟨u⟩ ⟨v⟩ h
      exact congrArg LengthPoint.mk (hD.eq_of_eq_zero u v h) }
  have hcurve (f : ℝ → ℂ) (a b : ℝ) :
      curveLength D f a b = eVariationOn (fun t => (⟨f t⟩ : LengthPoint)) (Icc a b) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  let f : ℝ → LengthPoint := fun t => ⟨p.extend t⟩
  have heq : EqOn (fun t => (⟨p.symm.extend t⟩ : LengthPoint))
      (f ∘ fun t : ℝ => 1 - t) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact congrArg LengthPoint.mk (Path.extend_symm_apply p t)
  calc
    pathLength D p.symm = eVariationOn (fun t => (⟨p.symm.extend t⟩ : LengthPoint))
        (Icc (0 : ℝ) 1) := hcurve _ _ _
    _ = eVariationOn (f ∘ fun t : ℝ => 1 - t) (Icc (0 : ℝ) 1) :=
      eVariationOn.eq_of_eqOn heq
    _ = eVariationOn f (Icc (0 : ℝ) 1) := eVariationOn_unitInterval_reverse f
    _ = pathLength D p := (hcurve _ _ _).symm

/-- Concatenation has length at most the sum of the two path lengths. -/
theorem IsEuclideanLengthMetric.pathLength_trans_le
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {x y z : ℂ} (p : Path x y) (q : Path y z) :
    pathLength D (p.trans q) ≤ pathLength D p + pathLength D q := by
  let : MetricSpace LengthPoint := {
    dist := fun x y => D x.val y.val
    dist_self := fun x => hD.self_eq_zero x.val
    dist_comm := fun x y => hD.symm x.val y.val
    dist_triangle := fun x y z => hD.triangle x.val y.val z.val
    eq_of_dist_eq_zero := by
      intro ⟨u⟩ ⟨v⟩ h
      exact congrArg LengthPoint.mk (hD.eq_of_eq_zero u v h) }
  have hcurve (f : ℝ → ℂ) (a b : ℝ) :
      curveLength D f a b = eVariationOn (fun t => (⟨f t⟩ : LengthPoint)) (Icc a b) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  let f : ℝ → LengthPoint := fun t => ⟨(p.trans q).extend t⟩
  let g : ℝ → LengthPoint := fun t => ⟨p.extend t⟩
  let h : ℝ → LengthPoint := fun t => ⟨q.extend t⟩
  have hleft : EqOn f (g ∘ fun t : ℝ => 2 * t) (Icc (0 : ℝ) (1 / 2)) := by
    intro t ht
    exact congrArg LengthPoint.mk (Path.extend_trans_of_le_half p q ht.2)
  have hright : EqOn f (h ∘ fun t : ℝ => 2 * t - 1) (Icc (1 / 2 : ℝ) 1) := by
    intro t ht
    exact congrArg LengthPoint.mk (Path.extend_trans_of_half_le p q ht.1)
  calc
    pathLength D (p.trans q) = eVariationOn f (Icc (0 : ℝ) 1) := hcurve _ _ _
    _ ≤ eVariationOn g (Icc (0 : ℝ) 1) + eVariationOn h (Icc (0 : ℝ) 1) :=
      eVariationOn_concat_le f g h hleft hright
    _ = pathLength D p + pathLength D q := congrArg₂ (· + ·) (hcurve _ _ _).symm (hcurve _ _ _).symm

/-- Internal distance is symmetric, including between distinct path components. -/
theorem IsEuclideanLengthMetric.internalMetric_symm
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (U : Set ℂ) (x y : ℂ) : internalMetric D U x y = internalMetric D U y x := by
  have hle (a b : ℂ) : internalMetric D U a b ≤ internalMetric D U b a := by
    unfold internalMetric
    refine le_iInf₂ fun p hp => ?_
    have hp' : ∀ t, p.symm t ∈ U := by
      intro t
      simp only [Path.symm_apply, Function.comp_apply]
      exact hp _
    exact (iInf_le_of_le p.symm (iInf_le _ hp')).trans_eq (hD.pathLength_symm p)
  exact le_antisymm (hle x y) (hle y x)

/-- The internal metric satisfies the triangle inequality, also when infinite. -/
theorem IsEuclideanLengthMetric.internalMetric_triangle
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (U : Set ℂ) (x y z : ℂ) :
    internalMetric D U x z ≤ internalMetric D U x y + internalMetric D U y z := by
  simp only [internalMetric, ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf₂ fun q hq => le_iInf₂ fun p hp => ?_
  have hpq : ∀ t, (p.trans q) t ∈ U := by
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact hp _
    · exact hq _
  exact (iInf_le_of_le (p.trans q) (iInf_le _ hpq)).trans (hD.pathLength_trans_le p q)

end HarmonicBalls
