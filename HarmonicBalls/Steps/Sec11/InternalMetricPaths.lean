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

end HarmonicBalls
