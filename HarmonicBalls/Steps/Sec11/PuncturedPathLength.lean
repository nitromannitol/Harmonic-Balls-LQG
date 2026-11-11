import HarmonicBalls.Steps.Sec11.LocalPathLength
import HarmonicBalls.Steps.Sec11.InternalMetricPaths

/-! # Length of two ordered subpaths

This supplies the length estimate for replacing a middle segment by a
detour around a puncture.
-/

namespace HarmonicBalls

open Set
open scoped ENNReal NNReal

private structure LengthPoint where
  val : ℂ

/-- The sum of the lengths of the initial and final subpaths separated by
an ordered interval does not exceed the length of the original path. -/
theorem IsEuclideanLengthMetric.pathLength_initial_add_final_le
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {x y : ℂ} (p : Path x y) (s t : unitInterval) (hst : s ≤ t) :
    pathLength D (p.subpath 0 s) + pathLength D (p.subpath t 1) ≤ pathLength D p := by
  let : MetricSpace LengthPoint := {
    dist := fun a b => D a.val b.val
    dist_self := fun a => hD.self_eq_zero a.val
    dist_comm := fun a b => hD.symm a.val b.val
    dist_triangle := fun a b c => hD.triangle a.val b.val c.val
    eq_of_dist_eq_zero := by
      intro ⟨a⟩ ⟨b⟩ h
      exact congrArg LengthPoint.mk (hD.eq_of_eq_zero a b h) }
  have hcurve (g : ℝ → ℂ) (a b : ℝ) :
      curveLength D g a b = eVariationOn (fun u => (⟨g u⟩ : LengthPoint)) (Icc a b) := by
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  let f : ℝ → LengthPoint := fun u => ⟨p.extend u⟩
  have hseg (a b : unitInterval) (hab : a ≤ b) :
      pathLength D (p.subpath a b) ≤ eVariationOn f (Icc (a : ℝ) (b : ℝ)) := by
    let φ : ℝ → ℝ := fun u => (1 - u) * (a : ℝ) + u * (b : ℝ)
    have hφ : MonotoneOn φ (Icc (0 : ℝ) 1) := by
      intro u hu v hv huv
      dsimp [φ]
      have hab' : (a : ℝ) ≤ b := hab
      nlinarith
    have hφmem : MapsTo φ (Icc (0 : ℝ) 1) (Icc (a : ℝ) (b : ℝ)) := by
      intro u hu
      dsimp [φ]
      have hab' : (a : ℝ) ≤ b := hab
      constructor <;> nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hab'),
        mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hab')]
    have hφunit : MapsTo φ (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
      intro u hu
      have h := hφmem hu
      exact ⟨a.property.1.trans h.1, h.2.trans b.property.2⟩
    have heq : EqOn (fun u => (⟨(p.subpath a b).extend u⟩ : LengthPoint))
        (f ∘ φ) (Icc (0 : ℝ) 1) := by
      intro u hu
      dsimp only [Function.comp_apply, f]
      apply congrArg LengthPoint.mk
      rw [Path.extend_apply _ hu, Path.extend_apply _ (hφunit hu)]
      rfl
    calc
      pathLength D (p.subpath a b) = eVariationOn
          (fun u => (⟨(p.subpath a b).extend u⟩ : LengthPoint)) (Icc (0 : ℝ) 1) :=
        hcurve _ _ _
      _ = eVariationOn (f ∘ φ) (Icc (0 : ℝ) 1) := eVariationOn.eq_of_eqOn heq
      _ ≤ eVariationOn f (Icc (a : ℝ) (b : ℝ)) :=
        eVariationOn.comp_le_of_monotoneOn f φ hφ hφmem
  have hleft := hseg 0 s (show (0 : unitInterval) ≤ s from s.property.1)
  have hright := hseg t 1 (show t ≤ (1 : unitInterval) from t.property.2)
  have hmono : eVariationOn f (Icc (0 : ℝ) (s : ℝ)) ≤ eVariationOn f (Icc (0 : ℝ) (t : ℝ)) :=
    eVariationOn.mono f (Icc_subset_Icc le_rfl (show (s : ℝ) ≤ t from hst))
  have hsplit : eVariationOn f (Icc (0 : ℝ) (t : ℝ)) +
      eVariationOn f (Icc (t : ℝ) 1) = eVariationOn f (Icc (0 : ℝ) 1) := by
    simpa only [univ_inter] using eVariationOn.Icc_add_Icc f (s := univ)
      (a := (0 : ℝ)) (b := (t : ℝ)) (c := 1) t.property.1 t.property.2 (mem_univ _)
  calc
    pathLength D (p.subpath 0 s) + pathLength D (p.subpath t 1) ≤
        eVariationOn f (Icc (0 : ℝ) (s : ℝ)) + eVariationOn f (Icc (t : ℝ) 1) :=
      add_le_add hleft hright
    _ ≤ eVariationOn f (Icc (0 : ℝ) (t : ℝ)) + eVariationOn f (Icc (t : ℝ) 1) :=
      add_le_add hmono le_rfl
    _ = eVariationOn f (Icc (0 : ℝ) 1) := hsplit
    _ = pathLength D p := (hcurve _ _ _).symm

/-- Replacing a middle subpath by a path in `U` costs at most the original
path length plus the length of the replacement. -/
theorem IsEuclideanLengthMetric.internalMetric_le_of_middle_detour
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {U : Set ℂ}
    {x y : ℂ} (p : Path x y) (s t : unitInterval) (hst : s ≤ t)
    (q : Path (p s) (p t))
    (hfirst : ∀ u, (p.subpath 0 s) u ∈ U)
    (hlast : ∀ u, (p.subpath t 1) u ∈ U)
    (hdetour : ∀ u, q u ∈ U) :
    internalMetric D U x y ≤ pathLength D p + pathLength D q := by
  let a : Path x (p s) := (p.subpath 0 s).cast p.source.symm rfl
  let b : Path (p t) y := (p.subpath t 1).cast rfl p.target.symm
  have ha : ∀ u, a u ∈ U := by simpa only [a, Path.cast_coe] using hfirst
  have hb : ∀ u, b u ∈ U := by simpa only [b, Path.cast_coe] using hlast
  have hfirst' : internalMetric D U x (p s) ≤ pathLength D (p.subpath 0 s) := by
    have hh : internalMetric D U x (p s) ≤ pathLength D a := iInf_le_of_le a (iInf_le _ ha)
    simpa only [a, pathLength, Path.extend_cast] using hh
  have hlast' : internalMetric D U (p t) y ≤ pathLength D (p.subpath t 1) := by
    have hh : internalMetric D U (p t) y ≤ pathLength D b := iInf_le_of_le b (iInf_le _ hb)
    simpa only [b, pathLength, Path.extend_cast] using hh
  have hq : internalMetric D U (p s) (p t) ≤ pathLength D q :=
    iInf_le_of_le q (iInf_le _ hdetour)
  calc
    internalMetric D U x y ≤ internalMetric D U x (p s) + internalMetric D U (p s) y :=
      hD.internalMetric_triangle U x (p s) y
    _ ≤ internalMetric D U x (p s) +
        (internalMetric D U (p s) (p t) + internalMetric D U (p t) y) :=
      add_le_add le_rfl (hD.internalMetric_triangle U (p s) (p t) y)
    _ ≤ pathLength D (p.subpath 0 s) + (pathLength D q + pathLength D (p.subpath t 1)) :=
      add_le_add hfirst' (add_le_add hq hlast')
    _ = (pathLength D (p.subpath 0 s) + pathLength D (p.subpath t 1)) + pathLength D q := by
      ac_rfl
    _ ≤ pathLength D p + pathLength D q :=
      add_le_add (hD.pathLength_initial_add_final_le p s t hst) le_rfl

/-- If every path in `V` admits arbitrarily short middle detours in `U`,
then deleting `V \ U` preserves the internal distance. The detour condition
is explicit and is not asserted for a particular random metric. -/
theorem IsEuclideanLengthMetric.internalMetric_eq_of_arbitrarily_short_middle_detours
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {U V : Set ℂ}
    (hUV : U ⊆ V) {x y : ℂ}
    (hdetours : ∀ (p : Path x y), (∀ u, p u ∈ V) →
      ∀ ε : ℝ≥0, 0 < ε → ∃ (s t : unitInterval) (_ : s ≤ t)
        (q : Path (p s) (p t)),
        (∀ u, (p.subpath 0 s) u ∈ U) ∧
        (∀ u, (p.subpath t 1) u ∈ U) ∧
        (∀ u, q u ∈ U) ∧ pathLength D q ≤ ε) :
    internalMetric D U x y = internalMetric D V x y := by
  apply le_antisymm
  · change internalMetric D U x y ≤ ⨅ (p : Path x y) (_ : ∀ u, p u ∈ V), pathLength D p
    refine le_iInf fun p => le_iInf fun hp => ?_
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨s, t, hst, q, hfirst, hlast, hq, hlen⟩ := hdetours p hp ε hε
    exact (hD.internalMetric_le_of_middle_detour p s t hst q hfirst hlast hq).trans
      (add_le_add le_rfl hlen)
  · exact internalMetric_anti D hUV x y


end HarmonicBalls
