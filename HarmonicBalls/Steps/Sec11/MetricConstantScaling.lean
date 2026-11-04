import HarmonicBalls.Defs.LQGMetric
import Mathlib.Basic.Real.Pointwise

/-! # Constant rescaling of path and internal distances -/

namespace HarmonicBalls

open Set
open scoped ENNReal Pointwise

/-- Multiplying a distance by a nonnegative constant multiplies curve length
by the same constant. -/
theorem curveLength_const_mul (D : ℂ → ℂ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (p : ℝ → ℂ) (a b : ℝ) :
    curveLength (fun x y => c * D x y) p a b = ENNReal.ofReal c * curveLength D p a b := by
  unfold curveLength
  rw [ENNReal.mul_iSup]
  apply iSup_congr
  intro q
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact ENNReal.ofReal_mul hc

/-- Multiplying a distance by a nonnegative constant multiplies path length
by the same constant. -/
theorem pathLength_const_mul (D : ℂ → ℂ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    {x y : ℂ} (p : Path x y) :
    pathLength (fun x y => c * D x y) p = ENNReal.ofReal c * pathLength D p :=
  curveLength_const_mul D c hc p.extend 0 1

/-- Positive constant rescaling commutes with internal distance, including
when no path joins the endpoints in the domain. -/
theorem internalMetric_const_mul (D : ℂ → ℂ → ℝ) {c : ℝ} (hc : 0 < c)
    (U : Set ℂ) (x y : ℂ) :
    internalMetric (fun x y => c * D x y) U x y = ENNReal.ofReal c * internalMetric D U x y := by
  unfold internalMetric
  simp_rw [pathLength_const_mul D c hc.le]
  have hct : ENNReal.ofReal c ≠ ∞ := ENNReal.ofReal_ne_top
  let : Nonempty (Path x y) := ⟨Path.segment x y⟩
  rw [ENNReal.mul_iInf (fun h _ => (hct h).elim)]
  apply iInf_congr
  intro p
  by_cases hp : ∀ t, p t ∈ U
  · let : Nonempty (∀ t, p t ∈ U) := ⟨hp⟩
    rw [ENNReal.mul_iInf (fun h _ => (hct h).elim)]
  · simp only [hp, iInf_false, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hc))]

/-- Multiplying the distance by a nonnegative constant multiplies the
set-to-set distance, including the empty-set convention. -/
theorem setDist_const_mul (D : ℂ → ℂ → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (A B : Set ℂ) :
    setDist (fun x y => c * D x y) A B = c * setDist D A B := by
  unfold setDist
  have hset : image2 (fun x y => c * D x y) A B = c • image2 D A B := by
    ext v
    simp only [mem_image2, Set.mem_smul_set]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨D x y, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨x, hx, y, hy, rfl⟩
  rw [hset, Real.sInf_smul_of_nonneg hc]
  rfl

end HarmonicBalls
