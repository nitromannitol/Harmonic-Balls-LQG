import HarmonicBalls.Steps.Sec11.ConeOpen

/-! # Coordinates for planar open sectors -/

namespace HarmonicBalls

open Set Topology

/-- The oriented planar area of two complex vectors. -/
def planarCross (v w : ℂ) : ℝ := v.re * w.im - v.im * w.re

/-- A positively oriented sector is the intersection of two open
half-planes. -/
theorem mem_openSector_iff_planarCross_pos {v w x : ℂ}
    (hvw : 0 < planarCross v w) :
    x ∈ openSector v w ↔ 0 < planarCross v x ∧ 0 < planarCross x w := by
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    dsimp [planarCross] at hvw ⊢
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    constructor <;> nlinarith [mul_pos ha hvw, mul_pos hb hvw]
  · rintro ⟨hxv, hxw⟩
    let a : ℝ := planarCross x w / planarCross v w
    let b : ℝ := planarCross v x / planarCross v w
    have ha : 0 < a := div_pos hxw hvw
    have hb : 0 < b := div_pos hxv hvw
    have hd : w.im * v.re - w.re * v.im ≠ 0 := by
      dsimp [planarCross] at hvw
      nlinarith
    refine ⟨a, b, ha, hb, ?_⟩
    apply Complex.ext <;> dsimp [a, b, planarCross] at * <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] <;>
      field_simp [ne_of_gt hvw, hd] <;> ring

/-- Two positively oriented directions generate a proper open cone. -/
theorem isOpenCone_openSector_of_planarCross_pos {v w : ℂ}
    (hvw : 0 < planarCross v w) : IsOpenCone (openSector v w) := by
  have hopen : IsOpen (openSector v w) := by
    have heq : openSector v w = {x : ℂ | 0 < planarCross v x ∧ 0 < planarCross x w} := by
      ext x
      exact mem_openSector_iff_planarCross_pos hvw
    rw [heq]
    have h1 : Continuous (fun x : ℂ => planarCross v x) := by unfold planarCross; fun_prop
    have h2 : Continuous (fun x : ℂ => planarCross x w) := by unfold planarCross; fun_prop
    exact (isOpen_lt continuous_const h1).inter (isOpen_lt continuous_const h2)
  have hproper : openSector v w ≠ univ := by
    intro h
    have hz : (0 : ℂ) ∈ openSector v w := by rw [h]; trivial
    have := (mem_openSector_iff_planarCross_pos hvw).mp hz
    simp [planarCross] at this
  have hv : v ≠ 0 := by
    intro h
    subst v
    simp [planarCross] at hvw
  have hw : w ≠ 0 := by
    intro h
    subst w
    simp [planarCross] at hvw
  exact ⟨⟨v + w, ⟨1, 1, by norm_num, by norm_num, by simp⟩⟩,
    hopen, hproper, v, w, hv, hw, rfl⟩

end HarmonicBalls
