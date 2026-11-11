import HarmonicBalls.FirstPass.S11c.Grid
import HarmonicBalls.FirstPass.S11c.Connect
import Mathlib.Analysis.Convex.PathConnected

/-!
# Proposition 11.10, the exterior set as a union of unit cells

The exterior set `K₀ = box \ (Xs ×ℂ Ys)` of the proof of `lemma:mass-diam` (paper 3022-3024) is
replaced by the union `K₁` of the closed unit cells of the box that are not inside an enlarged cell of the class.
`K₁` is a finite union of closed rectangles (for DDDF20 Lemma 3.9 as frozen), contains `K₀`, is connected, and
every enlarged piece meets it. The class cells `U` are disjoint from `K₁`.
-/

namespace HarmonicBalls

open Set

/-- The closed box `[A₁h, A₂h] × [B₁h, B₂h]` (the square `S₂` in units `h`). -/
def gridBox (h : ℝ) (A₁ A₂ B₁ B₂ : ℤ) : Set ℂ :=
  Icc ((A₁ : ℝ) * h) ((A₂ : ℝ) * h) ×ℂ Icc ((B₁ : ℝ) * h) ((B₂ : ℝ) * h)

/-- The closed unit cell `[Xh, (X+1)h] × [Yh, (Y+1)h]`. -/
def gridCell (h : ℝ) (X Y : ℤ) : Set ℂ :=
  Icc ((X : ℝ) * h) (((X : ℝ) + 1) * h) ×ℂ Icc ((Y : ℝ) * h) (((Y : ℝ) + 1) * h)

/-- The exterior set before the cell decomposition: the box minus the product of the enlarged abscissa and
ordinate unions. -/
def gridK0 (h : ℝ) (Jx Jy : Set ℤ) (A₁ A₂ B₁ B₂ : ℤ) : Set ℂ :=
  gridBox h A₁ A₂ B₁ B₂ \ {z : ℂ | z.re ∈ gridXs Jx h ∧ z.im ∈ gridXs Jy h}

/-- The unit cells of the box that are not inside an enlarged interval in at least one direction. -/
def gridCellFamily (Jx Jy : Set ℤ) (A₁ A₂ B₁ B₂ : ℤ) : Set (ℤ × ℤ) :=
  {p | A₁ ≤ p.1 ∧ p.1 + 1 ≤ A₂ ∧ B₁ ≤ p.2 ∧ p.2 + 1 ≤ B₂ ∧ (¬ gridAint Jx p.1 ∨ ¬ gridAint Jy p.2)}

/-- The exterior set `K₁`: the union of the cells of the family. -/
def gridK1 (h : ℝ) (Jx Jy : Set ℤ) (A₁ A₂ B₁ B₂ : ℤ) : Set ℂ :=
  ⋃ p ∈ gridCellFamily Jx Jy A₁ A₂ B₁ B₂, gridCell h p.1 p.2

lemma convex_combo_mem_Icc {a₁ a₂ u v s t : ℝ} (hu : u ∈ Icc a₁ a₂) (hv : v ∈ Icc a₁ a₂) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hst : s + t = 1) : s * u + t * v ∈ Icc a₁ a₂ := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  have h1 : s * a₁ + t * a₁ = a₁ := by rw [← add_mul, hst, one_mul]
  have h2 : s * a₂ + t * a₂ = a₂ := by rw [← add_mul, hst, one_mul]
  constructor
  · nlinarith [mul_nonneg hs (sub_nonneg.2 hu1), mul_nonneg ht (sub_nonneg.2 hv1)]
  · nlinarith [mul_nonneg hs (sub_nonneg.2 hu2), mul_nonneg ht (sub_nonneg.2 hv2)]

/-- Closed rectangles are preconnected. -/
lemma isPreconnected_rect (a₁ a₂ b₁ b₂ : ℝ) : IsPreconnected (Icc a₁ a₂ ×ℂ Icc b₁ b₂) := by
  apply Convex.isPreconnected
  intro x hx y hy s t hs ht hst
  rw [Complex.mem_reProdIm] at hx hy ⊢
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  exact ⟨convex_combo_mem_Icc hx.1 hy.1 hs ht hst, convex_combo_mem_Icc hx.2 hy.2 hs ht hst⟩

lemma isPreconnected_gridCell (h : ℝ) (X Y : ℤ) : IsPreconnected (gridCell h X Y) :=
  isPreconnected_rect _ _ _ _

lemma mem_gridCell_iff (h : ℝ) (X Y : ℤ) (z : ℂ) :
    z ∈ gridCell h X Y ↔ (X : ℝ) * h ≤ z.re ∧ z.re ≤ ((X : ℝ) + 1) * h ∧
      (Y : ℝ) * h ≤ z.im ∧ z.im ≤ ((Y : ℝ) + 1) * h := by
  simp only [gridCell, Complex.mem_reProdIm, mem_Icc]
  tauto

/-- Every point of the exterior set lies in a cell of the family. -/
lemma gridK0_subset_gridK1 {h : ℝ} (hh : 0 < h) {Jx Jy : Set ℤ} {A₁ A₂ B₁ B₂ : ℤ} (hA : A₁ + 1 ≤ A₂)
    (hB : B₁ + 1 ≤ B₂) : gridK0 h Jx Jy A₁ A₂ B₁ B₂ ⊆ gridK1 h Jx Jy A₁ A₂ B₁ B₂ := by
  rintro z ⟨hzbox, hzE⟩
  simp only [gridBox, Complex.mem_reProdIm, mem_Icc] at hzbox
  obtain ⟨⟨hr1, hr2⟩, hi1, hi2⟩ := hzbox
  by_cases hX : z.re ∈ gridXs Jx h
  · have hY : z.im ∉ gridXs Jy h := fun h' => hzE ⟨hX, h'⟩
    obtain ⟨Y, hY1, hY2, hY3, hY4, hY5⟩ := exists_cell_of_not_mem_gridXs hh hB hi1 hi2 hY
    obtain ⟨X, hX1, hX2, hX3, hX4⟩ := exists_cell_in_box hh hA hr1 hr2
    refine mem_iUnion₂.2 ⟨(X, Y), ⟨hX1, hX2, hY1, hY2, Or.inr hY3⟩, ?_⟩
    exact (mem_gridCell_iff h X Y z).2 ⟨hX3, hX4, hY4, hY5⟩
  · obtain ⟨X, hX1, hX2, hX3, hX4, hX5⟩ := exists_cell_of_not_mem_gridXs hh hA hr1 hr2 hX
    obtain ⟨Y, hY1, hY2, hY3, hY4⟩ := exists_cell_in_box hh hB hi1 hi2
    refine mem_iUnion₂.2 ⟨(X, Y), ⟨hX1, hX2, hY1, hY2, Or.inl hX3⟩, ?_⟩
    exact (mem_gridCell_iff h X Y z).2 ⟨hX4, hX5, hY3, hY4⟩

/-- Every family cell meets the exterior set: its open part in the free direction is outside the enlarged union. -/
lemma gridCell_inter_gridK0 {h : ℝ} (hh : 0 < h) {Jx Jy : Set ℤ} {A₁ A₂ B₁ B₂ : ℤ} {p : ℤ × ℤ}
    (hp : p ∈ gridCellFamily Jx Jy A₁ A₂ B₁ B₂) :
    (gridCell h p.1 p.2 ∩ gridK0 h Jx Jy A₁ A₂ B₁ B₂).Nonempty := by
  obtain ⟨hA1, hA2, hB1, hB2, hn⟩ := hp
  have cA1 : (A₁ : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hA1
  have cA2 : ((p.1 : ℝ) + 1) ≤ (A₂ : ℝ) := by exact_mod_cast hA2
  have cB1 : (B₁ : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast hB1
  have cB2 : ((p.2 : ℝ) + 1) ≤ (B₂ : ℝ) := by exact_mod_cast hB2
  rcases hn with hn | hn
  · -- the abscissa cell is free: the point at abscissa `(p.1 + 1/2) h` and ordinate `p.2 h`
    have m1 : (p.1 : ℝ) * h ≤ ((p.1 : ℝ) + 1 / 2) * h := by nlinarith
    have m2 : ((p.1 : ℝ) + 1 / 2) * h ≤ ((p.1 : ℝ) + 1) * h := by nlinarith
    have m4 : (p.2 : ℝ) * h ≤ ((p.2 : ℝ) + 1) * h := by nlinarith
    have b1 : (A₁ : ℝ) * h ≤ ((p.1 : ℝ) + 1 / 2) * h := by nlinarith
    have b2 : ((p.1 : ℝ) + 1 / 2) * h ≤ (A₂ : ℝ) * h := by nlinarith
    have b3 : (B₁ : ℝ) * h ≤ (p.2 : ℝ) * h := by nlinarith
    have b4 : (p.2 : ℝ) * h ≤ (B₂ : ℝ) * h := by nlinarith
    have s1 : (p.1 : ℝ) * h < ((p.1 : ℝ) + 1 / 2) * h := by nlinarith
    have s2 : ((p.1 : ℝ) + 1 / 2) * h < ((p.1 : ℝ) + 1) * h := by nlinarith
    have hnot : ((p.1 : ℝ) + 1 / 2) * h ∉ gridXs Jx h :=
      not_mem_gridXs_of_not_gridAint hh hn s1 s2
    refine ⟨⟨((p.1 : ℝ) + 1 / 2) * h, (p.2 : ℝ) * h⟩, ?_, ?_, ?_⟩
    · exact (mem_gridCell_iff h p.1 p.2 _).2 ⟨m1, m2, le_rfl, m4⟩
    · exact Complex.mem_reProdIm.2 ⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩
    · exact fun hE => hnot hE.1
  · -- the ordinate cell is free: the point at abscissa `p.1 h` and ordinate `(p.2 + 1/2) h`
    have m1 : (p.1 : ℝ) * h ≤ ((p.1 : ℝ) + 1) * h := by nlinarith
    have m3 : (p.2 : ℝ) * h ≤ ((p.2 : ℝ) + 1 / 2) * h := by nlinarith
    have m4 : ((p.2 : ℝ) + 1 / 2) * h ≤ ((p.2 : ℝ) + 1) * h := by nlinarith
    have b1 : (A₁ : ℝ) * h ≤ (p.1 : ℝ) * h := by nlinarith
    have b2 : (p.1 : ℝ) * h ≤ (A₂ : ℝ) * h := by nlinarith
    have b3 : (B₁ : ℝ) * h ≤ ((p.2 : ℝ) + 1 / 2) * h := by nlinarith
    have b4 : ((p.2 : ℝ) + 1 / 2) * h ≤ (B₂ : ℝ) * h := by nlinarith
    have s1 : (p.2 : ℝ) * h < ((p.2 : ℝ) + 1 / 2) * h := by nlinarith
    have s2 : ((p.2 : ℝ) + 1 / 2) * h < ((p.2 : ℝ) + 1) * h := by nlinarith
    have hnot : ((p.2 : ℝ) + 1 / 2) * h ∉ gridXs Jy h :=
      not_mem_gridXs_of_not_gridAint hh hn s1 s2
    refine ⟨⟨(p.1 : ℝ) * h, ((p.2 : ℝ) + 1 / 2) * h⟩, ?_, ?_, ?_⟩
    · exact (mem_gridCell_iff h p.1 p.2 _).2 ⟨le_rfl, m1, m3, m4⟩
    · exact Complex.mem_reProdIm.2 ⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩
    · exact fun hE => hnot hE.2

/-- The exterior set `K₁` is connected, once the exterior set `K₀` is connected. -/
lemma isPreconnected_gridK1 {h : ℝ} (hh : 0 < h) {Jx Jy : Set ℤ} {A₁ A₂ B₁ B₂ : ℤ} (hA : A₁ + 1 ≤ A₂)
    (hB : B₁ + 1 ≤ B₂) (hK0 : IsPreconnected (gridK0 h Jx Jy A₁ A₂ B₁ B₂)) {x0 : ℂ}
    (hx0 : x0 ∈ gridK0 h Jx Jy A₁ A₂ B₁ B₂) : IsPreconnected (gridK1 h Jx Jy A₁ A₂ B₁ B₂) := by
  have hsub := gridK0_subset_gridK1 (Jx := Jx) (Jy := Jy) hh hA hB
  have key : gridK1 h Jx Jy A₁ A₂ B₁ B₂ = ⋃₀ ((fun p : ℤ × ℤ => gridK0 h Jx Jy A₁ A₂ B₁ B₂ ∪
      gridCell h p.1 p.2) '' gridCellFamily Jx Jy A₁ A₂ B₁ B₂) := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp, hzc⟩ := mem_iUnion₂.1 hz
      exact ⟨_, ⟨p, hp, rfl⟩, Or.inr hzc⟩
    · rintro ⟨s, ⟨p, hp, rfl⟩, hzs⟩
      rcases hzs with hz | hz
      · exact hsub hz
      · exact mem_iUnion₂.2 ⟨p, hp, hz⟩
  rw [key]
  apply isPreconnected_sUnion x0
  · rintro s ⟨p, hp, rfl⟩
    exact Or.inl hx0
  · rintro s ⟨p, hp, rfl⟩
    obtain ⟨y, hyc, hyK⟩ := gridCell_inter_gridK0 hh hp
    exact IsPreconnected.union y hyK hyc hK0 (isPreconnected_gridCell h _ _)

/-- Contact: the enlarged abscissa interval `[(8j-1)h, (8j+9)h]` of a class cell meets the exterior set `K₁` inside the
box. The witness is the edge point just outside the enlarged interval, in a unit cell that is free in the abscissa
direction (the parity of the class makes the neighbouring cell free); the ordinate is the middle of a cell of `k`. -/
lemma gridK1_contact {h : ℝ} (hh : 0 < h) {Jx Jy : Set ℤ} {A₁ A₂ B₁ B₂ j k : ℤ} (hA : A₁ + 16 ≤ A₂)
    (hJx : ∀ j' ∈ Jx, j' % 2 = j % 2) (hjA : A₁ ≤ 8 * j) (hjA2 : 8 * j + 8 ≤ A₂)
    (hk : B₁ ≤ 8 * k) (hkB : 8 * k + 8 ≤ B₂) :
    ∃ w : ℂ, w ∈ gridK1 h Jx Jy A₁ A₂ B₁ B₂ ∧ w ∈ gridBox h A₁ A₂ B₁ B₂ ∧
      w.re ∈ Icc ((8 * (j : ℝ) - 1) * h) ((8 * (j : ℝ) + 9) * h) ∧
      w.im ∈ Icc ((8 * (k : ℝ) - 1) * h) ((8 * (k : ℝ) + 9) * h) := by
  have cyl : ((B₁ : ℤ) : ℝ) * h ≤ ((8 * k + 4 : ℤ) : ℝ) * h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast (show B₁ ≤ 8 * k + 4 by omega)) hh.le
  have cyu : ((8 * k + 4 : ℤ) : ℝ) * h ≤ ((B₂ : ℤ) : ℝ) * h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast (show 8 * k + 4 ≤ B₂ by omega)) hh.le
  have cyc : ((8 * k + 4 : ℤ) : ℝ) * h ≤ (((8 * k + 4 : ℤ) : ℝ) + 1) * h :=
    mul_le_mul_of_nonneg_right (by linarith) hh.le
  have ikk : (8 * (k : ℝ) - 1) * h ≤ ((8 * k + 4 : ℤ) : ℝ) * h :=
    mul_le_mul_of_nonneg_right (by push_cast; linarith) hh.le
  have ikk' : ((8 * k + 4 : ℤ) : ℝ) * h ≤ (8 * (k : ℝ) + 9) * h :=
    mul_le_mul_of_nonneg_right (by push_cast; linarith) hh.le
  by_cases hr : 8 * j + 10 ≤ A₂
  · -- right witness: the unit cell `X = 8j+9` is free
    have hfree : ¬ gridAint Jx (8 * j + 9) := by
      rintro ⟨j', hj', h1, h2⟩
      have := hJx j' hj'
      omega
    have cxl : (A₁ : ℝ) * h ≤ ((8 * j + 9 : ℤ) : ℝ) * h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show A₁ ≤ 8 * j + 9 by omega)) hh.le
    have cxu : ((8 * j + 9 : ℤ) : ℝ) * h ≤ (A₂ : ℝ) * h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show 8 * j + 9 ≤ A₂ by omega)) hh.le
    have cxc : ((8 * j + 9 : ℤ) : ℝ) * h ≤ (((8 * j + 9 : ℤ) : ℝ) + 1) * h :=
      mul_le_mul_of_nonneg_right (by linarith) hh.le
    refine ⟨⟨((8 * j + 9 : ℤ) : ℝ) * h, ((8 * k + 4 : ℤ) : ℝ) * h⟩, ?_, ?_, ?_, ?_⟩
    · refine mem_iUnion₂.2 ⟨(8 * j + 9, 8 * k + 4), ⟨by omega, by omega, by omega, by omega, Or.inl hfree⟩, ?_⟩
      exact (mem_gridCell_iff h _ _ _).2 ⟨le_rfl, cxc, le_rfl, cyc⟩
    · exact Complex.mem_reProdIm.2 ⟨⟨cxl, cxu⟩, ⟨cyl, cyu⟩⟩
    · show ((8 * j + 9 : ℤ) : ℝ) * h ∈ Icc _ _
      push_cast
      exact ⟨by nlinarith, le_rfl⟩
    · show ((8 * k + 4 : ℤ) : ℝ) * h ∈ Icc _ _
      exact ⟨ikk, ikk'⟩
  · -- left witness: the unit cell `X = 8j-2` is free, its right edge is `(8j-1)h`
    have hfree : ¬ gridAint Jx (8 * j - 2) := by
      rintro ⟨j', hj', h1, h2⟩
      have := hJx j' hj'
      omega
    have cxl : (A₁ : ℝ) * h ≤ ((8 * j - 2 : ℤ) : ℝ) * h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show A₁ ≤ 8 * j - 2 by omega)) hh.le
    have cxu : ((8 * j - 1 : ℤ) : ℝ) * h ≤ (A₂ : ℝ) * h :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (show 8 * j - 1 ≤ A₂ by omega)) hh.le
    have cxc : ((8 * j - 2 : ℤ) : ℝ) * h ≤ (((8 * j - 2 : ℤ) : ℝ) + 1) * h :=
      mul_le_mul_of_nonneg_right (by linarith) hh.le
    have cxe : ((8 * j - 2 : ℤ) : ℝ) * h ≤ ((8 * j - 1 : ℤ) : ℝ) * h :=
      mul_le_mul_of_nonneg_right (by push_cast; linarith) hh.le
    refine ⟨⟨((8 * j - 1 : ℤ) : ℝ) * h, ((8 * k + 4 : ℤ) : ℝ) * h⟩, ?_, ?_, ?_, ?_⟩
    · refine mem_iUnion₂.2 ⟨(8 * j - 2, 8 * k + 4), ⟨by omega, by omega, by omega, by omega, Or.inl hfree⟩, ?_⟩
      refine (mem_gridCell_iff h _ _ _).2 ⟨cxe, ?_, le_rfl, cyc⟩
      have e : ((8 * j - 2 : ℤ) : ℝ) + 1 = ((8 * j - 1 : ℤ) : ℝ) := by push_cast; ring
      rw [e]
    · exact Complex.mem_reProdIm.2 ⟨⟨cxl.trans cxe, cxu⟩, ⟨cyl, cyu⟩⟩
    · show ((8 * j - 1 : ℤ) : ℝ) * h ∈ Icc _ _
      push_cast
      exact ⟨le_rfl, by nlinarith⟩
    · show ((8 * k + 4 : ℤ) : ℝ) * h ∈ Icc _ _
      exact ⟨ikk, ikk'⟩

end HarmonicBalls
