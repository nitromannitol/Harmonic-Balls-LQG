import HarmonicBalls.FirstPass.S11c.Cover

/-!
# Proposition 11.10, closedness of the grid sets (fp-S11c, owner n1)

FIRST-PASS NEW (deterministic). The closed-set Weyl comparison (`WeylInternalClosedFrozen`) is applied to the closed box,
the closed enlarged blocks and the exterior set `K₁` (a finite union of closed unit cells inside the box). These closedness
facts and the inclusion `K₁ ⊆ box` are proved here.
-/

namespace HarmonicBalls

open Set

lemma isClosed_of_re_im_mem {A B : Set ℝ} (hA : IsClosed A) (hB : IsClosed B) :
    IsClosed {z : ℂ | z.re ∈ A ∧ z.im ∈ B} :=
  (hA.preimage Complex.continuous_re).inter (hB.preimage Complex.continuous_im)

lemma gridBox_isClosed (h : ℝ) (A₁ A₂ B₁ B₂ : ℤ) : IsClosed (gridBox h A₁ A₂ B₁ B₂) :=
  isClosed_of_re_im_mem isClosed_Icc isClosed_Icc

lemma gridBlock_isClosed (h : ℝ) (j k : ℤ) : IsClosed (gridBlock h j k) :=
  isClosed_of_re_im_mem isClosed_Icc isClosed_Icc

lemma gridCell_isClosed (h : ℝ) (X Y : ℤ) : IsClosed (gridCell h X Y) :=
  isClosed_of_re_im_mem isClosed_Icc isClosed_Icc

lemma gridCellFamily_finite (Jx Jy : Set ℤ) (A₁ A₂ B₁ B₂ : ℤ) :
    (gridCellFamily Jx Jy A₁ A₂ B₁ B₂).Finite := by
  refine ((Set.finite_Icc A₁ A₂).prod (Set.finite_Icc B₁ B₂)).subset ?_
  intro p hp
  obtain ⟨h1, h2, h3, h4, -⟩ := hp
  exact ⟨⟨h1, by omega⟩, ⟨h3, by omega⟩⟩

lemma gridK1_isClosed (h : ℝ) (Jx Jy : Set ℤ) (A₁ A₂ B₁ B₂ : ℤ) :
    IsClosed (gridK1 h Jx Jy A₁ A₂ B₁ B₂) := by
  unfold gridK1
  exact (gridCellFamily_finite Jx Jy A₁ A₂ B₁ B₂).isClosed_biUnion
    (fun p _ => gridCell_isClosed h p.1 p.2)

lemma gridK1_subset_gridBox {h : ℝ} (hh : 0 < h) (Jx Jy : Set ℤ) (A₁ A₂ B₁ B₂ : ℤ) :
    gridK1 h Jx Jy A₁ A₂ B₁ B₂ ⊆ gridBox h A₁ A₂ B₁ B₂ := by
  intro z hz
  obtain ⟨p, hp, hzc⟩ := mem_iUnion₂.1 hz
  obtain ⟨hA1, hA2, hB1, hB2, -⟩ := hp
  rw [mem_gridCell_iff] at hzc
  have c1 : (A₁ : ℝ) * h ≤ (p.1 : ℝ) * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hA1) hh.le
  have c2 : ((p.1 : ℝ) + 1) * h ≤ (A₂ : ℝ) * h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hA2) hh.le
  have c3 : (B₁ : ℝ) * h ≤ (p.2 : ℝ) * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hB1) hh.le
  have c4 : ((p.2 : ℝ) + 1) * h ≤ (B₂ : ℝ) * h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hB2) hh.le
  exact Complex.mem_reProdIm.2 ⟨⟨by linarith [hzc.1], by linarith [hzc.2.1]⟩,
    ⟨by linarith [hzc.2.2.1], by linarith [hzc.2.2.2]⟩⟩

end HarmonicBalls
