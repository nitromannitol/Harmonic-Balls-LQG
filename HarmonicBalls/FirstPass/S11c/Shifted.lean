import HarmonicBalls.FirstPass.S11c.Chain
import HarmonicBalls.FirstPass.S11c.Closed
import HarmonicBalls.FirstPass.S11c.Classes
import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# Proposition 11.10, the pointwise shifted bound on the square

Let `E` be the Weyl-scaled metric of `D` by a function `f` (the shifted
LQG metric, paper Fact 2.2 III). On the grid box `S₂`: if the weight satisfies `ξ f ≤ 0` on `S₂`, the weight on the exterior
set `K₁` is at most `log(ε/(3a))`, the enlarged pieces `Ŝ ∩ S₂` have `D`-diameter at most `ε/3`, and `K₁` has `D`-diameter at
most `a`, then `E` has internal diameter at most `ε` on `S₂` (paper lines 3127-3137, with the constant `ε/3` of defect (a)).
The closed-set Weyl comparison is the frozen input `WeylInternalClosedFrozen` (Frozen/S11c.lean). The pieces and `K₁` are
closed (Closed.lean); the cover and contacts are `gridBox_subset_gridK1_union_blocks` and `gridK1_contact`.
-/

namespace HarmonicBalls

open Set

theorem shifted_sup_le_of_good (hW : WeylInternalClosedFrozen) {h : ℝ} (hh : 0 < h) {Jx Jy : Set ℤ}
    {A₁ A₂ B₁ B₂ : ℤ} {D E : ℂ → ℂ → ℝ} {ξ : ℝ} {f : ℂ → ℝ} {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a)
    (hDl : IsEuclideanLengthMetric D) (hEl : IsEuclideanLengthMetric E) (hEnn : ∀ x y, 0 ≤ E x y)
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hA16 : A₁ + 16 ≤ A₂) (hB16 : B₁ + 16 ≤ B₂)
    (hpar : ∀ j ∈ Jx, ∀ j' ∈ Jx, j' % 2 = j % 2)
    (hJxbox : ∀ j ∈ Jx, A₁ ≤ 8 * j ∧ 8 * j + 8 ≤ A₂) (hJybox : ∀ k ∈ Jy, B₁ ≤ 8 * k ∧ 8 * k + 8 ≤ B₂)
    (hfP : ∀ z ∈ gridBox h A₁ A₂ B₁ B₂, ξ * f z ≤ 0)
    (hfK : ∀ z ∈ gridK1 h Jx Jy A₁ A₂ B₁ B₂, ξ * f z ≤ Real.log (ε / (3 * a)))
    (hDP : ∀ p : (Jx ×ˢ Jy : Set (ℤ × ℤ)), ∀ u ∈ gridBlock h p.1.1 p.1.2 ∩ gridBox h A₁ A₂ B₁ B₂,
      ∀ v ∈ gridBlock h p.1.1 p.1.2 ∩ gridBox h A₁ A₂ B₁ B₂,
        internalMetric D (gridBlock h p.1.1 p.1.2 ∩ gridBox h A₁ A₂ B₁ B₂) u v ≤ ENNReal.ofReal (ε / 3))
    (hDK : ∀ u ∈ gridK1 h Jx Jy A₁ A₂ B₁ B₂, ∀ v ∈ gridK1 h Jx Jy A₁ A₂ B₁ B₂,
      internalMetric D (gridK1 h Jx Jy A₁ A₂ B₁ B₂) u v ≤ ENNReal.ofReal a) :
    ∀ u ∈ gridBox h A₁ A₂ B₁ B₂, ∀ v ∈ gridBox h A₁ A₂ B₁ B₂,
      internalMetric E (gridBox h A₁ A₂ B₁ B₂) u v ≤ ENNReal.ofReal ε := by
  have hA1 : A₁ + 1 ≤ A₂ := by omega
  have hB1 : B₁ + 1 ≤ B₂ := by omega
  set W := gridBox h A₁ A₂ B₁ B₂ with hWdef
  set K := gridK1 h Jx Jy A₁ A₂ B₁ B₂ with hKdef
  set P : (Jx ×ˢ Jy : Set (ℤ × ℤ)) → Set ℂ := fun p => gridBlock h p.1.1 p.1.2 ∩ W with hPdef
  have hKW : K ⊆ W := gridK1_subset_gridBox hh Jx Jy A₁ A₂ B₁ B₂
  have hPW : ∀ p, P p ⊆ W := fun p => inter_subset_right
  have hcover : W ⊆ K ∪ ⋃ p, P p := by
    intro x hx
    rcases gridBox_subset_gridK1_union_blocks hh hA1 hB1 hx with hK | hb
    · exact Or.inl hK
    · obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 hb
      exact Or.inr (mem_iUnion.2 ⟨⟨p, hp⟩, ⟨hxp, hx⟩⟩)
  have hmeet : ∀ p, ∃ w, w ∈ K ∧ w ∈ P p := by
    intro p
    obtain ⟨hj, hk⟩ := p.2
    obtain ⟨hjA, hjA2⟩ := hJxbox _ hj
    obtain ⟨hkB, hkB2⟩ := hJybox _ hk
    obtain ⟨w, hwK, hwW, hwre, hwim⟩ := gridK1_contact hh hA16 (hpar _ hj) hjA hjA2 hkB hkB2
    exact ⟨w, hwK, ⟨⟨hwre, hwim⟩, hwW⟩⟩
  have hKc : IsClosed K := gridK1_isClosed h Jx Jy A₁ A₂ B₁ B₂
  have hPc : ∀ p, IsClosed (P p) := fun p => (gridBlock_isClosed h p.1.1 p.1.2).inter (gridBox_isClosed h A₁ A₂ B₁ B₂)
  -- the exterior set: the closed-set Weyl comparison with `B = log(ε/(3a))`
  have hexpB : Real.exp (Real.log (ε / (3 * a))) * a = ε / 3 := by
    rw [Real.exp_log (by positivity)]
    field_simp
  have hK : ∀ u ∈ K, ∀ v ∈ K, internalMetric E K u v ≤ ENNReal.ofReal (ε / 3) := by
    intro u hu v hv
    calc internalMetric E K u v
        ≤ ENNReal.ofReal (Real.exp (Real.log (ε / (3 * a)))) * internalMetric D K u v :=
          hW D E ξ (Real.log (ε / (3 * a))) f K hDl hEnn hscale hKc hfK u v
      _ ≤ ENNReal.ofReal (Real.exp (Real.log (ε / (3 * a)))) * ENNReal.ofReal a := by
          gcongr
          exact hDK u hu v hv
      _ = ENNReal.ofReal (ε / 3) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, hexpB]
  have hP : ∀ p, ∀ u ∈ P p, ∀ v ∈ P p, internalMetric E (P p) u v ≤ ENNReal.ofReal (ε / 3) := by
    intro p u hu v hv
    have hfw : ∀ z ∈ P p, ξ * f z ≤ 0 := fun z hz => hfP z (hPW p hz)
    calc internalMetric E (P p) u v
        ≤ ENNReal.ofReal (Real.exp 0) * internalMetric D (P p) u v :=
          hW D E ξ 0 f (P p) hDl hEnn hscale (hPc p) hfw u v
      _ ≤ ENNReal.ofReal (ε / 3) := by
          rw [Real.exp_zero, ENNReal.ofReal_one, one_mul]
          exact hDP p u hu v hv
  exact internalMetric_le_three_pieces hEl hε.le hKW hPW hcover hmeet hK hP

end HarmonicBalls
