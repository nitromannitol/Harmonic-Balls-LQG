import HarmonicBalls.FirstPass.S11c.Connect
import HarmonicBalls.FirstPass.S11c.Grid
import HarmonicBalls.FirstPass.S11c.Exterior

/-!
# Proposition 11.10, the core `gridK0` is preconnected for the class index sets

The exterior set `gridK1` is connected once its core `gridK0` is preconnected and nonempty
(`Exterior.isPreconnected_gridK1`, `ExteriorBound.isConnected_gridK1`); the preconnectedness of `gridK0` was a hypothesis
until now. For the class index sets `{j | j mod 2 = p, P₁ ≤ 8j, 8j + 8 ≤ P₂}` and `{k | k mod 2 = q, Q₁ ≤ 8k, 8k + 8 ≤ Q₂}`, the
core is the box minus the product of the two sets of enlarged abscissas, and each abscissa set misses a point of the box
(`Grid.exists_free_abscissa`, a free hub). Then `Connect.isPreconnected_box_diff_prod` applies.
-/

open Set

namespace HarmonicBalls

/-- The core `gridK0` of the box `[A₁, A₂] × [B₁, B₂]` for the class index sets of parities `p` and `q` is preconnected. -/
lemma isPreconnected_gridK0_class {h : ℝ} (hh : 0 < h) {p q P₁ P₂ Q₁ Q₂ A₁ A₂ B₁ B₂ : ℤ}
    (hp : p = 0 ∨ p = 1) (hq : q = 0 ∨ q = 1)
    (hP₁ : P₁ % 8 = 0) (hQ₁ : Q₁ % 8 = 0) (hA₁ : A₁ ≤ P₁) (hP₂ : P₂ ≤ A₂) (hB₁ : B₁ ≤ Q₁) (hQ₂ : Q₂ ≤ B₂)
    (hsz : P₁ + 16 ≤ P₂) (hQsz : Q₁ + 16 ≤ Q₂) (hA : A₁ + 16 ≤ A₂) (hB : B₁ + 16 ≤ B₂) :
    IsPreconnected (gridK0 h {j : ℤ | j % 2 = p ∧ P₁ ≤ 8 * j ∧ 8 * j + 8 ≤ P₂}
      {k : ℤ | k % 2 = q ∧ Q₁ ≤ 8 * k ∧ 8 * k + 8 ≤ Q₂} A₁ A₂ B₁ B₂) := by
  obtain ⟨xh, hxh, hxhX⟩ := exists_free_abscissa hh hp hP₁ hA₁ hP₂ hsz hA
  obtain ⟨yh, hyh, hyhY⟩ := exists_free_abscissa hh hq hQ₁ hB₁ hQ₂ hQsz hB
  unfold gridK0 gridBox
  exact isPreconnected_box_diff_prod hxh hxhX hyh hyhY

end HarmonicBalls
