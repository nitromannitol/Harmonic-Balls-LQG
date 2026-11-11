import HarmonicBalls.FirstPass.S11r.RootedFinite
import HarmonicBalls.FirstPass.S11r.RootedLocality

/-!
# triangle inequality of the internal metric of a symmetric function on a set

Deterministic input for `he_tri` of `eq_const_mul_internal_of_local_agreement` (section 3). For a symmetric `E` with `E x x = 0` and the triangle inequality on `D`:

* `curveLength_affine`: affine reparametrization `τ ↦ c τ + d` (`c > 0`) does not change the curve length;
* `pathLength_trans_le_of_symm`: the `E`-length of a concatenation of paths in `D` is at most the sum of the lengths;
* `internalMetric_triangle_on`: the internal metric `internalMetric E D` satisfies the triangle inequality on `D`.

Only the partition description of `curveLength` is used; no metric-space structure on `ℂ` is needed.
-/

namespace HarmonicBalls

open Set Filter Topology Metric unitInterval
open scoped ENNReal

/-- Affine reparametrization with positive slope preserves the curve length (reindexing of partitions). -/
theorem curveLength_affine (E : ℂ → ℂ → ℝ) (p : ℝ → ℂ) {c : ℝ} (d : ℝ) (hc : 0 < c) (a b : ℝ) :
    curveLength E (fun τ => p (c * τ + d)) a b = curveLength E p (c * a + d) (c * b + d) := by
  have hcancel : ∀ x : ℝ, c * ((x - d) / c) + d = x := fun x => by
    rw [mul_comm, div_mul_cancel₀ _ hc.ne']
    ring
  unfold curveLength
  apply le_antisymm
  · refine iSup_le fun w => ?_
    rcases w with ⟨N, u, hu, hmem⟩
    refine le_iSup_of_le ⟨N, ⟨fun i => c * u i + d, ?_, ?_⟩⟩ le_rfl
    · intro i j hij
      have := mul_le_mul_of_nonneg_left (hu hij) hc.le
      show c * u i + d ≤ c * u j + d
      linarith
    · intro i
      have h1 := mul_le_mul_of_nonneg_left (hmem i).1 hc.le
      have h2 := mul_le_mul_of_nonneg_left (hmem i).2 hc.le
      exact ⟨by show c * a + d ≤ c * u i + d; linarith, by show c * u i + d ≤ c * b + d; linarith⟩
  · refine iSup_le fun w => ?_
    rcases w with ⟨N, v, hv, hmem⟩
    refine le_iSup_of_le ⟨N, ⟨fun i => (v i - d) / c, ?_, ?_⟩⟩ (le_of_eq ?_)
    · intro i j hij
      show (v i - d) / c ≤ (v j - d) / c
      exact div_le_div_of_nonneg_right (by linarith [hv hij]) hc.le
    · intro i
      have h := hmem i
      constructor
      · show a ≤ (v i - d) / c
        rw [le_div_iff₀ hc]
        linarith [h.1]
      · show (v i - d) / c ≤ b
        rw [div_le_iff₀ hc]
        linarith [h.2]
    · simp only [hcancel]

/-- The `E`-length of a concatenation of two paths in `D` is at most the sum of their lengths: split the length of the
concatenation at `1/2` (`curveLength_add_on`) and reparametrize each half (`extend_trans_of_le_half`,
`extend_trans_of_half_le`). -/
theorem pathLength_trans_le_of_symm (E : ℂ → ℂ → ℝ) {D : Set ℂ} (hs : ∀ x y, E x y = E y x)
    (hself : ∀ x ∈ D, E x x = 0) (htri : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, E x z ≤ E x y + E y z)
    {x y z : ℂ} (P : Path x y) (Q : Path y z) (hP : ∀ t, P t ∈ D) (hQ : ∀ t, Q t ∈ D) :
    pathLength E (P.trans Q) ≤ pathLength E P + pathLength E Q := by
  have hPD : ∀ t ∈ Icc (0 : ℝ) 1, P.extend t ∈ D := fun t ht => by
    have e1 : P.extend t = P ⟨t, ht⟩ := Path.extend_extends' P ⟨t, ht⟩
    rw [e1]
    exact hP _
  have hQD : ∀ t ∈ Icc (0 : ℝ) 1, Q.extend t ∈ D := fun t ht => by
    have e1 : Q.extend t = Q ⟨t, ht⟩ := Path.extend_extends' Q ⟨t, ht⟩
    rw [e1]
    exact hQ _
  have hTD : ∀ t ∈ Icc (0 : ℝ) 1, (P.trans Q).extend t ∈ D := by
    intro t ht
    rcases le_total t (1 / 2) with h | h
    · rw [Path.extend_trans_of_le_half P Q h]
      exact hPD (2 * t) ⟨by linarith [ht.1], by linarith⟩
    · rw [Path.extend_trans_of_half_le P Q h]
      exact hQD (2 * t - 1) ⟨by linarith, by linarith [ht.2]⟩
  have hsplit := RootedLocal.curveLength_add_on (V := D) hs hself htri (hP 0) ((P.trans Q).extend)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (fun τ hτ => hTD τ hτ)
  have hA : curveLength E (P.trans Q).extend 0 (1 / 2) = pathLength E P := by
    have h1 : curveLength E (P.trans Q).extend 0 (1 / 2) =
        curveLength E (fun τ => P.extend (2 * τ + 0)) 0 (1 / 2) := by
      apply curveLength_eq_of_eqOn
      intro τ hτ
      show (P.trans Q).extend τ = P.extend (2 * τ + 0)
      rw [Path.extend_trans_of_le_half P Q hτ.2, add_zero]
    rw [h1, curveLength_affine E P.extend (c := 2) 0 two_pos]
    norm_num [pathLength]
  have hB : curveLength E (P.trans Q).extend (1 / 2) 1 = pathLength E Q := by
    have h1 : curveLength E (P.trans Q).extend (1 / 2) 1 =
        curveLength E (fun τ => Q.extend (2 * τ + -1)) (1 / 2) 1 := by
      apply curveLength_eq_of_eqOn
      intro τ hτ
      show (P.trans Q).extend τ = Q.extend (2 * τ + -1)
      rw [Path.extend_trans_of_half_le P Q hτ.1, sub_eq_add_neg]
    rw [h1, curveLength_affine E Q.extend (c := 2) (-1) two_pos]
    norm_num [pathLength]
  refine le_of_eq ?_
  calc pathLength E (P.trans Q) = curveLength E (P.trans Q).extend 0 1 := rfl
    _ = curveLength E (P.trans Q).extend 0 (1 / 2) + curveLength E (P.trans Q).extend (1 / 2) 1 := hsplit.symm
    _ = pathLength E P + pathLength E Q := by rw [hA, hB]

/-- **Triangle inequality of the internal metric on `D`** (he_tri of `eq_const_mul_internal_of_local_agreement`, R2 Step C):
for a symmetric `E` vanishing on the diagonal of `D` and satisfying the triangle inequality on `D`, the internal metric
`internalMetric E D` satisfies the triangle inequality on `D`. Concatenate a path from `x` to `y` and one from `y` to `z`. -/
theorem internalMetric_triangle_on (E : ℂ → ℂ → ℝ) {D : Set ℂ} (hs : ∀ x y, E x y = E y x)
    (hself : ∀ x ∈ D, E x x = 0) (htri : ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, E x z ≤ E x y + E y z)
    {x y z : ℂ} :
    internalMetric E D x z ≤ internalMetric E D x y + internalMetric E D y z := by
  simp only [internalMetric, ENNReal.iInf_add, ENNReal.add_iInf]
  refine le_iInf₂ fun Q hQ => le_iInf₂ fun P hP => ?_
  have hpq : ∀ t, (P.trans Q) t ∈ D := by
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact hP _
    · exact hQ _
  exact (iInf_le_of_le (P.trans Q) (iInf_le _ hpq)).trans (pathLength_trans_le_of_symm E hs hself htri P Q hP hQ)

end HarmonicBalls
