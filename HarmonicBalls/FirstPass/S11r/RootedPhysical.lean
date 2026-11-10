import HarmonicBalls.FirstPass.S11r.RootedRepair
import HarmonicBalls.FirstPass.S11m.ClearanceEq
import HarmonicBalls.Steps.Sec11.WeylPathSegments

/-!
# First pass, physical side of the rooted gluing: symmetry and length property (fp-S11r, owner n2)

Deterministic lemmas on the internal physical metric `internalPhysicalMetric e D` (RootedRepair.lean) for a symmetric
function `e`. They supply the hypotheses `he_symm` and `he_len` of `eq_const_mul_internal_of_local_agreement`
(CHATGPT-n2-R2-rooted-length.md section 3, Steps A and H):

* `internalMetric_symm_of_symm`: the internal metric of a symmetric function is symmetric (path reversal);
* `internalPhysicalMetric_length_eq` (Step H): if the internal metric of `e` on `D` is finite on `D × D`, the internal
  physical metric is a length metric on `D`: `ENNReal.ofReal (internalPhysicalMetric e D x y) =
  internalMetric (internalPhysicalMetric e D) D x y` for `x y ∈ D`.

Path reversal is proved from the partition description of `curveLength` (a supremum over partitions), so only the
symmetry of `e` is used. The metric-space versions (`IsEuclideanLengthMetric.pathLength_symm`) need the metric axioms
on all of `ℂ`, which the physical metric does not satisfy in general.
-/

namespace HarmonicBalls

open Set Filter Topology Metric unitInterval
open scoped ENNReal

/-- Reversal of time for a symmetric function `E`: the `E`-length of `t ↦ p (T - t)` on `[a, b]` is the `E`-length of
`p` on `[T - b, T - a]`. A partition of `[a, b]` is reflected, and the terms agree by the symmetry of `E`. -/
theorem curveLength_reverse_of_symm {E : ℂ → ℂ → ℝ} (hs : ∀ x y, E x y = E y x) (p : ℝ → ℂ) (T a b : ℝ) :
    curveLength E (fun t => p (T - t)) a b = curveLength E p (T - b) (T - a) := by
  have key : ∀ (q : ℝ → ℂ) (a' b' : ℝ),
      curveLength E (fun t => q (T - t)) a' b' ≤ curveLength E q (T - b') (T - a') := by
    intro q a' b'
    unfold curveLength
    refine iSup_le fun w => ?_
    rcases w with ⟨N, u, hu, hmem⟩
    let v : ℕ → ℝ := fun j => T - u (N - j)
    have hv : Monotone v := by
      apply monotone_nat_of_le_succ
      intro j
      have h1 : N - (j + 1) ≤ N - j := by omega
      have h2 : u (N - (j + 1)) ≤ u (N - j) := hu h1
      show T - u (N - j) ≤ T - u (N - (j + 1))
      linarith
    have hvmem : ∀ j, v j ∈ Icc (T - b') (T - a') := by
      intro j
      have h := hmem (N - j)
      show T - u (N - j) ∈ Icc (T - b') (T - a')
      exact ⟨by linarith [h.2], by linarith [h.1]⟩
    have hsum : ∑ i ∈ Finset.range N, ENNReal.ofReal (E (q (T - u (i + 1))) (q (T - u i)))
        = ∑ j ∈ Finset.range N, ENNReal.ofReal (E (q (v (j + 1))) (q (v j))) := by
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < N := Finset.mem_range.1 hj
      have h1 : N - 1 - j + 1 = N - j := by omega
      have h2 : N - 1 - j = N - (j + 1) := by omega
      rw [h1, h2]
      exact congrArg ENNReal.ofReal (hs _ _)
    exact le_trans (le_of_eq hsum) (le_iSup_of_le ⟨N, ⟨v, hv, hvmem⟩⟩ le_rfl)
  have h2 := key (fun t => p (T - t)) (T - b) (T - a)
  simp only [sub_sub_cancel] at h2
  exact le_antisymm (key p a b) h2

/-- The `D`-length of a path from `x` to `y` with the same symmetric `e`: the reversed path has the same length. -/
theorem pathLength_symm_of_symm {E : ℂ → ℂ → ℝ} (hs : ∀ x y, E x y = E y x) {x y : ℂ} (P : Path x y) :
    pathLength E P.symm = pathLength E P := by
  have h : P.symm.extend = fun t => P.extend (1 - t) := funext fun t => Path.extend_symm_apply P t
  unfold pathLength
  rw [h]
  have h1 := curveLength_reverse_of_symm hs P.extend 1 0 1
  rw [sub_self, sub_zero] at h1
  exact h1

/-- The internal metric of a symmetric function is symmetric (reverse the path). -/
theorem internalMetric_symm_of_symm {E : ℂ → ℂ → ℝ} (hs : ∀ x y, E x y = E y x) (U : Set ℂ) (x y : ℂ) :
    internalMetric E U x y = internalMetric E U y x := by
  have hle : ∀ a b : ℂ, internalMetric E U a b ≤ internalMetric E U b a := by
    intro a b
    unfold internalMetric
    refine le_iInf₂ fun Q hQ => ?_
    exact (iInf₂_le Q.symm (fun t => hQ _)).trans (le_of_eq (pathLength_symm_of_symm hs Q))
  exact le_antisymm (hle x y) (hle y x)

/-- Monotonicity of the curve length in the parameter interval (a partition of `[a', b']` is one of `[a, b]`). -/
theorem curveLength_mono_interval (E : ℂ → ℂ → ℝ) (p : ℝ → ℂ) {a b a' b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    curveLength E p a' b' ≤ curveLength E p a b := by
  unfold curveLength
  refine iSup_le fun w => ?_
  rcases w with ⟨N, u, hu, hmem⟩
  exact le_iSup_of_le ⟨N, ⟨u, hu, fun i => ⟨le_trans ha (hmem i).1, le_trans (hmem i).2 hb⟩⟩⟩ le_rfl

/-- The internal physical metric is the real part of the internal metric: its values are the finite internal distances. -/
theorem ofReal_internalPhysicalMetric {e : ℂ → ℂ → ℝ} {D : Set ℂ} {x y : ℂ} (h : internalMetric e D x y ≠ ⊤) :
    ENNReal.ofReal (internalPhysicalMetric e D x y) = internalMetric e D x y :=
  ENNReal.ofReal_toReal h

/-- The `D`-length of the internal physical metric along a path in `D` is at most the `e`-length of the path
(Step H, upper bound): a partition sum of internal distances is bounded by the `e`-lengths of the pieces
(`internalMetric_le_curveLength_arc`), and the pieces add up to at most the whole length (`sum_curveLength_le`). -/
theorem pathLength_internalPhysicalMetric_le {e : ℂ → ℂ → ℝ} {D : Set ℂ} (hs : ∀ x y, e x y = e y x)
    (hfin : ∀ x ∈ D, ∀ y ∈ D, internalMetric e D x y ≠ ⊤) {x y : ℂ} (P : Path x y) (hP : ∀ t, P t ∈ D) :
    pathLength (internalPhysicalMetric e D) P ≤ pathLength e P := by
  have hsymm := internalMetric_symm_of_symm hs D
  unfold pathLength
  conv_lhs => unfold curveLength
  refine iSup_le fun w => ?_
  rcases w with ⟨N, u, hu, hmem⟩
  have hPt : ∀ i, P.extend (u i) ∈ D := by
    intro i
    have e1 : P.extend (u i) = P ⟨u i, hmem i⟩ := Path.extend_extends' P ⟨u i, hmem i⟩
    rw [e1]
    exact hP _
  have hterm : ∀ i ∈ Finset.range N,
      ENNReal.ofReal (internalPhysicalMetric e D (P.extend (u (i + 1))) (P.extend (u i)))
        ≤ curveLength e P.extend (u i) (u (i + 1)) := by
    intro i _
    have hst : (⟨u i, hmem i⟩ : I) ≤ ⟨u (i + 1), hmem (i + 1)⟩ := hu (Nat.le_succ i)
    have hle := S11m.internalMetric_le_curveLength_arc (D := e) P hP hst
    rw [ofReal_internalPhysicalMetric (hfin _ (hPt (i + 1)) _ (hPt i)), hsymm]
    have e1 : P.extend (u i) = P ⟨u i, hmem i⟩ := Path.extend_extends' P ⟨u i, hmem i⟩
    have e2 : P.extend (u (i + 1)) = P ⟨u (i + 1), hmem (i + 1)⟩ :=
      Path.extend_extends' P ⟨u (i + 1), hmem (i + 1)⟩
    rw [e1, e2]
    exact hle
  calc ∑ i ∈ Finset.range N, ENNReal.ofReal (internalPhysicalMetric e D (P.extend (u (i + 1))) (P.extend (u i)))
      ≤ ∑ i ∈ Finset.range N, curveLength e P.extend (u i) (u (i + 1)) := Finset.sum_le_sum hterm
    _ ≤ curveLength e P.extend (u 0) (u N) := S11m.sum_curveLength_le e P.extend hu N
    _ ≤ curveLength e P.extend 0 1 := curveLength_mono_interval e P.extend (hmem 0).1 (hmem N).2

/-- **Step H (length property of the internal physical metric).** If the internal metric of a symmetric `e` on `D` is
finite on `D × D`, then for `x y ∈ D` the internal physical metric `internalPhysicalMetric e D` satisfies
`ENNReal.ofReal (internalPhysicalMetric e D x y) = internalMetric (internalPhysicalMetric e D) D x y`, i.e. it is a
length metric on `D` (CHATGPT-n2-R2-rooted-length.md section 3, Step H). Lower bound: each path in `D` has
`D`-length at least the one-piece distance. Upper bound: `pathLength_internalPhysicalMetric_le`. -/
theorem internalPhysicalMetric_length_eq {e : ℂ → ℂ → ℝ} {D : Set ℂ} (hs : ∀ x y, e x y = e y x)
    (hfin : ∀ x ∈ D, ∀ y ∈ D, internalMetric e D x y ≠ ⊤) :
    ∀ x ∈ D, ∀ y ∈ D, ENNReal.ofReal (internalPhysicalMetric e D x y) =
      internalMetric (internalPhysicalMetric e D) D x y := by
  intro x hx y hy
  have hgs := internalPhysicalMetric_symm_of (internalMetric_symm_of_symm hs D)
  apply le_antisymm
  · unfold internalMetric
    refine le_iInf₂ fun P hP => ?_
    exact ofReal_le_pathLength_of_symm hgs P
  · rw [ofReal_internalPhysicalMetric (hfin x hx y hy)]
    unfold internalMetric
    refine le_iInf₂ fun P hP => ?_
    exact (iInf₂_le P hP).trans (pathLength_internalPhysicalMetric_le hs hfin P hP)

end HarmonicBalls
