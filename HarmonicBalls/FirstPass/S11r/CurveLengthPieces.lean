import HarmonicBalls.Defs.LQGMetric

/-! # Curve-length facts for an arbitrary `D : ℂ → ℂ → ℝ`

Support for the local-to-global step of `eq_of_local_internalMetric_agreement_off_point`
(CHATGPT-n3-B1-B2.md, section 4.3). No metric axioms are used: superadditivity over a split
point holds for the `ENNReal`-valued partition sums, since the jump term is nonnegative. -/

namespace HarmonicBalls

open Set Finset
open scoped ENNReal

/-- Superadditivity of the `D`-length over a split point (no metric axioms needed). -/
theorem curveLength_add_le_general (D : ℂ → ℂ → ℝ) (p : ℝ → ℂ) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    curveLength D p a b + curveLength D p b c ≤ curveLength D p a c := by
  unfold curveLength
  have : Nonempty (ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b}) :=
    ⟨(0, ⟨fun _ => a, monotone_const, fun _ => ⟨le_rfl, hab⟩⟩)⟩
  have : Nonempty (ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc b c}) :=
    ⟨(0, ⟨fun _ => b, monotone_const, fun _ => ⟨le_rfl, hbc⟩⟩)⟩
  rw [ENNReal.iSup_add]
  refine iSup_le fun q1 => ?_
  rw [ENNReal.add_iSup]
  refine iSup_le fun q2 => ?_
  obtain ⟨n1, u, hu⟩ := q1
  obtain ⟨n2, v, hv⟩ := q2
  dsimp only
  let w : ℕ → ℝ := fun i => if i ≤ n1 then u i else v (min (i - n1 - 1) n2)
  have hw_mem : ∀ i, w i ∈ Icc a c := by
    intro i
    simp only [w]
    split_ifs with hi
    · exact ⟨(hu.2 i).1, (hu.2 i).2.trans hbc⟩
    · exact ⟨hab.trans (hv.2 _).1, (hv.2 _).2⟩
  have hw_mono : Monotone w := by
    intro i j hij
    by_cases hi : i ≤ n1
    · by_cases hj : j ≤ n1
      · simp only [w, hi, hj, ↓reduceIte]
        exact hu.1 hij
      · simp only [w, hi, hj, ↓reduceIte]
        exact (hu.2 i).2.trans (hv.2 _).1
    · have hj : ¬ j ≤ n1 := fun h => hi (hij.trans h)
      simp only [w, hi, hj, ↓reduceIte]
      exact hv.1 (min_le_min (by omega) le_rfl)
  have key := le_iSup
    (fun q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a c} =>
      ∑ i ∈ range q.1, ENNReal.ofReal (D (p (q.2.1 (i + 1))) (p (q.2.1 i))))
    (n1 + 1 + n2, ⟨w, hw_mono, hw_mem⟩)
  refine le_trans ?_ key
  dsimp only
  have hsplit : ∑ i ∈ range (n1 + 1 + n2), ENNReal.ofReal (D (p (w (i + 1))) (p (w i)))
      = (∑ i ∈ range n1, ENNReal.ofReal (D (p (w (i + 1))) (p (w i))))
        + ENNReal.ofReal (D (p (w (n1 + 1))) (p (w n1)))
        + ∑ x ∈ range n2, ENNReal.ofReal (D (p (w (n1 + 1 + x + 1))) (p (w (n1 + 1 + x)))) := by
    rw [Finset.sum_range_add, Finset.sum_range_succ]
  have hA : ∑ i ∈ range n1, ENNReal.ofReal (D (p (w (i + 1))) (p (w i)))
      = ∑ i ∈ range n1, ENNReal.ofReal (D (p (u (i + 1))) (p (u i))) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : w i = u i := by simp only [w, show i ≤ n1 by omega, ↓reduceIte]
    have h2 : w (i + 1) = u (i + 1) := by simp only [w, show i + 1 ≤ n1 by omega, ↓reduceIte]
    rw [h1, h2]
  have hB : ∑ x ∈ range n2, ENNReal.ofReal (D (p (w (n1 + 1 + x + 1))) (p (w (n1 + 1 + x))))
      = ∑ x ∈ range n2, ENNReal.ofReal (D (p (v (x + 1))) (p (v x))) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    have h1 : w (n1 + 1 + x) = v x := by
      have hm : min (n1 + 1 + x - n1 - 1) n2 = x := by omega
      simp only [w, show ¬ (n1 + 1 + x ≤ n1) by omega, ↓reduceIte, hm]
    have h2 : w (n1 + 1 + x + 1) = v (x + 1) := by
      have hm : min (n1 + 1 + x + 1 - n1 - 1) n2 = x + 1 := by omega
      simp only [w, show ¬ (n1 + 1 + x + 1 ≤ n1) by omega, ↓reduceIte, hm]
    rw [h1, h2]
  rw [hsplit, hA, hB, add_right_comm]
  exact le_self_add

/-- The `D`-length on `[a, b]` only depends on the restriction of the curve to `[a, b]`. -/
theorem curveLength_congr_on_Icc (D : ℂ → ℂ → ℝ) {p q : ℝ → ℂ} {a b : ℝ}
    (h : EqOn p q (Icc a b)) : curveLength D p a b = curveLength D q a b := by
  unfold curveLength
  apply iSup_congr
  intro n
  obtain ⟨m, u, hu⟩ := n
  apply Finset.sum_congr rfl
  intro i _
  rw [h (hu.2 (i + 1)), h (hu.2 i)]

/-- An affine reparametrisation of `p` onto `[s, t]` has no larger length on `[0, 1]`. -/
theorem curveLength_affine_reparam_le (D : ℂ → ℂ → ℝ) (p : ℝ → ℂ) {s t : ℝ} (hst : s ≤ t) :
    curveLength D (fun τ => p (s + τ * (t - s))) 0 1 ≤ curveLength D p s t := by
  unfold curveLength
  refine iSup_le fun q => ?_
  obtain ⟨n, u, hu⟩ := q
  refine le_iSup_of_le (n, ⟨fun i => s + u i * (t - s), ?_, ?_⟩) le_rfl
  · intro i j hij
    have := mul_le_mul_of_nonneg_right (hu.1 hij) (sub_nonneg.2 hst)
    show s + u i * (t - s) ≤ s + u j * (t - s)
    linarith
  · intro i
    have h0 := mul_nonneg (hu.2 i).1 (sub_nonneg.2 hst)
    have h1 := mul_le_mul_of_nonneg_right (hu.2 i).2 (sub_nonneg.2 hst)
    show s + u i * (t - s) ∈ Icc s t
    constructor <;> linarith [(hu.2 i).1, (hu.2 i).2]

/-- A continuous path `γ` whose restriction to `[s, t]` lies in the open set `V` gives a path in `V`
from `γ s` to `γ t`, so its internal metric in `V` is at most the `D`-length of `γ` on `[s, t]`. -/
theorem internalMetric_le_curveLength_of_subset (D : ℂ → ℂ → ℝ) {γ : ℝ → ℂ} (hγ : Continuous γ)
    {V : Set ℂ} {s t : ℝ} (hst : s ≤ t) (hV : ∀ τ ∈ Icc s t, γ τ ∈ V) :
    internalMetric D V (γ s) (γ t) ≤ curveLength D γ s t := by
  have hmem : ∀ τ ∈ Icc (0 : ℝ) 1, s + τ * (t - s) ∈ Icc s t := by
    intro τ hτ
    have h1 := mul_le_mul_of_nonneg_right hτ.2 (sub_nonneg.2 hst)
    have h0 := mul_nonneg hτ.1 (sub_nonneg.2 hst)
    constructor <;> linarith [hτ.1, hτ.2]
  let P : Path (γ s) (γ t) :=
    { toFun := fun u => γ (s + (u : ℝ) * (t - s))
      continuous_toFun := hγ.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))
      source' := by simp
      target' := by simp }
  have htrace : ∀ u, P u ∈ V := fun u => hV _ (hmem _ u.2)
  have hpath : pathLength D P = curveLength D (fun τ => γ (s + τ * (t - s))) 0 1 := by
    unfold pathLength
    apply curveLength_congr_on_Icc
    intro τ hτ
    exact Path.extend_extends' P ⟨τ, hτ⟩
  calc internalMetric D V (γ s) (γ t) ≤ pathLength D P := iInf₂_le P htrace
    _ = curveLength D (fun τ => γ (s + τ * (t - s))) 0 1 := hpath
    _ ≤ curveLength D γ s t := curveLength_affine_reparam_le D γ hst

/-- Monotonicity of the `D`-length in the interval (no metric axioms needed). -/
theorem curveLength_mono_Icc (D : ℂ → ℂ → ℝ) (p : ℝ → ℂ) {a b c d₁ : ℝ}
    (hac : c ≤ a) (hbd : b ≤ d₁) :
    curveLength D p a b ≤ curveLength D p c d₁ := by
  unfold curveLength
  refine iSup_le fun q => ?_
  obtain ⟨n, u, hu⟩ := q
  exact le_iSup_of_le (n, ⟨u, hu.1, fun i => ⟨hac.trans (hu.2 i).1, (hu.2 i).2.trans hbd⟩⟩) le_rfl

end HarmonicBalls
