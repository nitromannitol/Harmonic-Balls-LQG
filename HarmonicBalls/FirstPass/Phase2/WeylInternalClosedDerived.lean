import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.Steps.Sec11.MetricArcLength
import HarmonicBalls.Steps.Sec11.CurveLengthReparam
import HarmonicBalls.Steps.Sec11.WeylPathSegments
import HarmonicBalls.Steps.Sec11.WeylPathReverse

/-! # The closed-set Weyl comparison of internal metrics is derived

`WeylInternalClosedFrozen` (`FirstPass/Frozen/S11c.lean`, line 180; written argument in its docstring, "Why it holds")
is derived with no new hypothesis. The frozen Prop itself is not edited.

Written argument. Let `P` be a path in `U` with finite `D`-length `L`. Reparametrize `P` by `D`-arclength: `q : [0, L] → ℂ`
is `D`-length parametrized, has the same image as `P`, and `q (s t) = P t` where `s t` is the `D`-length of `P` on `[0, t]`
(`IsEuclideanLengthMetric.exists_lengthParametrized_with_tracking`, `IsEuclideanLengthMetric.cumulative_curveLength_properties`).
For `0 ≤ a ≤ b ≤ L`, the sub-arc `r ↦ q (a + r)`, `r ∈ [0, b - a]`, is a competitor in the infimum defining
`weylScaling D ξ f (q a) (q b)`; its weighted cost is at most `e^B (b - a)`, because `ξ f ≤ B` on the image of `q`, which lies
in `U`. Reversing `q` gives the same bound for `weylScaling (q b) (q a)`. Summing over a partition of `[0, 1]` and telescoping,
the `E`-length of `P` is at most `e^B` times the `D`-length of `P`. The infimum over paths in `U` gives the claim.

Closedness of `U` is not used: the argument needs only that the path lies in `U`. -/

namespace HarmonicBalls

open Set MeasureTheory
open scoped ENNReal NNReal

/-- A `D`-arclength parametrized curve `q` on `[0, L]` with weight `ξ f ≤ B` along it: the sub-arc `r ↦ q (a + r)` is a
competitor in `weylScaling`, so `weylScaling D ξ f (q a) (q b) ≤ e^B (b - a)` for `0 ≤ a ≤ b ≤ L`. -/
theorem weylScaling_le_of_subarc {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ B : ℝ} {f : ℂ → ℝ}
    {q : ℝ → ℂ} {L : ℝ} (hq : IsLengthParametrized D q L)
    (hw : ∀ x ∈ Icc 0 L, ξ * f (q x) ≤ B) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L) :
    weylScaling D ξ f (q a) (q b) ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (b - a) := by
  have hsub : IsLengthParametrized D (fun t => q (a + t)) (b - a) :=
    hD.isLengthParametrized_subcurve hq ha hab hb
  have h0 : (fun t => q (a + t)) 0 = q a := by simp
  have hT : (fun t => q (a + t)) (b - a) = q b := by simp
  refine iInf_le_of_le (b - a) (iInf_le_of_le (fun t => q (a + t)) (iInf_le_of_le hsub
    (iInf_le_of_le h0 (iInf_le_of_le hT ?_))))
  calc ∫⁻ t in Icc 0 (b - a), ENNReal.ofReal (Real.exp (ξ * f ((fun t => q (a + t)) t)))
      ≤ ∫⁻ _ in Icc 0 (b - a), ENNReal.ofReal (Real.exp B) := by
        refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        exact hw (a + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    _ = ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (b - a) := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero]

/-- Both orientations: for `0 ≤ a ≤ b ≤ L`, `weylScaling (q a) (q b)` and `weylScaling (q b) (q a)` are at most
`e^B (b - a)`. The second follows from the first applied to the reversed curve `t ↦ q (L - t)`. -/
theorem weylScaling_le_of_subarc_both {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ B : ℝ} {f : ℂ → ℝ}
    {q : ℝ → ℂ} {L : ℝ} (hq : IsLengthParametrized D q L)
    (hw : ∀ x ∈ Icc 0 L, ξ * f (q x) ≤ B) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ L) :
    weylScaling D ξ f (q a) (q b) ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (b - a) ∧
      weylScaling D ξ f (q b) (q a) ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (b - a) := by
  refine ⟨weylScaling_le_of_subarc hD hq hw ha hab hb, ?_⟩
  have hr : IsLengthParametrized D (fun t => q (L - t)) L := hD.isLengthParametrized_reverse hq
  have hwr : ∀ x ∈ Icc 0 L, ξ * f ((fun t => q (L - t)) x) ≤ B := fun x hx =>
    hw (L - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have h := weylScaling_le_of_subarc hD hr hwr (a := L - b) (b := L - a)
    (by linarith) (by linarith) (by linarith)
  simp only [sub_sub_cancel] at h
  rw [show L - a - (L - b) = b - a by ring] at h
  exact h

/-- Telescoping bound for partition sums: if `σ` is nondecreasing with `0 ≤ σ 0` and `σ N ≤ L`, and each term is at most
`c (σ (i+1) - σ i)`, the sum over `range N` is at most `c L`. -/
theorem sum_le_of_telescope {c : ℝ≥0∞} {σ : ℕ → ℝ} {L : ℝ} {d : ℕ → ℝ≥0∞} (N : ℕ)
    (hσ : ∀ i, σ i ≤ σ (i + 1)) (h0 : 0 ≤ σ 0) (hN : σ N ≤ L)
    (hd : ∀ i ∈ Finset.range N, d i ≤ c * ENNReal.ofReal (σ (i + 1) - σ i)) :
    ∑ i ∈ Finset.range N, d i ≤ c * ENNReal.ofReal L := by
  calc ∑ i ∈ Finset.range N, d i
      ≤ ∑ i ∈ Finset.range N, c * ENNReal.ofReal (σ (i + 1) - σ i) := Finset.sum_le_sum hd
    _ = c * ∑ i ∈ Finset.range N, ENNReal.ofReal (σ (i + 1) - σ i) := by rw [Finset.mul_sum]
    _ = c * ENNReal.ofReal (∑ i ∈ Finset.range N, (σ (i + 1) - σ i)) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sub_nonneg.mpr (hσ i))]
    _ = c * ENNReal.ofReal (σ N - σ 0) := by rw [Finset.sum_range_sub σ N]
    _ ≤ c * ENNReal.ofReal L :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (by linarith)) zero_le

/-- A partition bound for the `E`-length of a curve `p` on `[0, 1]` gives a bound for `curveLength E p 0 1`. -/
theorem curveLength_le_of_partition_bound {E : ℂ → ℂ → ℝ} {p : ℝ → ℂ} {M : ℝ≥0∞}
    (h : ∀ (N : ℕ) (u : ℕ → ℝ), Monotone u → (∀ i, u i ∈ Icc (0:ℝ) 1) →
      ∑ i ∈ Finset.range N, ENNReal.ofReal (E (p (u (i + 1))) (p (u i))) ≤ M) :
    curveLength E p 0 1 ≤ M := by
  unfold curveLength
  exact iSup_le fun ⟨N, u, hu, hI⟩ => h N u hu hI

/-- For a path `P` in `U`, with `E` the Weyl scaling of `D` by `f` and `ξ f ≤ B` on `U`, the `E`-length of `P` is at most
`e^B` times its `D`-length. The path is reparametrized by its `D`-arclength; each sub-arc is a competitor in `weylScaling`. -/
theorem pathLength_le_of_weylScaling {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ B : ℝ} {f : ℂ → ℝ}
    {U : Set ℂ} (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hweight : ∀ z ∈ U, ξ * f z ≤ B) {x y : ℂ} (P : Path x y) (hP : ∀ t, P t ∈ U) :
    pathLength E P ≤ ENNReal.ofReal (Real.exp B) * pathLength D P := by
  have hc0 : ENNReal.ofReal (Real.exp B) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos B)).ne'
  unfold pathLength
  by_cases hfin : curveLength D P.extend 0 1 = ⊤
  · rw [hfin, ENNReal.mul_top hc0]
    exact le_top
  have hlt : curveLength D P.extend 0 1 < ⊤ := lt_top_iff_ne_top.mpr hfin
  have hcont : ContinuousOn P.extend (Icc 0 1) := P.continuous_extend.continuousOn
  have hPU : ∀ t ∈ Icc (0:ℝ) 1, P.extend t ∈ U := fun t ht => by
    rw [Path.extend_apply P ht]
    exact hP ⟨t, ht⟩
  obtain ⟨q, hq, -, -, htrack⟩ := hD.exists_lengthParametrized_with_tracking zero_le_one hcont hlt
  obtain ⟨-, hmono, -, himg⟩ := hD.cumulative_curveLength_properties zero_le_one hcont hlt
  have hmono' : ∀ a b : ℝ, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 → a ≤ b →
      (curveLength D P.extend 0 a).toReal ≤ (curveLength D P.extend 0 b).toReal :=
    fun a b ha hb hab => hmono ha hb hab
  -- the image of `q` on `[0, L]` is the image of `P` on `[0, 1]`, hence lies in `U`
  have hqU : ∀ x ∈ Icc (0:ℝ) (curveLength D P.extend 0 1).toReal, q x ∈ U := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := (Set.ext_iff.mp himg x).mpr hx
    show q (curveLength D P.extend 0 t).toReal ∈ U
    rw [htrack t ht]
    exact hPU t ht
  have hw : ∀ x ∈ Icc (0:ℝ) (curveLength D P.extend 0 1).toReal, ξ * f (q x) ≤ B :=
    fun x hx => hweight _ (hqU x hx)
  have hsum : ∀ (N : ℕ) (u : ℕ → ℝ), Monotone u → (∀ i, u i ∈ Icc (0:ℝ) 1) →
      ∑ i ∈ Finset.range N, ENNReal.ofReal (E (P.extend (u (i + 1))) (P.extend (u i))) ≤
        ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (curveLength D P.extend 0 1).toReal := by
    intro N u hu hI
    have hσ : ∀ i, (curveLength D P.extend 0 (u i)).toReal ≤
        (curveLength D P.extend 0 (u (i + 1))).toReal :=
      fun i => hmono' _ _ (hI i) (hI (i + 1)) (hu (Nat.le_succ i))
    have hd : ∀ i ∈ Finset.range N, ENNReal.ofReal (E (P.extend (u (i + 1))) (P.extend (u i))) ≤
        ENNReal.ofReal (Real.exp B) *
          ENNReal.ofReal ((curveLength D P.extend 0 (u (i + 1))).toReal -
            (curveLength D P.extend 0 (u i)).toReal) := by
      intro i _
      have hL : (curveLength D P.extend 0 (u (i + 1))).toReal ≤
          (curveLength D P.extend 0 1).toReal :=
        hmono' _ _ (hI (i + 1)) (right_mem_Icc.mpr zero_le_one) (hI (i + 1)).2
      rw [hscale, ← htrack (u (i + 1)) (hI (i + 1)), ← htrack (u i) (hI i)]
      exact (weylScaling_le_of_subarc_both hD hq hw ENNReal.toReal_nonneg (hσ i) hL).2
    have hN : (curveLength D P.extend 0 (u N)).toReal ≤ (curveLength D P.extend 0 1).toReal :=
      hmono' _ _ (hI N) (right_mem_Icc.mpr zero_le_one) (hI N).2
    exact sum_le_of_telescope (σ := fun i => (curveLength D P.extend 0 (u i)).toReal) N hσ
      ENNReal.toReal_nonneg hN hd
  calc curveLength E P.extend 0 1
      ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (curveLength D P.extend 0 1).toReal :=
        curveLength_le_of_partition_bound (fun N u hu hI => hsum N u hu hI)
    _ = ENNReal.ofReal (Real.exp B) * curveLength D P.extend 0 1 := by
        rw [ENNReal.ofReal_toReal hfin]

/-- **Derived**: the closed-set Weyl comparison of internal metrics,
`WeylInternalClosedFrozen` (`FirstPass/Frozen/S11c.lean:180`), with no hypothesis added. Source as in its docstring:
paper Fact 2.2 III (corrected copy, lines 441-447); the open-set version is
`IsEuclideanLengthMetric.internalMetric_weylScaling_le`. -/
theorem weylInternalClosed_derived : WeylInternalClosedFrozen := by
  intro D E ξ B f U hD _hEnn hscale _hclosed hweight x y
  have hc0 : ENNReal.ofReal (Real.exp B) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos B)).ne'
  have hctop : ENNReal.ofReal (Real.exp B) ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold internalMetric
  calc ⨅ (P : Path x y) (_ : ∀ t, P t ∈ U), pathLength E P
      ≤ ⨅ (P : Path x y) (_ : ∀ t, P t ∈ U), ENNReal.ofReal (Real.exp B) * pathLength D P :=
        le_iInf₂ fun P hP => (iInf₂_le P hP).trans (pathLength_le_of_weylScaling hD hscale hweight P hP)
    _ = ENNReal.ofReal (Real.exp B) * ⨅ (P : Path x y) (_ : ∀ t, P t ∈ U), pathLength D P := by
        simp only [ENNReal.mul_iInf_of_ne hc0 hctop]

end HarmonicBalls
