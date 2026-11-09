import Mathlib

/-!
# Weighted Cauchy-Schwarz duality for sine/cosine Fourier coefficients on `ℤ × ℤ`

Frequencies are `k = (k₁, k₂) : ℤ × ℤ`. For real families `a, b` (the cosine and sine coordinates of a first
expansion) and `u, v` (the cosine and sine coordinates of a second one), the pairing series is
`∑_k (a k * u k + b k * v k)`. The literal weight is `w k = (1 + k₁² + k₂²)^(-2 : ℤ)`, the weight of
`CutoffFourierSummability.lean` (`frequencyWeight_nonneg`); the power `w k ^ (-1 : ℤ)` is written `(w k)⁻¹`.

Main results, in the `HarmonicBalls` namespace:

* `weightedFourier_duality`: if `∑_k w k * (a k ^ 2 + b k ^ 2)` and `∑_k (w k)⁻¹ * (u k ^ 2 + v k ^ 2)` are
  summable, then `∑_k |a k * u k + b k * v k|` and `∑_k (a k * u k + b k * v k)` are summable, and
  `|∑_k (a k * u k + b k * v k)| ≤ √(∑_k w k * (a k ^ 2 + b k ^ 2)) * √(∑_k (w k)⁻¹ * (u k ^ 2 + v k ^ 2))`.
* `weightedFourier_finite_sum_abs_le`: the same Cauchy-Schwarz bound for every finite partial sum.
* `weightedFourier_finite_tail_le`: for finite `S ⊆ T`, `|∑_T x - ∑_S x| ≤ √(∑_T F - ∑_S F) * √(∑_T G - ∑_S G)`,
  where `x k = a k * u k + b k * v k`, `F k = w k * (a k ^ 2 + b k ^ 2)` and `G k = (w k)⁻¹ * (u k ^ 2 + v k ^ 2)`.
* `weightedFourier_cauchy`: for every `ε > 0` there is a finite `R` with `|∑_T x - ∑_S x| ≤ ε` whenever
  `R ⊆ S ⊆ T` (the Cauchy criterion for the finite Fourier partial sums).

The proof uses the Euclidean Cauchy-Schwarz inequality in `ℝ²` at each frequency, Mathlib's finite
Cauchy-Schwarz for square roots (`Real.sum_sqrt_mul_sqrt_le`), Hölder's inequality for series with exponents
`2` and `2` (`Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg`), and the Cauchy criterion for summable
families (`summable_iff_cauchySeq_finset`). The file defines no distribution, Sobolev norm, decoder or step.
It is the summation prerequisite for the weighted square-summable Fourier coefficients of
`sec11-proof-r10.tex`, lines 1075-1087.
-/

namespace HarmonicBalls

section Core

variable {ι : Type*}

/-- Euclidean Cauchy-Schwarz in `ℝ²`, with the weight split as `√w * √w⁻¹`: for `w > 0`,
`|a u + b v| ≤ √(w (a² + b²)) * √(w⁻¹ (u² + v²))`. -/
theorem abs_mul_add_mul_le_sqrt_mul_sqrt {w a b u v : ℝ} (hw : 0 < w) :
    |a * u + b * v| ≤ Real.sqrt (w * (a ^ 2 + b ^ 2)) * Real.sqrt (w⁻¹ * (u ^ 2 + v ^ 2)) := by
  have hw0 : w ≠ 0 := hw.ne'
  have hF : 0 ≤ w * (a ^ 2 + b ^ 2) := mul_nonneg hw.le (by positivity)
  rw [← Real.sqrt_mul hF]
  have key : w * (a ^ 2 + b ^ 2) * (w⁻¹ * (u ^ 2 + v ^ 2)) = (a ^ 2 + b ^ 2) * (u ^ 2 + v ^ 2) := by
    linear_combination ((a ^ 2 + b ^ 2) * (u ^ 2 + v ^ 2)) * mul_inv_cancel₀ hw0
  rw [key, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a * v - b * u)])

/-- Pointwise bounds for the sine/cosine pairing with a positive weight `w`. -/
theorem pairing_pointwise {w a b u v : ι → ℝ} (hw : ∀ i, 0 < w i) :
    (∀ i, |a i * u i + b i * v i| ≤
        Real.sqrt (w i * (a i ^ 2 + b i ^ 2)) * Real.sqrt ((w i)⁻¹ * (u i ^ 2 + v i ^ 2))) ∧
      (∀ i, 0 ≤ w i * (a i ^ 2 + b i ^ 2)) ∧ (∀ i, 0 ≤ (w i)⁻¹ * (u i ^ 2 + v i ^ 2)) :=
  ⟨fun i => abs_mul_add_mul_le_sqrt_mul_sqrt (hw i),
    fun i => mul_nonneg (hw i).le (by positivity),
    fun i => mul_nonneg (inv_nonneg.mpr (hw i).le) (by positivity)⟩

/-- Hölder's inequality with exponents `2, 2`: the series `∑ √(F i) √(G i)` is summable and bounded by
`√(∑ F) * √(∑ G)`. -/
theorem summable_sqrt_mul_sqrt_and_tsum_le {F G : ι → ℝ} (hF0 : ∀ i, 0 ≤ F i) (hG0 : ∀ i, 0 ≤ G i)
    (hF : Summable F) (hG : Summable G) :
    Summable (fun i => Real.sqrt (F i) * Real.sqrt (G i)) ∧
      ∑' i, Real.sqrt (F i) * Real.sqrt (G i) ≤ Real.sqrt (∑' i, F i) * Real.sqrt (∑' i, G i) := by
  have hpow : ∀ x : ℝ, 0 ≤ x → Real.sqrt x ^ (2 : ℝ) = x := fun x hx => by
    rw [Real.rpow_two, Real.sq_sqrt hx]
  have hf : ∀ i, 0 ≤ Real.sqrt (F i) := fun i => Real.sqrt_nonneg _
  have hg : ∀ i, 0 ≤ Real.sqrt (G i) := fun i => Real.sqrt_nonneg _
  have hF2 : Summable fun i => Real.sqrt (F i) ^ (2 : ℝ) := hF.congr fun i => (hpow _ (hF0 i)).symm
  have hG2 : Summable fun i => Real.sqrt (G i) ^ (2 : ℝ) := hG.congr fun i => (hpow _ (hG0 i)).symm
  obtain ⟨hs, hle⟩ :=
    Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two hf hg hF2 hG2
  have hF' : ∑' i, Real.sqrt (F i) ^ (2 : ℝ) = ∑' i, F i := tsum_congr fun i => hpow _ (hF0 i)
  have hG' : ∑' i, Real.sqrt (G i) ^ (2 : ℝ) = ∑' i, G i := tsum_congr fun i => hpow _ (hG0 i)
  rw [hF', hG'] at hle
  rw [Real.sqrt_eq_rpow (∑' i, F i), Real.sqrt_eq_rpow (∑' i, G i)]
  exact ⟨hs, hle⟩

/-- Finite Cauchy-Schwarz: a pointwise domination `|x i| ≤ √(F i) √(G i)` bounds every finite sum. -/
theorem sum_abs_le_of_pointwise {x F G : ι → ℝ} (hx : ∀ i, |x i| ≤ Real.sqrt (F i) * Real.sqrt (G i))
    (hF0 : ∀ i, 0 ≤ F i) (hG0 : ∀ i, 0 ≤ G i) (S : Finset ι) :
    ∑ i ∈ S, |x i| ≤ Real.sqrt (∑ i ∈ S, F i) * Real.sqrt (∑ i ∈ S, G i) :=
  (Finset.sum_le_sum fun i _ => hx i).trans (Real.sum_sqrt_mul_sqrt_le S hF0 hG0)

/-- Summability of `|x|` and `x`, and the Cauchy-Schwarz bound `|∑ x| ≤ √(∑ F) √(∑ G)`. -/
theorem summable_and_tsum_le_of_pointwise {x F G : ι → ℝ}
    (hx : ∀ i, |x i| ≤ Real.sqrt (F i) * Real.sqrt (G i))
    (hF0 : ∀ i, 0 ≤ F i) (hG0 : ∀ i, 0 ≤ G i) (hF : Summable F) (hG : Summable G) :
    Summable (fun i => |x i|) ∧ Summable x ∧
      |∑' i, x i| ≤ Real.sqrt (∑' i, F i) * Real.sqrt (∑' i, G i) := by
  obtain ⟨hs, hle⟩ := summable_sqrt_mul_sqrt_and_tsum_le hF0 hG0 hF hG
  have habs : Summable (fun i => |x i|) := Summable.of_nonneg_of_le (fun i => abs_nonneg _) hx hs
  have hsum : Summable x := Summable.of_norm (by simpa only [Real.norm_eq_abs] using habs)
  have h1 : |∑' i, x i| ≤ ∑' i, |x i| := by
    simpa only [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := x) (by simpa only [Real.norm_eq_abs] using habs)
  exact ⟨habs, hsum, h1.trans ((Summable.tsum_le_tsum hx habs hs).trans hle)⟩

/-- Finite tail bound: for `S ⊆ T`, `|∑_T x - ∑_S x| ≤ √(∑_T F - ∑_S F) * √(∑_T G - ∑_S G)`. -/
theorem abs_sub_le_sqrt_of_pointwise [DecidableEq ι] {x F G : ι → ℝ}
    (hx : ∀ i, |x i| ≤ Real.sqrt (F i) * Real.sqrt (G i))
    (hF0 : ∀ i, 0 ≤ F i) (hG0 : ∀ i, 0 ≤ G i) {S T : Finset ι} (hST : S ⊆ T) :
    |(∑ i ∈ T, x i) - ∑ i ∈ S, x i| ≤
      Real.sqrt ((∑ i ∈ T, F i) - ∑ i ∈ S, F i) * Real.sqrt ((∑ i ∈ T, G i) - ∑ i ∈ S, G i) := by
  have hx' : (∑ i ∈ T, x i) - ∑ i ∈ S, x i = ∑ i ∈ T \ S, x i := by
    linarith [Finset.sum_sdiff (f := x) hST]
  have hF' : (∑ i ∈ T, F i) - ∑ i ∈ S, F i = ∑ i ∈ T \ S, F i := by
    linarith [Finset.sum_sdiff (f := F) hST]
  have hG' : (∑ i ∈ T, G i) - ∑ i ∈ S, G i = ∑ i ∈ T \ S, G i := by
    linarith [Finset.sum_sdiff (f := G) hST]
  rw [hx', hF', hG']
  exact (Finset.abs_sum_le_sum_abs x (T \ S)).trans (sum_abs_le_of_pointwise hx hF0 hG0 (T \ S))

/-- Cauchy criterion for the finite partial sums: for `ε > 0` some finite `R` gives
`|∑_T x - ∑_S x| ≤ ε` whenever `R ⊆ S ⊆ T`. -/
theorem exists_finset_abs_sub_le_of_pointwise [DecidableEq ι] {x F G : ι → ℝ}
    (hx : ∀ i, |x i| ≤ Real.sqrt (F i) * Real.sqrt (G i))
    (hF0 : ∀ i, 0 ≤ F i) (hG0 : ∀ i, 0 ≤ G i) (hF : Summable F) (hG : Summable G)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : Finset ι, ∀ S T : Finset ι, R ⊆ S → S ⊆ T →
      |(∑ i ∈ T, x i) - ∑ i ∈ S, x i| ≤ ε := by
  obtain ⟨NF, hNF⟩ := summable_iff_vanishing_norm.mp hF ε hε
  obtain ⟨NG, hNG⟩ := summable_iff_vanishing_norm.mp hG ε hε
  refine ⟨NF ∪ NG, fun S T hRS hST => ?_⟩
  -- the difference set `T \ S` is disjoint from every finite set contained in `S`
  have hdisj : ∀ R' : Finset ι, R' ⊆ S → Disjoint (T \ S) R' := fun R' hR' =>
    Finset.disjoint_left.mpr fun i hi hi' => (Finset.mem_sdiff.mp hi).2 (hR' hi')
  have hFd : ‖∑ i ∈ T \ S, F i‖ < ε :=
    hNF _ (hdisj NF fun i hi => hRS (Finset.mem_union_left _ hi))
  have hGd : ‖∑ i ∈ T \ S, G i‖ < ε :=
    hNG _ (hdisj NG fun i hi => hRS (Finset.mem_union_right _ hi))
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => hF0 i)] at hFd
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => hG0 i)] at hGd
  have hx' : |(∑ i ∈ T, x i) - ∑ i ∈ S, x i| ≤
      Real.sqrt (∑ i ∈ T \ S, F i) * Real.sqrt (∑ i ∈ T \ S, G i) := by
    have e : (∑ i ∈ T, x i) - ∑ i ∈ S, x i = ∑ i ∈ T \ S, x i := by
      linarith [Finset.sum_sdiff (f := x) hST]
    rw [e]
    exact (Finset.abs_sum_le_sum_abs x (T \ S)).trans (sum_abs_le_of_pointwise hx hF0 hG0 (T \ S))
  calc |(∑ i ∈ T, x i) - ∑ i ∈ S, x i|
      ≤ Real.sqrt (∑ i ∈ T \ S, F i) * Real.sqrt (∑ i ∈ T \ S, G i) := hx'
    _ ≤ Real.sqrt ε * Real.sqrt ε :=
        mul_le_mul (Real.sqrt_le_sqrt hFd.le) (Real.sqrt_le_sqrt hGd.le) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = ε := Real.mul_self_sqrt hε.le

end Core

/-- The literal frequency weight `w(k) = (1 + k₁² + k₂²)^(-2)` is strictly positive on `ℤ × ℤ`. -/
theorem frequencyWeight_pos (k : ℤ × ℤ) : 0 < (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) :=
  zpow_pos (by positivity) _

/-- **Weighted Cauchy-Schwarz duality on `ℤ × ℤ`.** Let `x k = a k * u k + b k * v k` (cosine times cosine
plus sine times sine). If `∑_k w k * (a k ^ 2 + b k ^ 2)` and `∑_k (w k)⁻¹ * (u k ^ 2 + v k ^ 2)` are summable
for the literal weight `w k = (1 + k₁² + k₂²)^(-2)`, then `∑_k |x k|` and `∑_k x k` are summable and
`|∑_k x k| ≤ √(∑_k w k * (a k ^ 2 + b k ^ 2)) * √(∑_k (w k)⁻¹ * (u k ^ 2 + v k ^ 2))`. -/
theorem weightedFourier_duality (a b u v : ℤ × ℤ → ℝ)
    (ha : Summable fun k : ℤ × ℤ => (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) * (a k ^ 2 + b k ^ 2))
    (hu : Summable fun k : ℤ × ℤ =>
      ((1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ))⁻¹ * (u k ^ 2 + v k ^ 2)) :
    (Summable fun k : ℤ × ℤ => |a k * u k + b k * v k|) ∧
      Summable (fun k : ℤ × ℤ => a k * u k + b k * v k) ∧
      |∑' k : ℤ × ℤ, (a k * u k + b k * v k)| ≤
        Real.sqrt (∑' k : ℤ × ℤ, (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) * (a k ^ 2 + b k ^ 2)) *
          Real.sqrt (∑' k : ℤ × ℤ, ((1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ))⁻¹ * (u k ^ 2 + v k ^ 2)) := by
  obtain ⟨hx, hF0, hG0⟩ := pairing_pointwise
    (w := fun k : ℤ × ℤ => (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ)) frequencyWeight_pos
    (a := a) (b := b) (u := u) (v := v)
  exact summable_and_tsum_le_of_pointwise hx hF0 hG0 ha hu

/-- **Finite partial sums.** The Cauchy-Schwarz bound holds for every finite set `S ⊆ ℤ × ℤ` of frequencies. -/
theorem weightedFourier_finite_sum_abs_le (a b u v : ℤ × ℤ → ℝ) (S : Finset (ℤ × ℤ)) :
    ∑ k ∈ S, |a k * u k + b k * v k| ≤
      Real.sqrt (∑ k ∈ S, (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) * (a k ^ 2 + b k ^ 2)) *
        Real.sqrt (∑ k ∈ S, ((1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ))⁻¹ * (u k ^ 2 + v k ^ 2)) := by
  obtain ⟨hx, hF0, hG0⟩ := pairing_pointwise
    (w := fun k : ℤ × ℤ => (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ)) frequencyWeight_pos
    (a := a) (b := b) (u := u) (v := v)
  exact sum_abs_le_of_pointwise hx hF0 hG0 S

/-- **Finite-tail bound.** For finite `S ⊆ T ⊆ ℤ × ℤ`, the difference of the partial sums
`∑_T x - ∑_S x` is bounded by the square roots of the weighted tails `∑_T F - ∑_S F` and `∑_T G - ∑_S G`. -/
theorem weightedFourier_finite_tail_le (a b u v : ℤ × ℤ → ℝ) {S T : Finset (ℤ × ℤ)} (hST : S ⊆ T) :
    |(∑ k ∈ T, (a k * u k + b k * v k)) - ∑ k ∈ S, (a k * u k + b k * v k)| ≤
      Real.sqrt ((∑ k ∈ T, (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) * (a k ^ 2 + b k ^ 2)) -
          ∑ k ∈ S, (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) * (a k ^ 2 + b k ^ 2)) *
        Real.sqrt ((∑ k ∈ T, ((1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ))⁻¹ * (u k ^ 2 + v k ^ 2)) -
          ∑ k ∈ S, ((1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ))⁻¹ * (u k ^ 2 + v k ^ 2)) := by
  obtain ⟨hx, hF0, hG0⟩ := pairing_pointwise
    (w := fun k : ℤ × ℤ => (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ)) frequencyWeight_pos
    (a := a) (b := b) (u := u) (v := v)
  exact abs_sub_le_sqrt_of_pointwise hx hF0 hG0 hST

/-- **Cauchy bound for the Fourier partial sums.** If the weighted energies are summable (as in
`weightedFourier_duality`), then for every `ε > 0` there is a finite `R ⊆ ℤ × ℤ` such that
`|∑_T x - ∑_S x| ≤ ε` whenever `R ⊆ S ⊆ T`. -/
theorem weightedFourier_cauchy (a b u v : ℤ × ℤ → ℝ)
    (ha : Summable fun k : ℤ × ℤ => (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) * (a k ^ 2 + b k ^ 2))
    (hu : Summable fun k : ℤ × ℤ =>
      ((1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ))⁻¹ * (u k ^ 2 + v k ^ 2))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : Finset (ℤ × ℤ), ∀ S T : Finset (ℤ × ℤ), R ⊆ S → S ⊆ T →
      |(∑ k ∈ T, (a k * u k + b k * v k)) - ∑ k ∈ S, (a k * u k + b k * v k)| ≤ ε := by
  obtain ⟨hx, hF0, hG0⟩ := pairing_pointwise
    (w := fun k : ℤ × ℤ => (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ)) frequencyWeight_pos
    (a := a) (b := b) (u := u) (v := v)
  exact exists_finset_abs_sub_le_of_pointwise hx hF0 hG0 ha hu hε

end HarmonicBalls
