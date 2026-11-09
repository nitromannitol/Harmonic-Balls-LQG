import Mathlib
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.Laplacian
import HarmonicBalls.Proofs.Sec11.ClosureScales.GaussianCircleTestIntegral
import HarmonicBalls.Proofs.Sec11.ClosureScales.RouteAPairingSecondMoment

/-!
# Uniform Fourier second moments and weighted summability of cut-off GFF pairings

Let `(hC, hcirc)` be a whole-plane Gaussian free field, `IsWholePlaneGFF P hC hcirc`, and let `χ : ℂ → ℝ` be a test
function on `ℂ`, `IsTestFunction Set.univ χ`. For a period `L : ℝ` and a frequency `k = (k₁, k₂) : ℤ × ℤ` the real
Fourier tests are

* `cutoffCosTest χ L k x = χ x * cos ((2π/L) (k₁ x_re + k₂ x_im))`,
* `cutoffSinTest χ L k x = χ x * sin ((2π/L) (k₁ x_re + k₂ x_im))`.

This file formalizes the uniform Fourier step of the written argument (`sec11-proof-r10.tex`, lines 1064-1074):

1. both tests are test functions on `ℂ` (`isTestFunction_cutoffCosTest`, `isTestFunction_cutoffSinTest`);
2. the lattice weight `(1 + k₁² + k₂²)^(-2)` is summable over `ℤ × ℤ` (`summable_frequencyWeight`);
3. the second moments `E[(hC cos_k)²]` and `E[(hC sin_k)²]` are bounded by one constant independent of `k`
   (`IsWholePlaneGFF.exists_integral_sq_cutoffTest_le`), by the pairing bound
   `IsWholePlaneGFF.integral_sq_pairing_le`, the compact support of `χ` and `|sin|, |cos| ≤ 1`;
4. the weighted series `∑_k (1 + k₁² + k₂²)^(-2) ((hC cos_k)² + (hC sin_k)²)` is summable on a measurable event of
   full measure (`IsWholePlaneGFF.exists_measurable_conull_cutoffFourier`), by Tonelli for nonnegative series
   (`exists_measurable_conull_summable_of_tsum_lintegral_ne_top`);
5. for a countable family of cut-offs the same holds on one measurable conull event
   (`IsWholePlaneGFF.exists_measurable_conull_cutoffFourier_countable`).

Every statement holds for each real period `L`, so the hypothesis `0 < L` of the written argument is not assumed.
The only hypotheses are `IsWholePlaneGFF` and `IsTestFunction`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- The real Fourier cosine test at frequency `k : ℤ × ℤ` on the period-`L` torus, cut off by `χ`:
`x ↦ χ x * cos ((2π/L) (k₁ x_re + k₂ x_im))`. -/
def cutoffCosTest (χ : ℂ → ℝ) (L : ℝ) (k : ℤ × ℤ) : ℂ → ℝ :=
  fun x => χ x * Real.cos ((2 * Real.pi / L) * ((k.1 : ℝ) * x.re + (k.2 : ℝ) * x.im))

/-- The real Fourier sine test at frequency `k : ℤ × ℤ`: `x ↦ χ x * sin ((2π/L) (k₁ x_re + k₂ x_im))`. -/
def cutoffSinTest (χ : ℂ → ℝ) (L : ℝ) (k : ℤ × ℤ) : ℂ → ℝ :=
  fun x => χ x * Real.sin ((2 * Real.pi / L) * ((k.1 : ℝ) * x.re + (k.2 : ℝ) * x.im))

/-- The smooth phase `x ↦ (2π/L) (k₁ x_re + k₂ x_im)` of the Fourier tests. -/
theorem contDiff_cutoffPhase (L : ℝ) (k : ℤ × ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℂ => (2 * Real.pi / L) * ((k.1 : ℝ) * x.re + (k.2 : ℝ) * x.im)) :=
  contDiff_const.mul ((contDiff_const.mul Complex.reCLM.contDiff).add
    (contDiff_const.mul Complex.imCLM.contDiff))

/-- Each cosine test is a test function on `ℂ`: the cut-off `χ` times a smooth factor, with compact support. -/
theorem isTestFunction_cutoffCosTest {χ : ℂ → ℝ} (hχ : IsTestFunction Set.univ χ) (L : ℝ) (k : ℤ × ℤ) :
    IsTestFunction Set.univ (cutoffCosTest χ L k) :=
  ⟨hχ.1.mul (Real.contDiff_cos.comp (contDiff_cutoffPhase L k)), hχ.2.1.mul_right, Set.subset_univ _⟩

/-- Each sine test is a test function on `ℂ`. -/
theorem isTestFunction_cutoffSinTest {χ : ℂ → ℝ} (hχ : IsTestFunction Set.univ χ) (L : ℝ) (k : ℤ × ℤ) :
    IsTestFunction Set.univ (cutoffSinTest χ L k) :=
  ⟨hχ.1.mul (Real.contDiff_sin.comp (contDiff_cutoffPhase L k)), hχ.2.1.mul_right, Set.subset_univ _⟩

/-- The lattice weight `(1 + k₁² + k₂²)^(-2)` is nonnegative. -/
theorem frequencyWeight_nonneg (k : ℤ × ℤ) : 0 ≤ (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) :=
  zpow_nonneg (by positivity) _

/-- The one-dimensional weight `(1 + n²)^(-1)` is summable over `ℤ`. It is bounded by the p-series weight `1/n²`
for `n ≠ 0` (a finite set of exceptions, handled by `Summable.of_norm_bounded_eventually`), and
`Real.summable_one_div_int_pow` applies with exponent `2`. -/
theorem summable_one_add_sq_zpow_neg_one :
    Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ (-1 : ℤ)) := by
  have hp : Summable (fun n : ℤ => 1 / (n : ℝ) ^ 2) := Real.summable_one_div_int_pow.mpr (by norm_num)
  refine Summable.of_norm_bounded_eventually hp ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hpos : (0 : ℝ) ≤ 1 + (n : ℝ) ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (zpow_nonneg hpos _), zpow_neg_one, one_div]
  exact inv_anti₀ hn2 (by linarith)

/-- The splitting inequality `(1 + a² + b²)^(-2) ≤ (1 + a²)^(-1) (1 + b²)^(-1)`. It follows from
`(1 + a²)(1 + b²) ≤ (1 + a² + b²)²`, whose difference is `a⁴ + b⁴ + a²b² + a² + b²`. -/
theorem frequencyWeight_le_prod (a b : ℝ) :
    (1 + a ^ 2 + b ^ 2) ^ (-2 : ℤ) ≤ (1 + a ^ 2) ^ (-1 : ℤ) * (1 + b ^ 2) ^ (-1 : ℤ) := by
  have hdiff : (1 + a ^ 2 + b ^ 2) ^ 2 - (1 + a ^ 2) * (1 + b ^ 2)
      = a ^ 4 + b ^ 4 + a ^ 2 * b ^ 2 + a ^ 2 + b ^ 2 := by ring
  have hnn : (0 : ℝ) ≤ a ^ 4 + b ^ 4 + a ^ 2 * b ^ 2 + a ^ 2 + b ^ 2 := by positivity
  have hle : (1 + a ^ 2) * (1 + b ^ 2) ≤ (1 + a ^ 2 + b ^ 2) ^ 2 := by linarith
  have e2 : ∀ x : ℝ, x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := fun x => by rw [zpow_neg, zpow_ofNat]
  rw [e2, zpow_neg_one, zpow_neg_one, ← mul_inv]
  exact inv_anti₀ (by positivity) hle

/-- **Lattice summability from its factors.** If the one-dimensional weight `(1 + n²)^(-1)` is summable over `ℤ` and
the splitting inequality holds, then `(1 + k₁² + k₂²)^(-2)` is summable over `ℤ × ℤ`: the weight is dominated by the
product of the one-dimensional weights, and `Summable.mul_of_nonneg` sums the product. -/
theorem summable_frequencyWeight_of_factors
    (h1 : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ (-1 : ℤ)))
    (hkey : ∀ a b : ℝ, (1 + a ^ 2 + b ^ 2) ^ (-2 : ℤ) ≤ (1 + a ^ 2) ^ (-1 : ℤ) * (1 + b ^ 2) ^ (-1 : ℤ)) :
    Summable (fun k : ℤ × ℤ => (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ)) := by
  have hnn : ∀ n : ℤ, (0 : ℝ) ≤ (1 + (n : ℝ) ^ 2) ^ (-1 : ℤ) := fun n => zpow_nonneg (by positivity) _
  exact Summable.of_nonneg_of_le (fun k => zpow_nonneg (by positivity) _)
    (fun k => hkey (k.1 : ℝ) (k.2 : ℝ)) (Summable.mul_of_nonneg h1 h1 hnn hnn)

/-- **Lattice summability.** The weight `(1 + k₁² + k₂²)^(-2)` is summable over `ℤ × ℤ`. -/
theorem summable_frequencyWeight :
    Summable (fun k : ℤ × ℤ => (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ)) :=
  summable_frequencyWeight_of_factors summable_one_add_sq_zpow_neg_one frequencyWeight_le_prod

/-- A test function vanishes outside one fixed ball, so one radius serves for all Fourier tests. -/
theorem exists_radius_eq_zero_of_isTestFunction {χ : ℂ → ℝ} (hχ : IsTestFunction Set.univ χ) :
    ∃ M : ℝ, ∀ x : ℂ, x ∉ ball (0 : ℂ) M → χ x = 0 := by
  obtain ⟨R, hR⟩ := hχ.2.1.isCompact.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨R + 1, fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx ?_⟩
  have hxR : dist x 0 ≤ R := mem_closedBall.mp (hR h)
  rw [mem_ball]
  linarith

/-- The Fourier cosine test is bounded by the bound of the cut-off, uniformly in `k`. -/
theorem abs_cutoffCosTest_le {χ : ℂ → ℝ} {B : ℝ} (hB : ∀ x, |χ x| ≤ B) (L : ℝ) (k : ℤ × ℤ) (x : ℂ) :
    |cutoffCosTest χ L k x| ≤ B := by
  simp only [cutoffCosTest]
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)).trans (hB x)

/-- The Fourier sine test is bounded by the bound of the cut-off, uniformly in `k`. -/
theorem abs_cutoffSinTest_le {χ : ℂ → ℝ} {B : ℝ} (hB : ∀ x, |χ x| ≤ B) (L : ℝ) (k : ℤ × ℤ) (x : ℂ) :
    |cutoffSinTest χ L k x| ≤ B := by
  simp only [cutoffSinTest]
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)).trans (hB x)

/-- The square of the Fourier cosine test is dominated by the square of the cut-off, uniformly in `k`. -/
theorem cutoffCosTest_sq_le (χ : ℂ → ℝ) (L : ℝ) (k : ℤ × ℤ) (x : ℂ) :
    cutoffCosTest χ L k x ^ 2 ≤ χ x ^ 2 := by
  simp only [cutoffCosTest]
  rw [mul_pow]
  exact mul_le_of_le_one_right (sq_nonneg _) (Real.cos_sq_le_one _)

/-- The square of the Fourier sine test is dominated by the square of the cut-off, uniformly in `k`. -/
theorem cutoffSinTest_sq_le (χ : ℂ → ℝ) (L : ℝ) (k : ℤ × ℤ) (x : ℂ) :
    cutoffSinTest χ L k x ^ 2 ≤ χ x ^ 2 := by
  simp only [cutoffSinTest]
  rw [mul_pow]
  exact mul_le_of_le_one_right (sq_nonneg _) (Real.sin_sq_le_one _)

/-- The square of a test function is integrable (continuous with compact support). -/
theorem integrable_sq_of_isTestFunction {χ : ℂ → ℝ} (hχ : IsTestFunction Set.univ χ) :
    Integrable (fun x => χ x ^ 2) :=
  have hcont : Continuous (fun x => χ x ^ 2) := hχ.1.continuous.pow 2
  have hcpt : HasCompactSupport (fun x => χ x ^ 2) :=
    hχ.2.1.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  hcont.integrable_of_hasCompactSupport hcpt

/-- **Frequency-uniform Fourier second moment.** For a test function `χ` and a period `L`, one finite constant
`C ≥ 0` bounds the second moments of both Fourier pairings at every frequency `k`:
`E[(hC cos_k)²] ≤ C` and `E[(hC sin_k)²] ≤ C`. One may take `C = (2 K_M).toReal · ∫ χ²` with `K_M = kernelBoxConst M`
for a radius `M` outside which `χ` vanishes; this constant does not depend on `k`. -/
theorem IsWholePlaneGFF.exists_integral_sq_cutoffTest_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {χ : ℂ → ℝ} (hχ : IsTestFunction Set.univ χ) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℤ × ℤ,
      ∫ ω, (hC ω (cutoffCosTest χ L k)) ^ 2 ∂P ≤ C ∧ ∫ ω, (hC ω (cutoffSinTest χ L k)) ^ 2 ∂P ≤ C := by
  obtain ⟨M, hM⟩ := exists_radius_eq_zero_of_isTestFunction hχ
  obtain ⟨B, hB⟩ := hχ.1.continuous.bounded_above_of_compact_support hχ.2.1
  have hBχ : ∀ x, |χ x| ≤ B := fun x => by simpa only [Real.norm_eq_abs] using hB x
  have hI : 0 ≤ ∫ x, χ x ^ 2 := integral_nonneg fun x => sq_nonneg _
  refine ⟨(2 * kernelBoxConst M).toReal * ∫ x, χ x ^ 2, mul_nonneg ENNReal.toReal_nonneg hI,
    fun k => ⟨?_, ?_⟩⟩
  · have hsupp : ∀ x, x ∉ ball (0 : ℂ) M → cutoffCosTest χ L k x = 0 := fun x hx => by
      simp only [cutoffCosTest, hM x hx, zero_mul]
    have hcmp : ∫ x, cutoffCosTest χ L k x ^ 2 ≤ ∫ x, χ x ^ 2 :=
      integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) (integrable_sq_of_isTestFunction hχ)
        (ae_of_all _ fun x => cutoffCosTest_sq_le χ L k x)
    exact (hG.integral_sq_pairing_le (isTestFunction_cutoffCosTest hχ L k) hsupp
      (abs_cutoffCosTest_le hBχ L k)).trans (mul_le_mul_of_nonneg_left hcmp ENNReal.toReal_nonneg)
  · have hsupp : ∀ x, x ∉ ball (0 : ℂ) M → cutoffSinTest χ L k x = 0 := fun x hx => by
      simp only [cutoffSinTest, hM x hx, zero_mul]
    have hcmp : ∫ x, cutoffSinTest χ L k x ^ 2 ≤ ∫ x, χ x ^ 2 :=
      integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) (integrable_sq_of_isTestFunction hχ)
        (ae_of_all _ fun x => cutoffSinTest_sq_le χ L k x)
    exact (hG.integral_sq_pairing_le (isTestFunction_cutoffSinTest hχ L k) hsupp
      (abs_cutoffSinTest_le hBχ L k)).trans (mul_le_mul_of_nonneg_left hcmp ENNReal.toReal_nonneg)

/-- **Tonelli criterion.** Nonnegative measurable summands `F i` with finite expected sum
`∑_i E[F i] < ∞` are summable on a measurable event `S` with `P Sᶜ = 0`. -/
theorem exists_measurable_conull_summable_of_tsum_lintegral_ne_top {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {ι : Type*} [Countable ι] (F : ι → Ω → ℝ) (hF0 : ∀ i ω, 0 ≤ F i ω)
    (hFm : ∀ i, Measurable (F i)) (hfin : ∑' i, ∫⁻ ω, ENNReal.ofReal (F i ω) ∂P ≠ ⊤) :
    ∃ S : Set Ω, MeasurableSet S ∧ P Sᶜ = 0 ∧ ∀ ω ∈ S, Summable (fun i => F i ω) := by
  have hmeas : Measurable fun ω => ∑' i, ENNReal.ofReal (F i ω) :=
    Measurable.tsum fun i => (hFm i).ennreal_ofReal
  have hint : ∫⁻ ω, ∑' i, ENNReal.ofReal (F i ω) ∂P ≠ ⊤ := by
    rw [lintegral_tsum fun i => ((hFm i).ennreal_ofReal).aemeasurable]
    exact hfin
  have hae : ∀ᵐ ω ∂P, ∑' i, ENNReal.ofReal (F i ω) < ⊤ := ae_lt_top' hmeas.aemeasurable hint
  refine ⟨{ω | ∑' i, ENNReal.ofReal (F i ω) < ⊤}, measurableSet_lt hmeas measurable_const, ae_iff.mp hae, ?_⟩
  intro ω hω
  have hω' : ∑' i, ENNReal.ofReal (F i ω) < ⊤ := hω
  exact (ENNReal.summable_toReal hω'.ne).congr fun i => ENNReal.toReal_ofReal (hF0 i ω)

/-- **Weighted summability on a conull event (one cut-off).** For a test function `χ` and a period `L`, the series
`∑_k (1 + k₁² + k₂²)^(-2) ((hC ω cos_k)² + (hC ω sin_k)²)` is summable on a measurable event `S` with `P Sᶜ = 0`. -/
theorem IsWholePlaneGFF.exists_measurable_conull_cutoffFourier {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {χ : ℂ → ℝ} (hχ : IsTestFunction Set.univ χ) (L : ℝ) :
    ∃ S : Set Ω, MeasurableSet S ∧ P Sᶜ = 0 ∧ ∀ ω ∈ S, Summable (fun k : ℤ × ℤ =>
      (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) *
        ((hC ω (cutoffCosTest χ L k)) ^ 2 + (hC ω (cutoffSinTest χ L k)) ^ 2)) := by
  obtain ⟨C, hC0, hCb⟩ := hG.exists_integral_sq_cutoffTest_le hχ L
  have hint : ∀ k : ℤ × ℤ, Integrable (fun ω => (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) *
      ((hC ω (cutoffCosTest χ L k)) ^ 2 + (hC ω (cutoffSinTest χ L k)) ^ 2)) P := fun k =>
    ((GaussianCircleTestIntegral.memLp_pairing hG (isTestFunction_cutoffCosTest hχ L k)).integrable_sq.add
      (GaussianCircleTestIntegral.memLp_pairing hG (isTestFunction_cutoffSinTest hχ L k)).integrable_sq).const_mul _
  have hmeas : ∀ k : ℤ × ℤ, Measurable fun ω => (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) *
      ((hC ω (cutoffCosTest χ L k)) ^ 2 + (hC ω (cutoffSinTest χ L k)) ^ 2) := fun k =>
    (((hG.measurable_pairing _ (isTestFunction_cutoffCosTest hχ L k)).pow_const 2).add
      ((hG.measurable_pairing _ (isTestFunction_cutoffSinTest hχ L k)).pow_const 2)).const_mul _
  have hlint : ∀ k : ℤ × ℤ, ∫⁻ ω, ENNReal.ofReal ((1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) *
      ((hC ω (cutoffCosTest χ L k)) ^ 2 + (hC ω (cutoffSinTest χ L k)) ^ 2)) ∂P ≤
      ENNReal.ofReal (2 * C * (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ)) := by
    intro k
    have hnn : 0 ≤ᵐ[P] fun ω => (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) *
        ((hC ω (cutoffCosTest χ L k)) ^ 2 + (hC ω (cutoffSinTest χ L k)) ^ 2) :=
      ae_of_all _ fun ω => mul_nonneg (frequencyWeight_nonneg k) (add_nonneg (sq_nonneg _) (sq_nonneg _))
    rw [← ofReal_integral_eq_lintegral_ofReal (hint k) hnn]
    apply ENNReal.ofReal_le_ofReal
    have h1 : Integrable (fun ω => (hC ω (cutoffCosTest χ L k)) ^ 2) P :=
      (GaussianCircleTestIntegral.memLp_pairing hG (isTestFunction_cutoffCosTest hχ L k)).integrable_sq
    have h2 : Integrable (fun ω => (hC ω (cutoffSinTest χ L k)) ^ 2) P :=
      (GaussianCircleTestIntegral.memLp_pairing hG (isTestFunction_cutoffSinTest hχ L k)).integrable_sq
    obtain ⟨hc, hs⟩ := hCb k
    rw [integral_const_mul, integral_add h1 h2]
    calc _ ≤ (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) * (C + C) :=
          mul_le_mul_of_nonneg_left (add_le_add hc hs) (frequencyWeight_nonneg k)
      _ = 2 * C * (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) := by ring
  have hsum2 : Summable (fun k : ℤ × ℤ => 2 * C * (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ)) :=
    summable_frequencyWeight.mul_left (2 * C)
  have hfin : ∑' k : ℤ × ℤ, ENNReal.ofReal (2 * C * (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ)) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun k => mul_nonneg (mul_nonneg zero_le_two hC0) (frequencyWeight_nonneg k)) hsum2]
    exact ENNReal.ofReal_ne_top
  refine exists_measurable_conull_summable_of_tsum_lintegral_ne_top
    (fun (k : ℤ × ℤ) (ω : Ω) => (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) *
      ((hC ω (cutoffCosTest χ L k)) ^ 2 + (hC ω (cutoffSinTest χ L k)) ^ 2))
    (fun k ω => mul_nonneg (frequencyWeight_nonneg k) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    (fun k => hmeas k) ?_
  exact ne_top_of_le_ne_top hfin (ENNReal.tsum_le_tsum hlint)

/-- **Weighted summability, almost surely (one cut-off).** For a test function `χ` and a period `L`, the series
`∑_k (1 + k₁² + k₂²)^(-2) ((hC ω cos_k)² + (hC ω sin_k)²)` is summable for `P`-almost every `ω`. -/
theorem IsWholePlaneGFF.ae_summable_cutoffFourier {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {χ : ℂ → ℝ} (hχ : IsTestFunction Set.univ χ) (L : ℝ) :
    ∀ᵐ ω ∂P, Summable (fun k : ℤ × ℤ =>
      (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) *
        ((hC ω (cutoffCosTest χ L k)) ^ 2 + (hC ω (cutoffSinTest χ L k)) ^ 2)) := by
  obtain ⟨S, -, hS0, hSs⟩ := hG.exists_measurable_conull_cutoffFourier hχ L
  exact ae_iff.mpr (measure_mono_null (fun ω hω hS => hω (hSs ω hS)) hS0)

/-- **Countable cut-offs on one measurable conull event.** For a countable family `χ i` of test functions, the
weighted series is summable for every cut-off `i` simultaneously, on one measurable event `S` with `P Sᶜ = 0`. -/
theorem IsWholePlaneGFF.exists_measurable_conull_cutoffFourier_countable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {ι : Type*} [Countable ι] (χ : ι → ℂ → ℝ) (hχ : ∀ i, IsTestFunction Set.univ (χ i)) (L : ℝ) :
    ∃ S : Set Ω, MeasurableSet S ∧ P Sᶜ = 0 ∧ ∀ ω ∈ S, ∀ i : ι, Summable (fun k : ℤ × ℤ =>
      (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) *
        ((hC ω (cutoffCosTest (χ i) L k)) ^ 2 + (hC ω (cutoffSinTest (χ i) L k)) ^ 2)) := by
  choose S hSm hS0 hSs using fun i => hG.exists_measurable_conull_cutoffFourier (hχ i) L
  refine ⟨⋂ i, S i, MeasurableSet.iInter hSm, ?_, fun ω hω i => hSs i ω (Set.mem_iInter.mp hω i)⟩
  rw [Set.compl_iInter]
  exact measure_iUnion_null hS0

end HarmonicBalls

end
