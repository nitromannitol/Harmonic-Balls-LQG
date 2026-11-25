import HarmonicBalls.Proofs.Potential.ReflectedBrownianMarkov
import HarmonicBalls.Proofs.Potential.BrownianOriginOccupationDensity
import HarmonicBalls.Proofs.Potential.GreenPotentialHolder

/-!
# Green potentials of reflected Brownian motion in the unit square

The transition law of reflected Brownian motion in `K₀ = [0, 1]²` at time `r` is the image of the
planar Gaussian law `N(y, r)` under the fold. In one dimension the triangle wave `u` agrees at every
point with one of the maps `w ↦ w - 2n`, `w ↦ 2n - w`, so a function of `u(w)` is dominated by the
sum of its translates and reflections (`le_tsum_indicator_unitIntervalFold`). For `a, c ∈ [0, 1]`
every image `2n ± c` of `c` is at least as far from `a` as `c`, and at distance at least
`2|n| - 2`. Hence the folded Gaussian density is at most `2 √2 S` times the Gaussian density of
variance `2r`, where `S = ∑_{n ∈ ℤ} e^{2 - |n|}` (`lintegral_gaussianReal_unitIntervalFold_le`),
the reflection-of-the-Gaussian-kernel bound for the Neumann kernel of the square
(consultant note on target 12; Kigami, *Time changes of the Brownian motion*, Mem. AMS 259
(2019), Section 13). In two dimensions the fold acts coordinatewise
(`lintegral_planarGaussian_squareFold_le`).

With the Gaussian bound `e^{-u} ≤ u^{-θ}` (`ofReal_heatDensity_le`) and the Riesz potential bound
for measures with power ball bounds (`lintegral_norm_sub_rpow_neg_le`), the expected occupation
integral `E_y ∫_{(0,1]} g(b_s) ds` of reflected Brownian motion is bounded uniformly in the start
`y ∈ K₀` when `g dx` on `K₀` has finite mass and ball bounds `C ρ^β`
(`lintegral_windowOccupation_reflected_le`).
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess Metric
open scoped ENNReal NNReal

/-! ### The lattice sum -/

/-- The lattice sum `∑_{n ∈ ℤ} e^{2 - |n|}`. -/
noncomputable def foldLatticeSum : ℝ≥0∞ :=
  ∑' n : ℤ, ENNReal.ofReal (Real.exp (2 - |(n : ℝ)|))

theorem summable_exp_two_sub_abs_int : Summable fun n : ℤ => Real.exp (2 - |(n : ℝ)|) := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine (Real.summable_exp_neg_nat.mul_left (Real.exp 2)).congr fun n => ?_
    have h : |(((n : ℤ) : ℝ))| = (n : ℝ) := by simp
    rw [← Real.exp_add, h]
    ring_nf
  · refine (Real.summable_exp_neg_nat.mul_left (Real.exp 1)).congr fun n => ?_
    have h : |(((-((n : ℤ) + 1)) : ℤ) : ℝ)| = (n : ℝ) + 1 := by
      rw [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, abs_neg,
        abs_of_nonneg (by positivity)]
    rw [← Real.exp_add, h]
    ring_nf

theorem foldLatticeSum_lt_top : foldLatticeSum < ⊤ := by
  rw [foldLatticeSum, ← ENNReal.ofReal_tsum_of_nonneg (fun n => (Real.exp_pos _).le)
    summable_exp_two_sub_abs_int]
  exact ENNReal.ofReal_lt_top

/-! ### Distances to the images of a point under the reflections -/

theorem int_cast_le_neg_one_or_eq_zero_or_one_le (n : ℤ) :
    (n : ℝ) ≤ -1 ∨ (n : ℝ) = 0 ∨ 1 ≤ (n : ℝ) := by
  rcases lt_trichotomy n 0 with h | h | h
  · left
    exact_mod_cast (show n ≤ -1 by omega)
  · right; left
    exact_mod_cast h
  · right; right
    exact_mod_cast (show 1 ≤ n by omega)

/-- The translates `c + 2n` of a point `c ∈ [0, 1]` are at least as far from `a ∈ [0, 1]` as `c`,
and at distance at least `2|n| - 2`. -/
theorem sq_sub_le_sq_translate {a c : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1)
    (n : ℤ) : (c - a) ^ 2 ≤ (c - (a - 2 * n)) ^ 2 ∧
      4 * (|(n : ℝ)| - 2) ≤ (c - (a - 2 * n)) ^ 2 := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hc0, hc1⟩ := hc
  rcases int_cast_le_neg_one_or_eq_zero_or_one_le n with hn | hn | hn
  · rw [abs_of_neg (by linarith)]
    have hx : c - (a - 2 * n) ≤ 1 + 2 * n := by linarith
    constructor
    · nlinarith
    · nlinarith [mul_nonneg (show 0 ≤ (1 + 2 * (n : ℝ)) - (c - (a - 2 * n)) by linarith)
        (show 0 ≤ -((c - (a - 2 * n)) + (1 + 2 * n)) by linarith), sq_nonneg ((n : ℝ) + 1)]
  · rw [hn, abs_zero]
    constructor
    · nlinarith
    · nlinarith [sq_nonneg (c - a)]
  · rw [abs_of_pos (by linarith)]
    have hx : 2 * n - 1 ≤ c - (a - 2 * n) := by linarith
    constructor
    · nlinarith
    · nlinarith [mul_nonneg (show 0 ≤ (c - (a - 2 * n)) - (2 * (n : ℝ) - 1) by linarith)
        (show 0 ≤ (c - (a - 2 * n)) + (2 * n - 1) by linarith), sq_nonneg ((n : ℝ) - 1)]

/-- The reflections `2n - c` of a point `c ∈ [0, 1]` are at least as far from `a ∈ [0, 1]` as `c`,
and at distance at least `2|n| - 2`. -/
theorem sq_sub_le_sq_reflect {a c : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1)
    (n : ℤ) : (c - a) ^ 2 ≤ (c - (2 * n - a)) ^ 2 ∧
      4 * (|(n : ℝ)| - 2) ≤ (c - (2 * n - a)) ^ 2 := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hc0, hc1⟩ := hc
  rcases int_cast_le_neg_one_or_eq_zero_or_one_le n with hn | hn | hn
  · rw [abs_of_neg (by linarith)]
    constructor
    · nlinarith [mul_nonneg (show 0 ≤ c - n by linarith) (show 0 ≤ a - n by linarith)]
    · nlinarith [mul_nonneg (show 0 ≤ c - (2 * n - a) + 2 * n by linarith)
        (show 0 ≤ c - (2 * n - a) - 2 * n by linarith), sq_nonneg ((n : ℝ) + 1 / 2)]
  · rw [hn, abs_zero]
    constructor
    · nlinarith [mul_nonneg hc0 ha0]
    · nlinarith [sq_nonneg (c + a)]
  · rw [abs_of_pos (by linarith)]
    constructor
    · nlinarith [mul_nonneg (show 0 ≤ n - c by linarith) (show 0 ≤ n - a by linarith)]
    · nlinarith [mul_nonneg (show 0 ≤ (2 * n - a - c) - (2 * n - 2 : ℝ) by linarith)
        (show 0 ≤ (2 * n - a - c) + (2 * n - 2 : ℝ) by linarith), sq_nonneg ((n : ℝ) - 3 / 2)]

/-- The Gaussian density at an image point at distance `x` is at most `√2` times the Gaussian
density of twice the variance at `c`, times `e^{2 - |n|}`. -/
theorem gaussianPDFReal_image_le {a c x N : ℝ} {r : ℝ≥0} (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) ≤ 1)
    (hx1 : (c - a) ^ 2 ≤ x ^ 2) (hx2 : 4 * (|N| - 2) ≤ x ^ 2) :
    (Real.sqrt (2 * Real.pi * r))⁻¹ * Real.exp (-x ^ 2 / (2 * r)) ≤
      Real.sqrt 2 * gaussianPDFReal a (2 * r) c * Real.exp (2 - |N|) := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_mul, NNReal.coe_ofNat]
  have hs : Real.sqrt (2 * Real.pi * (2 * r)) = Real.sqrt 2 * Real.sqrt (2 * Real.pi * r) := by
    rw [show 2 * Real.pi * (2 * (r : ℝ)) = 2 * (2 * Real.pi * r) by ring,
      Real.sqrt_mul (by norm_num)]
  have hpos : 0 < Real.sqrt (2 * Real.pi * r) := Real.sqrt_pos.2 (by positivity)
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hpre : Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt (2 * Real.pi * r))⁻¹ =
      (Real.sqrt (2 * Real.pi * r))⁻¹ := by
    field_simp
  rw [hs]
  have hexp : Real.exp (-x ^ 2 / (2 * r)) ≤
      Real.exp (-(c - a) ^ 2 / (2 * (2 * r))) * Real.exp (2 - |N|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have e1 : -x ^ 2 / (2 * (r : ℝ)) = -(x ^ 2 / (4 * r)) - x ^ 2 / (4 * r) := by
      field_simp
      ring
    have e2 : -(c - a) ^ 2 / (2 * (2 * (r : ℝ))) = -((c - a) ^ 2 / (4 * r)) := by
      rw [show 2 * (2 * (r : ℝ)) = 4 * r by ring, neg_div]
    have h1 : (c - a) ^ 2 / (4 * r) ≤ x ^ 2 / (4 * r) :=
      div_le_div_of_nonneg_right hx1 (by positivity)
    have h3 : x ^ 2 / 4 ≤ x ^ 2 / (4 * r) :=
      div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) (by linarith)
    rw [e1, e2]
    linarith
  calc (Real.sqrt (2 * Real.pi * r))⁻¹ * Real.exp (-x ^ 2 / (2 * r))
      ≤ (Real.sqrt (2 * Real.pi * r))⁻¹ *
          (Real.exp (-(c - a) ^ 2 / (2 * (2 * r))) * Real.exp (2 - |N|)) :=
        mul_le_mul_of_nonneg_left hexp (inv_nonneg.2 hpos.le)
    _ = Real.sqrt 2 * ((Real.sqrt 2 * Real.sqrt (2 * Real.pi * r))⁻¹ *
          Real.exp (-(c - a) ^ 2 / (2 * (2 * r)))) * Real.exp (2 - |N|) := by
        rw [← hpre]
        ring

/-- The two Gaussian densities at the images `a - 2n`, `2n - a` of the centre. -/
theorem gaussianPDF_image_add_le {a c : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1)
    {r : ℝ≥0} (hr0 : r ≠ 0) (hr1 : r ≤ 1) (n : ℤ) :
    gaussianPDF (a - 2 * n) r c + gaussianPDF (2 * n - a) r c ≤
      2 * ENNReal.ofReal (Real.sqrt 2) * gaussianPDF a (2 * r) c *
        ENNReal.ofReal (Real.exp (2 - |(n : ℝ)|)) := by
  have hr0' : 0 < (r : ℝ) := by
    have := r.coe_nonneg
    exact lt_of_le_of_ne this (by exact_mod_cast (Ne.symm hr0))
  have hr1' : (r : ℝ) ≤ 1 := by exact_mod_cast hr1
  have hone : ∀ μ : ℝ, (c - a) ^ 2 ≤ (c - μ) ^ 2 → 4 * (|(n : ℝ)| - 2) ≤ (c - μ) ^ 2 →
      gaussianPDF μ r c ≤ ENNReal.ofReal (Real.sqrt 2) * gaussianPDF a (2 * r) c *
        ENNReal.ofReal (Real.exp (2 - |(n : ℝ)|)) := by
    intro μ h1 h2
    rw [gaussianPDF_def, gaussianPDF_def]
    simp only
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ← ENNReal.ofReal_mul (mul_nonneg (Real.sqrt_nonneg _) (gaussianPDFReal_nonneg _ _ _))]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := gaussianPDFReal_image_le (a := a) (c := c) (x := c - μ) (N := n) (r := r) hr0' hr1'
      h1 h2
    rw [gaussianPDFReal_def]
    exact h
  obtain ⟨t1, t2⟩ := sq_sub_le_sq_translate ha hc n
  obtain ⟨s1, s2⟩ := sq_sub_le_sq_reflect ha hc n
  calc gaussianPDF (a - 2 * n) r c + gaussianPDF (2 * n - a) r c
      ≤ ENNReal.ofReal (Real.sqrt 2) * gaussianPDF a (2 * r) c *
          ENNReal.ofReal (Real.exp (2 - |(n : ℝ)|)) +
        ENNReal.ofReal (Real.sqrt 2) * gaussianPDF a (2 * r) c *
          ENNReal.ofReal (Real.exp (2 - |(n : ℝ)|)) :=
        add_le_add (hone _ t1 t2) (hone _ s1 s2)
    _ = 2 * ENNReal.ofReal (Real.sqrt 2) * gaussianPDF a (2 * r) c *
          ENNReal.ofReal (Real.exp (2 - |(n : ℝ)|)) := by ring

/-! ### The folded Gaussian law in one dimension -/

/-- **A function of the triangle wave is dominated by its translates and reflections**:
`ψ(u(w)) ≤ ∑_n (ψ̃(w - 2n) + ψ̃(2n - w))` with `ψ̃ = 1_{[0,1]} ψ`. -/
theorem le_tsum_indicator_unitIntervalFold (ψ : ℝ → ℝ≥0∞) (w : ℝ) :
    ψ (unitIntervalFold w) ≤ ∑' n : ℤ, ((Icc (0 : ℝ) 1).indicator ψ (w - 2 * n) +
      (Icc (0 : ℝ) 1).indicator ψ (2 * n - w)) := by
  obtain ⟨σ, hσ, n, e⟩ := exists_unitIntervalFold_eq w
  have hmem := unitIntervalFold_mem_Icc w
  refine le_trans ?_ (ENNReal.le_tsum n)
  rcases hσ with rfl | rfl
  · have h : unitIntervalFold w = w - 2 * n := by rw [e, one_mul]
    rw [h] at hmem ⊢
    rw [Set.indicator_of_mem hmem]
    exact le_self_add
  · have h : unitIntervalFold w = 2 * n - w := by rw [e]; ring
    rw [h] at hmem ⊢
    rw [Set.indicator_of_mem hmem]
    exact le_add_self

theorem lintegral_gaussianReal_comp_sub {ψ : ℝ → ℝ≥0∞} (hψ : Measurable ψ) (μ y : ℝ) (v : ℝ≥0) :
    ∫⁻ w, ψ (w - y) ∂gaussianReal μ v = ∫⁻ c, ψ c ∂gaussianReal (μ - y) v := by
  rw [← gaussianReal_map_sub_const y, lintegral_map hψ (measurable_sub_const y)]

theorem lintegral_gaussianReal_comp_const_sub {ψ : ℝ → ℝ≥0∞} (hψ : Measurable ψ) (μ y : ℝ)
    (v : ℝ≥0) : ∫⁻ w, ψ (y - w) ∂gaussianReal μ v = ∫⁻ c, ψ c ∂gaussianReal (y - μ) v := by
  rw [← gaussianReal_map_const_sub y, lintegral_map hψ (measurable_const_sub y)]

theorem lintegral_gaussianReal_indicator_Icc {ψ : ℝ → ℝ≥0∞} (hψ : Measurable ψ) (μ : ℝ)
    {v : ℝ≥0} (hv : v ≠ 0) :
    ∫⁻ c, (Icc (0 : ℝ) 1).indicator ψ c ∂gaussianReal μ v =
      ∫⁻ c in Icc (0 : ℝ) 1, ψ c * gaussianPDF μ v c := by
  rw [gaussianReal_of_var_ne_zero μ hv, lintegral_withDensity_eq_lintegral_mul _
    (measurable_gaussianPDF μ v) (hψ.indicator measurableSet_Icc), ← lintegral_indicator measurableSet_Icc]
  refine lintegral_congr fun c => ?_
  by_cases hc : c ∈ Icc (0 : ℝ) 1
  · simp [Set.indicator_of_mem hc, mul_comm]
  · simp [Set.indicator_of_notMem hc]

/-- **The folded Gaussian law in one dimension**: for `a ∈ [0, 1]`, `0 < r ≤ 1` and measurable
`ψ ≥ 0`, `E[ψ(u(a + √r N))] ≤ 2 √2 S ∫_0^1 ψ(c) p_{2r}(a, c) dc`, with `p_{2r}` the Gaussian
density of variance `2r` and `S = foldLatticeSum`. -/
theorem lintegral_gaussianReal_unitIntervalFold_le {ψ : ℝ → ℝ≥0∞} (hψ : Measurable ψ) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) {r : ℝ≥0} (hr0 : r ≠ 0) (hr1 : r ≤ 1) :
    ∫⁻ w, ψ (unitIntervalFold w) ∂gaussianReal a r ≤
      2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum *
        ∫⁻ c in Icc (0 : ℝ) 1, ψ c * gaussianPDF a (2 * r) c := by
  have hψ'm : Measurable ((Icc (0 : ℝ) 1).indicator ψ) := hψ.indicator measurableSet_Icc
  have hpdf : ∀ (μ : ℝ) (v : ℝ≥0), Measurable (gaussianPDF μ v) := measurable_gaussianPDF
  calc ∫⁻ w, ψ (unitIntervalFold w) ∂gaussianReal a r
      ≤ ∫⁻ w, ∑' n : ℤ, ((Icc (0 : ℝ) 1).indicator ψ (w - 2 * n) +
          (Icc (0 : ℝ) 1).indicator ψ (2 * n - w)) ∂gaussianReal a r :=
        lintegral_mono fun w => le_tsum_indicator_unitIntervalFold ψ w
    _ = ∑' n : ℤ, ((∫⁻ w, (Icc (0 : ℝ) 1).indicator ψ (w - 2 * n) ∂gaussianReal a r) +
          ∫⁻ w, (Icc (0 : ℝ) 1).indicator ψ (2 * n - w) ∂gaussianReal a r) := by
        rw [lintegral_tsum fun n : ℤ => (show Measurable fun w =>
          (Icc (0 : ℝ) 1).indicator ψ (w - 2 * n) + (Icc (0 : ℝ) 1).indicator ψ (2 * n - w) from
          (hψ'm.comp (measurable_sub_const _)).add (hψ'm.comp (measurable_const_sub _))).aemeasurable]
        congr 1
        funext n
        exact lintegral_add_left (show Measurable fun w =>
          (Icc (0 : ℝ) 1).indicator ψ (w - 2 * n) from hψ'm.comp (measurable_sub_const _)) _
    _ = ∑' n : ℤ, ((∫⁻ c in Icc (0 : ℝ) 1, ψ c * gaussianPDF (a - 2 * n) r c) +
          ∫⁻ c in Icc (0 : ℝ) 1, ψ c * gaussianPDF (2 * n - a) r c) := by
        congr 1
        funext n
        rw [lintegral_gaussianReal_comp_sub hψ'm, lintegral_gaussianReal_comp_const_sub hψ'm,
          lintegral_gaussianReal_indicator_Icc hψ _ hr0,
          lintegral_gaussianReal_indicator_Icc hψ _ hr0]
    _ = ∫⁻ c in Icc (0 : ℝ) 1, ψ c * ∑' n : ℤ,
          (gaussianPDF (a - 2 * n) r c + gaussianPDF (2 * n - a) r c) := by
        have h : ∀ c, ψ c * ∑' n : ℤ,
            (gaussianPDF (a - 2 * n) r c + gaussianPDF (2 * n - a) r c) =
            ∑' n : ℤ, (ψ c * gaussianPDF (a - 2 * n) r c + ψ c * gaussianPDF (2 * n - a) r c) :=
          fun c => by
            rw [← ENNReal.tsum_mul_left]
            simp only [mul_add]
        simp_rw [h]
        rw [lintegral_tsum fun n : ℤ => (show Measurable fun c => ψ c * gaussianPDF (a - 2 * n) r c +
          ψ c * gaussianPDF (2 * n - a) r c from
          (hψ.mul (hpdf _ _)).add (hψ.mul (hpdf _ _))).aemeasurable]
        congr 1
        funext n
        rw [lintegral_add_left (show Measurable fun c => ψ c * gaussianPDF (a - 2 * n) r c from
          hψ.mul (hpdf _ _))]
    _ ≤ ∫⁻ c in Icc (0 : ℝ) 1, ψ c * (2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum *
          gaussianPDF a (2 * r) c) := by
        refine setLIntegral_mono' measurableSet_Icc fun c hc => mul_le_mul' le_rfl ?_
        calc ∑' n : ℤ, (gaussianPDF (a - 2 * n) r c + gaussianPDF (2 * n - a) r c)
            ≤ ∑' n : ℤ, 2 * ENNReal.ofReal (Real.sqrt 2) * gaussianPDF a (2 * r) c *
                ENNReal.ofReal (Real.exp (2 - |(n : ℝ)|)) :=
              ENNReal.tsum_le_tsum fun n => gaussianPDF_image_add_le ha hc hr0 hr1 n
          _ = 2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum * gaussianPDF a (2 * r) c := by
              rw [ENNReal.tsum_mul_left, foldLatticeSum]
              ring
    _ = 2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum *
          ∫⁻ c in Icc (0 : ℝ) 1, ψ c * gaussianPDF a (2 * r) c := by
        rw [← lintegral_const_mul _ (show Measurable fun c => ψ c * gaussianPDF a (2 * r) c from
          hψ.mul (hpdf _ _))]
        refine lintegral_congr fun c => ?_
        ring

/-! ### The folded Gaussian law in two dimensions -/

/-- A Lebesgue integral over the unit square as an iterated integral over `[0, 1]`. -/
theorem setLIntegral_closedSquare_zero_one_eq {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in closedSquare 0 1, f x =
      ∫⁻ x₁ in Icc (0 : ℝ) 1, ∫⁻ x₂ in Icc (0 : ℝ) 1, f ⟨x₁, x₂⟩ := by
  have hpre : Complex.measurableEquivRealProd ⁻¹' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) =
      closedSquare 0 1 := by
    ext z
    simp only [closedSquare, Complex.mem_reProdIm, Complex.measurableEquivRealProd, mem_preimage,
      mem_prod, Complex.zero_re, Complex.zero_im, zero_add]
    rfl
  have h1 := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding (fun p : ℝ × ℝ => f ⟨p.1, p.2⟩)
    (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  rw [hpre] at h1
  have hfm : Measurable fun p : ℝ × ℝ => f ⟨p.1, p.2⟩ := hf.comp measurable_complex_mk
  calc ∫⁻ x in closedSquare 0 1, f x
      = ∫⁻ p in Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, f ⟨p.1, p.2⟩ := h1
    _ = ∫⁻ x₁ in Icc (0 : ℝ) 1, ∫⁻ x₂ in Icc (0 : ℝ) 1, f ⟨x₁, x₂⟩ := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hfm.aemeasurable]

theorem squareFold_measurableEquivRealProd_symm (p : ℝ × ℝ) :
    squareFold 0 1 (Complex.measurableEquivRealProd.symm p) =
      ⟨unitIntervalFold p.1, unitIntervalFold p.2⟩ := by
  rw [squareFold_zero_one_apply]
  rfl

/-- **The folded Gaussian law in two dimensions**: for `y ∈ K₀`, `0 < r ≤ 1` and measurable
`Φ ≥ 0`, `E[Φ(fold(y + √r N))] ≤ (2 √2 S)² ∫_{K₀} Φ(c) p_{2r}(c - y) dc`, with `p_{2r}` the planar
Gaussian density of variance `2r`. -/
theorem lintegral_planarGaussian_squareFold_le {Φ : ℂ → ℝ≥0∞} (hΦ : Measurable Φ) {y : ℂ}
    (hy : y ∈ closedSquare 0 1) {r : ℝ≥0} (hr0 : r ≠ 0) (hr1 : r ≤ 1) :
    ∫⁻ w, Φ (squareFold 0 1 w) ∂planarGaussian y r ≤
      (2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum) ^ 2 *
        ∫⁻ c in closedSquare 0 1, Φ c *
          ENNReal.ofReal ((2 * Real.pi * (2 * r))⁻¹ * Real.exp (-‖c - y‖ ^ 2 / (2 * (2 * r)))) := by
  have hy' : y.re ∈ Icc (0 : ℝ) 1 ∧ y.im ∈ Icc (0 : ℝ) 1 := by
    simpa [closedSquare, Complex.mem_reProdIm] using hy
  have he := Complex.measurableEquivRealProd.symm.measurable
  have hu := continuous_unitIntervalFold.measurable
  have hpdf : ∀ (μ : ℝ) (v : ℝ≥0), Measurable (gaussianPDF μ v) := measurable_gaussianPDF
  have hF : Measurable fun p : ℝ × ℝ => Φ ⟨unitIntervalFold p.1, unitIntervalFold p.2⟩ :=
    hΦ.comp (measurable_complex_mk_comp (hu.comp measurable_fst) (hu.comp measurable_snd))
  have hGm : Measurable fun t : ℝ =>
      ∫⁻ c₂ in Icc (0 : ℝ) 1, Φ ⟨t, c₂⟩ * gaussianPDF y.im (2 * r) c₂ := by
    have : Measurable fun p : ℝ × ℝ => Φ ⟨p.1, p.2⟩ * gaussianPDF y.im (2 * r) p.2 :=
      (hΦ.comp measurable_complex_mk).mul ((hpdf _ _).comp measurable_snd)
    exact this.lintegral_prod_right'
  have hr0' : 0 < (r : ℝ) := by
    have := r.coe_nonneg
    exact lt_of_le_of_ne this (by exact_mod_cast (Ne.symm hr0))
  have hX : ∫⁻ c₁ in Icc (0 : ℝ) 1, (∫⁻ c₂ in Icc (0 : ℝ) 1,
        Φ ⟨c₁, c₂⟩ * gaussianPDF y.im (2 * r) c₂) * gaussianPDF y.re (2 * r) c₁ =
      ∫⁻ c in closedSquare 0 1, Φ c *
        ENNReal.ofReal ((2 * Real.pi * (2 * r))⁻¹ * Real.exp (-‖c - y‖ ^ 2 / (2 * (2 * r)))) := by
    have hmK : Measurable fun c : ℂ => Φ c * ENNReal.ofReal ((2 * Real.pi * (2 * r))⁻¹ *
        Real.exp (-‖c - y‖ ^ 2 / (2 * (2 * r)))) := by fun_prop
    rw [setLIntegral_closedSquare_zero_one_eq hmK]
    refine setLIntegral_congr_fun measurableSet_Icc fun c₁ _ => ?_
    rw [← lintegral_mul_const _ (show Measurable fun c₂ => Φ ⟨c₁, c₂⟩ *
      gaussianPDF y.im (2 * r) c₂ from (hΦ.comp (measurable_complex_mk_left c₁)).mul (hpdf _ _))]
    refine setLIntegral_congr_fun measurableSet_Icc fun c₂ _ => ?_
    rw [mul_assoc]
    congr 1
    rw [gaussianPDF_def, gaussianPDF_def]
    beta_reduce
    rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
    congr 1
    simp only [gaussianPDFReal_def, NNReal.coe_mul, NNReal.coe_ofNat]
    set v : ℝ := 2 * Real.pi * (2 * r) with hv
    have hv0 : 0 < v := by positivity
    have hn : ‖(⟨c₁, c₂⟩ : ℂ) - y‖ ^ 2 = (c₁ - y.re) ^ 2 + (c₂ - y.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im]
      ring
    rw [hn]
    have hsq : (Real.sqrt v)⁻¹ * (Real.sqrt v)⁻¹ = v⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hv0.le]
    calc (Real.sqrt v)⁻¹ * Real.exp (-(c₂ - y.im) ^ 2 / (2 * (2 * r))) *
          ((Real.sqrt v)⁻¹ * Real.exp (-(c₁ - y.re) ^ 2 / (2 * (2 * r))))
        = ((Real.sqrt v)⁻¹ * (Real.sqrt v)⁻¹) * (Real.exp (-(c₂ - y.im) ^ 2 / (2 * (2 * r))) *
            Real.exp (-(c₁ - y.re) ^ 2 / (2 * (2 * r)))) := by ring
      _ = v⁻¹ * Real.exp (-((c₁ - y.re) ^ 2 + (c₂ - y.im) ^ 2) / (2 * (2 * r))) := by
        rw [hsq, ← Real.exp_add]
        congr 2
        ring
  calc ∫⁻ w, Φ (squareFold 0 1 w) ∂planarGaussian y r
      = ∫⁻ p, Φ ⟨unitIntervalFold p.1, unitIntervalFold p.2⟩
          ∂((gaussianReal y.re r).prod (gaussianReal y.im r)) := by
        rw [planarGaussian, lintegral_map (show Measurable fun w => Φ (squareFold 0 1 w) from
          hΦ.comp (continuous_squareFold 0 1).measurable) he]
        exact lintegral_congr fun p => by rw [squareFold_measurableEquivRealProd_symm p]
    _ = ∫⁻ w₁, ∫⁻ w₂, Φ ⟨unitIntervalFold w₁, unitIntervalFold w₂⟩ ∂gaussianReal y.im r
          ∂gaussianReal y.re r := lintegral_prod _ hF.aemeasurable
    _ ≤ ∫⁻ w₁, 2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum *
          (∫⁻ c₂ in Icc (0 : ℝ) 1, Φ ⟨unitIntervalFold w₁, c₂⟩ * gaussianPDF y.im (2 * r) c₂)
          ∂gaussianReal y.re r :=
        lintegral_mono fun w₁ => lintegral_gaussianReal_unitIntervalFold_le
          (ψ := fun t => Φ ⟨unitIntervalFold w₁, t⟩)
          (hΦ.comp (measurable_complex_mk_left _)) hy'.2 hr0 hr1
    _ = 2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum *
          ∫⁻ w₁, (∫⁻ c₂ in Icc (0 : ℝ) 1, Φ ⟨unitIntervalFold w₁, c₂⟩ *
            gaussianPDF y.im (2 * r) c₂) ∂gaussianReal y.re r :=
        lintegral_const_mul _ (show Measurable fun w₁ => ∫⁻ c₂ in Icc (0 : ℝ) 1,
          Φ ⟨unitIntervalFold w₁, c₂⟩ * gaussianPDF y.im (2 * r) c₂ from hGm.comp hu)
    _ ≤ 2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum *
          (2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum *
            ∫⁻ c₁ in Icc (0 : ℝ) 1, (∫⁻ c₂ in Icc (0 : ℝ) 1,
              Φ ⟨c₁, c₂⟩ * gaussianPDF y.im (2 * r) c₂) * gaussianPDF y.re (2 * r) c₁) :=
        mul_le_mul' le_rfl (lintegral_gaussianReal_unitIntervalFold_le
          (ψ := fun t => ∫⁻ c₂ in Icc (0 : ℝ) 1, Φ ⟨t, c₂⟩ * gaussianPDF y.im (2 * r) c₂)
          hGm hy'.1 hr0 hr1)
    _ = _ := by
        rw [hX]
        ring

/-! ### The Green potential bound -/

/-- **Expected occupation integrals of reflected Brownian motion in the unit square**: if the
measure `ν = g dx` on `K₀` has mass at most `m` and closed-ball bounds `ν(B̄(z, ρ)) ≤ A ρ^β`, then
for `0 < θ ≤ 1` with `2θ < β` and every start `y ∈ K₀`,
`E_y ∫_{(0,1]} g(b_s) ds ≤ (2 √2 S)² (2π)⁻¹ 2^θ θ⁻¹ (m + A 2θ / (β - 2θ))`. -/
theorem lintegral_windowOccupation_reflected_le {g : ℂ → ℝ≥0∞} (hg : Measurable g)
    {θ m A β : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθβ : 2 * θ < β) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hmass : ((volume.restrict (closedSquare 0 1)).withDensity g) univ ≤ ENNReal.ofReal m)
    (hball : ∀ z : ℂ, ∀ ρ : ℝ, 0 < ρ →
      ((volume.restrict (closedSquare 0 1)).withDensity g) (closedBall z ρ) ≤
        ENNReal.ofReal (A * ρ ^ β))
    {y : ℂ} (hy : y ∈ closedSquare 0 1) :
    ∫⁻ b, windowOccupation g b ∂(reflectedPlanarBrownianMotion 0 1 y) ≤
      (2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum) ^ 2 *
        ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * (1 / θ)) *
          ENNReal.ofReal (m + A * (2 * θ / (β - 2 * θ))) := by
  set K := (2 * ENNReal.ofReal (Real.sqrt 2) * foldLatticeSum) ^ 2 with hK
  set ν := (volume.restrict (closedSquare 0 1)).withDensity g with hν
  set R := ∫⁻ c in closedSquare 0 1, g c * ENNReal.ofReal ‖c - y‖ ^ (-(2 * θ)) with hR
  have hgfold : Measurable fun w => g (squareFold 0 1 w) :=
    hg.comp (continuous_squareFold 0 1).measurable
  -- the time-`s` bound
  have hpt : ∀ s ∈ Ioc (0 : ℝ) 1, ∫⁻ b, g (b s.toNNReal) ∂(reflectedPlanarBrownianMotion 0 1 y) ≤
      K * ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * s ^ (θ - 1)) * R := by
    intro s hs
    have hs0 : s.toNNReal ≠ 0 := (Real.toNNReal_pos.mpr hs.1).ne'
    have hs1 : s.toNNReal ≤ 1 := by
      rw [Real.toNNReal_le_one]
      exact hs.2
    have hcoe : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs.1.le
    rw [lintegral_reflected_eval_eq _ hg y]
    refine (lintegral_planarGaussian_squareFold_le hg hy hs0 hs1).trans ?_
    rw [hR, mul_assoc K, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine mul_le_mul' le_rfl (lintegral_mono fun c => ?_)
    refine (mul_le_mul' le_rfl ?_).trans (mul_left_comm _ _ _).le
    rw [hcoe]
    have h2s : 0 < 2 * s := by linarith [hs.1]
    refine (ofReal_heatDensity_le hθ0 hθ1 h2s (c - y)).trans (mul_le_mul' ?_ le_rfl)
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Real.rpow_le_rpow_of_nonpos hs.1 (by linarith [hs.1]) (by linarith)
  -- the time integral
  have hev := measurable_eval_toNNReal_uncurry hg
  have htime : ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * s ^ (θ - 1)) =
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * (1 / θ)) := by
    have hint : IntervalIntegrable (fun s : ℝ => (2 * Real.pi)⁻¹ * 2 ^ θ * s ^ (θ - 1))
        volume 0 1 :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hint)
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs => by
        have := hs.1
        positivity)), ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by linarith : (-1 : ℝ) < θ - 1))]
    congr 1
    rw [show θ - 1 + 1 = θ by ring, Real.zero_rpow hθ0.ne', sub_zero, Real.one_rpow]
  -- the Riesz potential
  have hRle : R ≤ ENNReal.ofReal (m + A * (2 * θ / (β - 2 * θ))) := by
    have hν0 : ν {y} = 0 := by
      rw [hν, withDensity_apply _ (measurableSet_singleton y)]
      refine setLIntegral_measure_zero _ _ ?_
      rw [Measure.restrict_apply (measurableSet_singleton y)]
      exact measure_mono_null inter_subset_left (measure_singleton y)
    have hae : ∀ᵐ c ∂ν, c ≠ y := by
      rw [ae_iff]
      have hset : {a : ℂ | ¬a ≠ y} = {y} := by
        ext a
        simp
      rw [hset]
      exact hν0
    have hmeas : Measurable fun c : ℂ => ENNReal.ofReal ‖c - y‖ ^ (-(2 * θ)) := by fun_prop
    calc R = ∫⁻ c, ENNReal.ofReal ‖c - y‖ ^ (-(2 * θ)) ∂ν := by
          rw [hR, hν, lintegral_withDensity_eq_lintegral_mul _ hg hmeas]
          rfl
      _ = ∫⁻ c, ENNReal.ofReal (‖y - c‖ ^ (-(2 * θ))) ∂ν := by
          refine lintegral_congr_ae (hae.mono fun c hc => ?_)
          have hpos : 0 < ‖c - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hc)
          show ENNReal.ofReal ‖c - y‖ ^ (-(2 * θ)) = ENNReal.ofReal (‖y - c‖ ^ (-(2 * θ)))
          rw [ENNReal.ofReal_rpow_of_pos hpos, norm_sub_rev]
      _ ≤ ENNReal.ofReal (m + A * (2 * θ / (β - 2 * θ))) :=
          lintegral_norm_sub_rpow_neg_le (by linarith) hθβ hm hA hmass (hball y)
  calc ∫⁻ b, windowOccupation g b ∂(reflectedPlanarBrownianMotion 0 1 y)
      = ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ b, g (b s.toNNReal) ∂(reflectedPlanarBrownianMotion 0 1 y) :=
        lintegral_windowOccupation_eq hg _
    _ ≤ ∫⁻ s in Ioc (0 : ℝ) 1, K * ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * s ^ (θ - 1)) * R :=
        setLIntegral_mono' measurableSet_Ioc hpt
    _ = K * (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * s ^ (θ - 1))) * R := by
        have hmeas : Measurable fun s : ℝ =>
            ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * s ^ (θ - 1)) := by fun_prop
        rw [lintegral_mul_const _ (show Measurable fun s : ℝ =>
          K * ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * s ^ (θ - 1)) from hmeas.const_mul K),
          lintegral_const_mul _ hmeas]
    _ ≤ K * ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * (1 / θ)) *
          ENNReal.ofReal (m + A * (2 * θ / (β - 2 * θ))) := by
        rw [htime]
        exact mul_le_mul' le_rfl hRle

end HarmonicBalls
