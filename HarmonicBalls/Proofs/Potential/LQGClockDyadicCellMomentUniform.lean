import LatticeProb.Analysis.MonotoneGridApprox
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! # Uniform limits of monotone random functions from dyadic cell moments

Let `X n ω` be random functions that are nondecreasing on `[0, 1]`. Suppose that almost surely
their values at every dyadic point `j / 2 ^ m` converge as `n → ∞`, and that for some `p > 0`
and `a > 1` the `p`-th moments of the dyadic cell increments satisfy
`E[(X n ((j + 1) / 2 ^ m) - X n (j / 2 ^ m)) ^ p] ≤ C (2 ^ -m) ^ a` uniformly in `n`, `m` and
`j < 2 ^ m`, for all large `n`. Then almost surely `X n ω` converges uniformly on `[0, 1]`.

The proof sums the `p`-th powers of the `2 ^ m` cell increments of one level, passes to the
limit in `n` by Fatou's lemma, and sums the resulting geometric bound over the levels. The sum
over levels is almost surely finite, so the largest cell increment of the limit at level `m`
tends to zero. The grid inequality for monotone functions then gives the uniform Cauchy
property.

## Main results

* `ae_tendstoUniformlyOn_of_dyadic_cell_moment`: almost sure uniform convergence on `[0, 1]`.
* `ae_exists_continuousOn_monotoneOn_limit_of_dyadic_cell_moment`: the uniform limit is
  continuous and nondecreasing on `[0, 1]` when the approximants are continuous there.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

private theorem two_pow_mul_inv_two_pow_rpow (a : ℝ) (m : ℕ) :
    (2 : ℝ) ^ m * ((2 : ℝ) ^ m)⁻¹ ^ a = (2 * (2 : ℝ)⁻¹ ^ a) ^ m := by
  rw [← inv_pow, ← Real.rpow_natCast ((2 : ℝ)⁻¹) m,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2⁻¹), mul_comm (m : ℝ) a,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2⁻¹), Real.rpow_natCast, ← mul_pow]

/-- Nondecreasing random functions on `[0, 1]` whose values at the dyadic points converge
almost surely, and whose dyadic cell increments eventually have `p`-th moments bounded by
`C h ^ a` for cells of length `h = 2 ^ -m` with `a > 1`, converge uniformly on `[0, 1]` almost
surely. -/
theorem ae_tendstoUniformlyOn_of_dyadic_cell_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (X : ℕ → Ω → ℝ → ℝ)
    (hmono : ∀ᵐ ω ∂μ, ∀ n, MonotoneOn (X n ω) (Icc 0 1))
    (hmeas : ∀ n (t : ℝ), Measurable fun ω => X n ω t)
    (hconv : ∀ᵐ ω ∂μ, ∀ m j : ℕ, j ≤ 2 ^ m →
      ∃ L : ℝ, Tendsto (fun n => X n ω (j / 2 ^ m)) atTop (𝓝 L))
    {p a C : ℝ} (hp : 0 < p) (ha : 1 < a)
    (hmom : ∀ᶠ n in atTop, ∀ m j : ℕ, j < 2 ^ m →
      ∫⁻ ω, ENNReal.ofReal (X n ω ((j + 1) / 2 ^ m) - X n ω (j / 2 ^ m)) ^ p ∂μ ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ m)⁻¹ ^ a)) :
    ∀ᵐ ω ∂μ, ∃ F : ℝ → ℝ, TendstoUniformlyOn (fun n => X n ω) F atTop (Icc 0 1) := by
  set C' : ℝ := max C 0
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set r : ℝ := 2 * (2 : ℝ)⁻¹ ^ a with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    have h := Real.rpow_lt_rpow_of_exponent_gt (by norm_num : (0 : ℝ) < 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1) ha
    rw [Real.rpow_one] at h
    rw [hr]
    linarith
  let I : ℕ → ℕ → ℕ → Ω → ℝ := fun n m j ω =>
    X n ω ((j + 1) / 2 ^ m) - X n ω (j / 2 ^ m)
  let S : ℕ → ℕ → Ω → ℝ≥0∞ := fun n m ω =>
    ∑ j ∈ Finset.range (2 ^ m), ENNReal.ofReal (I n m j ω) ^ p
  let G : ℕ → Ω → ℝ≥0∞ := fun m ω => liminf (fun n => S n m ω) atTop
  have hIm (n m j : ℕ) : Measurable fun ω => ENNReal.ofReal (I n m j ω) ^ p :=
    (ENNReal.measurable_ofReal.comp ((hmeas n (((j : ℝ) + 1) / 2 ^ m)).sub
      (hmeas n ((j : ℝ) / 2 ^ m)))).pow_const p
  have hSm (n m : ℕ) : Measurable (S n m) :=
    Finset.measurable_sum _ fun j _ => hIm n m j
  have hGm (m : ℕ) : Measurable (G m) := Measurable.liminf fun n => hSm n m
  have hS (m : ℕ) : ∀ᶠ n in atTop, ∫⁻ ω, S n m ω ∂μ ≤ ENNReal.ofReal (C' * r ^ m) := by
    filter_upwards [hmom] with n hn
    calc ∫⁻ ω, S n m ω ∂μ
        = ∑ j ∈ Finset.range (2 ^ m), ∫⁻ ω, ENNReal.ofReal (I n m j ω) ^ p ∂μ :=
          lintegral_finsetSum _ fun j _ => hIm n m j
      _ ≤ ∑ _j ∈ Finset.range (2 ^ m), ENNReal.ofReal (C' * ((2 : ℝ) ^ m)⁻¹ ^ a) := by
          refine Finset.sum_le_sum fun j hj => (hn m j (Finset.mem_range.mp hj)).trans ?_
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      _ = ENNReal.ofReal (C' * r ^ m) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1
          rw [hr, ← two_pow_mul_inv_two_pow_rpow a m]
          push_cast
          ring
  have hG (m : ℕ) : ∫⁻ ω, G m ω ∂μ ≤ ENNReal.ofReal (C' * r ^ m) := by
    calc ∫⁻ ω, G m ω ∂μ ≤ liminf (fun n => ∫⁻ ω, S n m ω ∂μ) atTop :=
          lintegral_liminf_le' fun n => (hSm n m).aemeasurable
      _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal (C' * r ^ m)) atTop :=
          liminf_le_liminf (hS m)
      _ = ENNReal.ofReal (C' * r ^ m) := liminf_const _
  have hsum : ∫⁻ ω, ∑' m, G m ω ∂μ ≠ ∞ := by
    rw [lintegral_tsum fun m => (hGm m).aemeasurable]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hG)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg hC'0 (pow_nonneg hr0 m))
      ((summable_geometric_of_lt_one hr0 hr1).mul_left C')]
    exact ENNReal.ofReal_ne_top
  have hfin : ∀ᵐ ω ∂μ, ∑' m, G m ω ≠ ∞ := by
    filter_upwards [ae_lt_top' (AEMeasurable.tsum fun m => (hGm m).aemeasurable) hsum]
      with ω hω
    exact hω.ne
  filter_upwards [hmono, hconv, hfin] with ω hωm hω hωG
  let L : ℕ → ℕ → ℝ := fun m j => limUnder atTop (fun n => X n ω (j / 2 ^ m))
  have hL (m j : ℕ) (hj : j ≤ 2 ^ m) :
      Tendsto (fun n => X n ω (j / 2 ^ m)) atTop (𝓝 (L m j)) :=
    tendsto_nhds_limUnder (hω m j hj)
  have hGt : Tendsto (fun m => G m ω) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hωG
  have hcauchy : UniformCauchySeqOn (fun n => X n ω) atTop (Icc 0 1) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    set e : ℝ := ε / 6 with he_def
    have he : 0 < e := by positivity
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal e ^ p :=
      ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr he) ENNReal.ofReal_ne_top
    obtain ⟨m, hm⟩ := (hGt.eventually (gt_mem_nhds hpos)).exists
    have hcell (j : ℕ) (hj : j < 2 ^ m) : L m (j + 1) - L m j < e := by
      have h1 : Tendsto (fun n => I n m j ω) atTop (𝓝 (L m (j + 1) - L m j)) := by
        have h := (hL m (j + 1) (Nat.succ_le_of_lt hj)).sub (hL m j hj.le)
        simpa only [I, Nat.cast_add, Nat.cast_one] using h
      have h2 : Tendsto (fun n => ENNReal.ofReal (I n m j ω) ^ p) atTop
          (𝓝 (ENNReal.ofReal (L m (j + 1) - L m j) ^ p)) :=
        (ENNReal.continuous_rpow_const.tendsto _).comp (ENNReal.tendsto_ofReal h1)
      have h3 : ENNReal.ofReal (L m (j + 1) - L m j) ^ p ≤ G m ω := by
        rw [← h2.liminf_eq]
        refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
        exact Finset.single_le_sum (f := fun i => ENNReal.ofReal (I n m i ω) ^ p)
          (fun _ _ => zero_le) (Finset.mem_range.mpr hj)
      exact (ENNReal.ofReal_lt_ofReal_iff he).mp
        ((ENNReal.rpow_lt_rpow_iff hp).mp (h3.trans_lt hm))
    have hev : ∀ᶠ n in atTop, ∀ j ∈ Finset.range (2 ^ m + 1),
        |X n ω (j / 2 ^ m) - L m j| < e := by
      rw [eventually_all_finset]
      intro j hj
      have hj' : j ≤ 2 ^ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      exact (Metric.tendsto_nhds.mp (hL m j hj') e he).mono fun n hn => by
        rwa [Real.dist_eq] at hn
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    have hm0 : 0 < 2 ^ m := pow_pos (by norm_num) m
    have hcast (j : ℕ) : (j : ℝ) * 1 / ((2 ^ m : ℕ) : ℝ) = j / 2 ^ m := by
      rw [Nat.cast_pow, Nat.cast_ofNat, mul_one]
    have hcast' (j : ℕ) : ((j : ℝ) + 1) * 1 / ((2 ^ m : ℕ) : ℝ) = (j + 1) / 2 ^ m := by
      rw [Nat.cast_pow, Nat.cast_ofNat, mul_one]
    refine ⟨N, fun n hn k hk x hx => ?_⟩
    have hgrid : ∀ j : ℕ, j ≤ 2 ^ m →
        |X n ω (j * 1 / ((2 ^ m : ℕ) : ℝ)) - X k ω (j * 1 / ((2 ^ m : ℕ) : ℝ))| ≤ 2 * e := by
      intro j hj
      rw [hcast j]
      have h1 := hN n hn j (Finset.mem_range.mpr (by omega))
      have h2 := hN k hk j (Finset.mem_range.mpr (by omega))
      rw [abs_lt] at h1 h2
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hosc : ∀ j : ℕ, j < 2 ^ m →
        X k ω ((j + 1) * 1 / ((2 ^ m : ℕ) : ℝ)) - X k ω (j * 1 / ((2 ^ m : ℕ) : ℝ)) ≤
          3 * e := by
      intro j hj
      rw [hcast' j, hcast j]
      have h1 := hN k hk (j + 1) (Finset.mem_range.mpr (by omega))
      have h2 := hN k hk j (Finset.mem_range.mpr (by omega))
      have h3 := hcell j hj
      push_cast at h1
      rw [abs_lt] at h1 h2
      linarith [h1.1, h1.2, h2.1, h2.2]
    have key := LatticeProb.abs_sub_le_of_grid hm0 zero_le_one (hωm n) (hωm k)
      hgrid hosc x hx
    show dist (X n ω x) (X k ω x) < ε
    rw [Real.dist_eq]
    linarith [he_def]
  exact ⟨fun x => limUnder atTop (fun n => X n ω x),
    hcauchy.tendstoUniformlyOn_of_tendsto fun x hx => (hcauchy.cauchySeq hx).tendsto_limUnder⟩

/-- Under the hypotheses of `ae_tendstoUniformlyOn_of_dyadic_cell_moment`, if the
approximants are continuous on `[0, 1]`, then almost surely they converge uniformly on
`[0, 1]` to a function that is continuous and nondecreasing there. -/
theorem ae_exists_continuousOn_monotoneOn_limit_of_dyadic_cell_moment {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} (X : ℕ → Ω → ℝ → ℝ)
    (hmono : ∀ᵐ ω ∂μ, ∀ n, MonotoneOn (X n ω) (Icc 0 1))
    (hcont : ∀ᵐ ω ∂μ, ∀ n, ContinuousOn (X n ω) (Icc 0 1))
    (hmeas : ∀ n (t : ℝ), Measurable fun ω => X n ω t)
    (hconv : ∀ᵐ ω ∂μ, ∀ m j : ℕ, j ≤ 2 ^ m →
      ∃ L : ℝ, Tendsto (fun n => X n ω (j / 2 ^ m)) atTop (𝓝 L))
    {p a C : ℝ} (hp : 0 < p) (ha : 1 < a)
    (hmom : ∀ᶠ n in atTop, ∀ m j : ℕ, j < 2 ^ m →
      ∫⁻ ω, ENNReal.ofReal (X n ω ((j + 1) / 2 ^ m) - X n ω (j / 2 ^ m)) ^ p ∂μ ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ m)⁻¹ ^ a)) :
    ∀ᵐ ω ∂μ, ∃ F : ℝ → ℝ, ContinuousOn F (Icc 0 1) ∧ MonotoneOn F (Icc 0 1) ∧
      TendstoUniformlyOn (fun n => X n ω) F atTop (Icc 0 1) := by
  filter_upwards [ae_tendstoUniformlyOn_of_dyadic_cell_moment X hmono hmeas hconv hp ha hmom,
    hmono, hcont] with ω ⟨F, hF⟩ hωm hωc
  refine ⟨F, hF.continuousOn (Frequently.of_forall hωc), ?_, hF⟩
  intro x hx y hy hxy
  exact le_of_tendsto_of_tendsto' (hF.tendsto_at hx) (hF.tendsto_at hy)
    fun n => hωm n hx hy hxy

end HarmonicBalls
