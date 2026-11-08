import HarmonicBalls.Defs.GFF
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Mean-zero test functions away from the origin

This file records the deterministic approximation needed for the dilation argument.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ContDiff Topology MeasureTheory

namespace HarmonicBalls

/-- The desired common deterministic approximation, with convergence for every
whole-plane GFF and every probability space. -/
def ZeroIntegralAwayOriginApproximation (φ : ℂ → ℝ) : Prop :=
  ∃ ψ : ℕ → ℂ → ℝ,
    (∀ n, IsTestFunction univ (ψ n)) ∧
    (∀ n, (∫ z, ψ n z) = 0) ∧
    (∀ n, (0 : ℂ) ∉ tsupport (ψ n)) ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc →
      Tendsto (fun n => ∫ sample, (hC sample (ψ n) - hC sample φ) ^ 2 ∂P)
        atTop (𝓝 0)

/-- A fixed smooth probability density supported away from zero. -/
theorem exists_testFunction_integral_one_away_origin :
    ∃ η : ℂ → ℝ, IsTestFunction univ η ∧ (∫ z, η z) = 1 ∧
      (0 : ℂ) ∉ tsupport η := by
  let b : ContDiffBump (2 : ℂ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨b.normed volume, ⟨b.contDiff_normed, b.hasCompactSupport_normed, subset_univ _⟩,
    b.integral_normed, ?_⟩
  rw [b.tsupport_normed_eq]
  simp [b, Metric.mem_closedBall, Complex.dist_eq]

/-- Cutting out the origin and subtracting the mass against an integral-one
test produces another mean-zero test supported away from the origin. -/
theorem cutout_corrected_test {φ η : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hη : IsTestFunction univ η)
    (hηone : (∫ z, η z) = 1) (hηzero : (0 : ℂ) ∉ tsupport η)
    (b : ContDiffBump (0 : ℂ)) :
    let cut : ℂ → ℝ := fun z => φ z * (1 - b z)
    let corrected : ℂ → ℝ := fun z => cut z - (∫ w, cut w) * η z
    IsTestFunction univ corrected ∧ (∫ z, corrected z) = 0 ∧
      (0 : ℂ) ∉ tsupport corrected ∧
      tsupport corrected ⊆ tsupport φ ∪ tsupport η := by
  dsimp only
  let cut : ℂ → ℝ := fun z => φ z * (1 - b z)
  have hcut_smooth : ContDiff ℝ ∞ cut := hφ.1.mul (contDiff_const.sub b.contDiff)
  have hcut_compact : HasCompactSupport cut := hφ.2.1.mul_right
  have hcut_int : Integrable cut := hcut_smooth.continuous.integrable_of_hasCompactSupport hcut_compact
  have hη_int : Integrable η := hη.1.continuous.integrable_of_hasCompactSupport hη.2.1
  have hcut_zero : (0 : ℂ) ∉ tsupport cut := by
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [b.eventuallyEq_one] with z hz
    simp [cut, hz]
  refine ⟨⟨hcut_smooth.sub (contDiff_const.mul hη.1),
    hcut_compact.sub hη.2.1.mul_left, subset_univ _⟩, ?_, ?_, ?_⟩
  · change (∫ z, cut z - (∫ w, cut w) * η z) = 0
    rw [integral_sub hcut_int (hη_int.const_mul _), integral_const_mul, hηone, mul_one, sub_self]
  · change (0 : ℂ) ∉ tsupport (fun z => cut z - (∫ w, cut w) * η z)
    intro hz
    rcases tsupport_sub _ _ hz with hz | hz
    · exact hcut_zero hz
    · exact hηzero (tsupport_mul_subset_right hz)
  · change tsupport (fun z => cut z - (∫ w, cut w) * η z) ⊆ _
    exact (tsupport_sub _ _).trans (union_subset_union
      tsupport_mul_subset_left tsupport_mul_subset_right)

/-- The mass removed by shrinking smooth cutoffs tends to zero. -/
theorem tendsto_integral_mul_shrinking_bump {φ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (b : ℕ → ContDiffBump (0 : ℂ))
    (hb : Tendsto (fun n => (b n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, φ z * b n z) atTop (𝓝 0) := by
  have hφint : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have ht := tendsto_integral_of_dominated_convergence
    (F := fun n z => φ z * b n z) (f := fun _ => (0 : ℝ)) (fun z => ‖φ z‖)
    (fun n => (hφ.1.continuous.mul (b n).continuous).aestronglyMeasurable)
    hφint.norm
    (fun n => Filter.Eventually.of_forall fun z => by
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (b n).nonneg]
      exact mul_le_of_le_one_right (abs_nonneg _) (b n).le_one)
    (by
      filter_upwards [Measure.ae_ne volume (0 : ℂ)] with z hz
      have hd : 0 < dist z 0 := dist_pos.mpr hz
      have he := hb.eventually (Iio_mem_nhds hd)
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with n hn
      simp [(b n).zero_of_le_dist (le_of_lt hn)])
  simpa using ht

/-- A sequence of smooth cutoffs shrinking to the origin. -/
def originShrinkingBump (n : ℕ) : ContDiffBump (0 : ℂ) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply div_lt_div_of_pos_right _ (by positivity)
    norm_num

/-- The outer radii of the standard cutoffs vanish. -/
theorem tendsto_originShrinkingBump_rOut :
    Tendsto (fun n => (originShrinkingBump n).rOut) atTop (𝓝 0) := by
  simpa [originShrinkingBump, div_eq_mul_inv] using
    (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) :
      Tendsto (fun n : ℕ => (2 : ℝ) * (1 / ((n : ℝ) + 1))) atTop (𝓝 (2 * 0)))

/-- The restoring coefficient for a mean-zero test tends to zero. -/
theorem tendsto_integral_cutout {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ)
    (hφzero : (∫ z, φ z) = 0) (b : ℕ → ContDiffBump (0 : ℂ))
    (hb : Tendsto (fun n => (b n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, φ z * (1 - b n z)) atTop (𝓝 0) := by
  have hi : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have hsub (n : ℕ) : (∫ z, φ z * (1 - b n z)) = -(∫ z, φ z * b n z) := by
    have heq : (fun z => φ z * (1 - b n z)) = fun z => φ z - φ z * b n z := by
      funext z
      ring
    have hmul : Integrable (fun z => φ z * b n z) :=
      (hφ.1.continuous.mul (b n).continuous).integrable_of_hasCompactSupport hφ.2.1.mul_right
    rw [heq, integral_sub hi hmul, hφzero, zero_sub]
  simp_rw [hsub]
  simpa using (tendsto_integral_mul_shrinking_bump hφ b hb).neg

/-- Mean-zero tests have a common-compactly-supported approximation away
from zero which converges pointwise away from zero. -/
theorem exists_zeroIntegral_awayOrigin_pointwise {φ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hφzero : (∫ z, φ z) = 0) :
    ∃ ψ : ℕ → ℂ → ℝ, ∃ K : Set ℂ, IsCompact K ∧
      (∀ n, IsTestFunction univ (ψ n)) ∧
      (∀ n, (∫ z, ψ n z) = 0) ∧
      (∀ n, (0 : ℂ) ∉ tsupport (ψ n)) ∧
      (∀ n, tsupport (ψ n) ⊆ K) ∧
      ∀ z ≠ 0, Tendsto (fun n => ψ n z) atTop (𝓝 (φ z)) := by
  obtain ⟨η, hη, hηone, hηzero⟩ := exists_testFunction_integral_one_away_origin
  let b := originShrinkingBump
  let cut : ℕ → ℂ → ℝ := fun n z => φ z * (1 - b n z)
  let ψ : ℕ → ℂ → ℝ := fun n z => cut n z - (∫ w, cut n w) * η z
  have htests := fun n => cutout_corrected_test hφ hη hηone hηzero (b n)
  refine ⟨ψ, tsupport φ ∪ tsupport η, hφ.2.1.union hη.2.1,
    fun n => (htests n).1, fun n => (htests n).2.1,
    fun n => (htests n).2.2.1, fun n => (htests n).2.2.2, ?_⟩
  intro z hz
  have hmass : Tendsto (fun n => ∫ w, cut n w) atTop (𝓝 0) :=
    tendsto_integral_cutout hφ hφzero b tendsto_originShrinkingBump_rOut
  have hd : 0 < dist z 0 := dist_pos.mpr hz
  have he := tendsto_originShrinkingBump_rOut.eventually (Iio_mem_nhds hd)
  have hcut : Tendsto (fun n => cut n z) atTop (𝓝 (φ z)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    simp [cut, b, (originShrinkingBump n).zero_of_le_dist (le_of_lt hn)]
  simpa [ψ] using hcut.sub (hmass.mul tendsto_const_nhds)

#print axioms exists_testFunction_integral_one_away_origin
#print axioms cutout_corrected_test
#print axioms tendsto_integral_mul_shrinking_bump
#print axioms tendsto_originShrinkingBump_rOut
#print axioms tendsto_integral_cutout
#print axioms exists_zeroIntegral_awayOrigin_pointwise

end HarmonicBalls
