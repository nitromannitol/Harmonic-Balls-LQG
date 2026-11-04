import HarmonicBalls.Proofs.Sec6.CriterionThreeFromPrevalence
import HarmonicBalls.Proofs.Sec6.GoodAnnulusSpatialMap

/-! # Approximating a center by the lattice -/

namespace HarmonicBalls.Section6

open Metric Set

/-- Every complex point lies within twice the mesh size of a point in the
square lattice. -/
theorem exists_scaledLattice_dist_lt (z : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ w ∈ scaledLattice δ, dist z w < 2 * δ := by
  let j : ℤ := ⌊z.re / δ⌋
  let k : ℤ := ⌊z.im / δ⌋
  let w : ℂ := (δ : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)
  refine ⟨w, ⟨j, k, rfl⟩, ?_⟩
  have hj₁ : δ * (j : ℝ) ≤ z.re := by
    have h := (le_div_iff₀ hδ).mp (Int.floor_le (z.re / δ))
    simpa only [mul_comm] using h
  have hj₂ : z.re < δ * ((j : ℝ) + 1) := by
    have h := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (z.re / δ))
    simpa only [mul_comm] using h
  have hk₁ : δ * (k : ℝ) ≤ z.im := by
    have h := (le_div_iff₀ hδ).mp (Int.floor_le (z.im / δ))
    simpa only [mul_comm] using h
  have hk₂ : z.im < δ * ((k : ℝ) + 1) := by
    have h := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (z.im / δ))
    simpa only [mul_comm] using h
  have hre : 0 ≤ (z - w).re ∧ (z - w).re < δ := by
    simp only [w, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.intCast_re, Complex.mul_re,
      Complex.intCast_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one,
      sub_zero, add_zero]
    constructor <;> linarith
  have him : 0 ≤ (z - w).im ∧ (z - w).im < δ := by
    simp only [w, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_im, Complex.intCast_re, Complex.mul_im, Complex.intCast_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one,
      add_zero, zero_add]
    constructor <;> linarith
  rw [dist_eq_norm]
  calc ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ < 2 * δ := by rw [abs_of_nonneg hre.1, abs_of_nonneg him.1]; linarith [hre.2, him.2]

/-- After shifting by a nearby lattice point, the tested lattice points of
an off-center unit annulus lie in the prevalence grid. -/
theorem shifted_annulus_lattice_subset_prevalenceGrid {n : ℕ} (hn : 9 ≤ n)
    {x y : ℂ} (hy : y ∈ scaledLattice (dyadicScale n / 100))
    (hxy : dist x y < 2 * (dyadicScale n / 100)) :
    ∀ z ∈ scaledLattice (dyadicScale n / 100) ∩ annulus x (1 / 2) 1,
      z - y ∈ prevalenceGrid (dyadicScale n) := by
  intro z hz
  have hε0 : 0 < dyadicScale n := by unfold dyadicScale; positivity
  have hε1 : dyadicScale n ≤ 1 := by
    unfold dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hsqrt : Real.sqrt (dyadicScale n) ≤ 1 / 22 := by
    rw [Real.sqrt_le_left (by norm_num)]
    unfold dyadicScale
    calc (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ 9 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      _ ≤ (1 / 22) ^ 2 := by norm_num
  have hzupper : ‖z - x‖ < 1 := by simpa [dist_eq_norm] using hz.2.1
  have hzlower : 1 / 2 < ‖z - x‖ := by
    have h : ¬ dist z x ≤ (1 / 2 : ℝ) := hz.2.2
    simpa [dist_eq_norm] using lt_of_not_ge h
  have hclose : ‖x - y‖ < 2 * (dyadicScale n / 100) := by
    simpa [dist_eq_norm] using hxy
  have hup : ‖z - y‖ ≤ ‖z - x‖ + ‖x - y‖ := by
    calc ‖z - y‖ = ‖(z - x) + (x - y)‖ := by congr 1; abel
      _ ≤ ‖z - x‖ + ‖x - y‖ := norm_add_le _ _
  have hlow : ‖z - x‖ ≤ ‖z - y‖ + ‖x - y‖ := by
    calc ‖z - x‖ = ‖(z - y) - (x - y)‖ := by congr 1; abel
      _ ≤ ‖z - y‖ + ‖x - y‖ := norm_sub_le _ _
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change dist (z - y) 0 < 1 + dyadicScale n
    rw [dist_zero_right]
    linarith
  · change ¬ dist (z - y) 0 < 10 * Real.sqrt (dyadicScale n)
    rw [dist_zero_right]
    linarith
  · obtain ⟨j, k, hjk⟩ := hz.1
    obtain ⟨j', k', hjk'⟩ := hy
    refine ⟨j - j', k - k', ?_⟩
    rw [hjk, hjk']
    push_cast
    ring

/-- A translated subrange prevalence event gives the criterion-three count
on an arbitrary unit annulus, after correcting the lattice phase. -/
theorem criterionThree_count_of_translated_subrange_prevalence
    {μ : MeasureTheory.Measure ℂ} {c a b : ℝ} (hc : 0 < c) {n : ℕ} (hn : 9 ≤ n)
    {x y : ℂ} (hy : y ∈ scaledLattice (dyadicScale n / 100))
    (hxy : dist x y < 2 * (dyadicScale n / 100))
    (h : ∀ z ∈ prevalenceGrid (dyadicScale n),
      c * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
            IsGoodAnnulus (μ.map (fun w : ℂ => w + -y)) r z a b}.ncard : ℝ)) :
    ∀ z ∈ scaledLattice (dyadicScale n * 1 / 100) ∩ annulus x (1 / 2) 1,
      c * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n * 1) (Real.sqrt (dyadicScale n) * 1) ∧
          (∃ k : ℕ, 1 ≤ k ∧ r = 1 * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z a b}.ncard : ℝ) := by
  intro z hz
  have hε0 : 0 < dyadicScale n := by unfold dyadicScale; positivity
  have hsqrt := sqrt_dyadicScale_le_one_twentieth hn
  have hε1 : dyadicScale n ≤ 1 := by
    unfold dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hz' : z - y ∈ prevalenceGrid (dyadicScale n) :=
    shifted_annulus_lattice_subset_prevalenceGrid hn hy hxy z (by simpa using hz)
  have hgood (r : ℝ) : IsGoodAnnulus (μ.map (fun w : ℂ => w + -y)) r (z - y) a b ↔
      IsGoodAnnulus μ r z a b := by
    simpa only [sub_eq_add_neg] using isGoodAnnulus_map_add_iff (-y) μ r z a b
  refine ((logb_neg_half_le (by norm_num) hc hε0 hε1).trans (h (z - y) hz')).trans ?_
  norm_cast
  refine Set.ncard_le_ncard (fun r hr => ?_) ?_
  · have hr_sqrt : r ≤ Real.sqrt (dyadicScale n) := by
      refine hr.1.2.trans ?_
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by norm_num)
    obtain ⟨k, hk⟩ := hr.2.1
    have hk1 : 1 ≤ k := by
      by_contra hk1
      have : k = 0 := by omega
      subst k
      simp only [pow_zero] at hk
      linarith
    exact ⟨by simpa using ⟨hr.1.1, hr_sqrt⟩, ⟨k, hk1, by simpa using hk⟩,
      (hgood r).mp hr.2.2⟩
  · refine finite_of_geometric (q := (7 : ℝ)⁻¹) (A := 1) (lo := dyadicScale n)
      (by norm_num) (by norm_num) hε0 fun r hr => ⟨by simpa using hr.1.1, ?_⟩
    obtain ⟨k, _, hk⟩ := hr.2.1
    exact ⟨k, hk⟩

end HarmonicBalls.Section6
