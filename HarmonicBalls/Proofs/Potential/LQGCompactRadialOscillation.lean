import HarmonicBalls.Proofs.Potential.LQGCircleBoxGrid
import HarmonicBalls.Proofs.Potential.LQGCircleBoxModulus
import HarmonicBalls.Proofs.Potential.LQGCircleRadialGridTail

/-! # Compact-center circle-average oscillation

Spatial box estimates and finite grid bounds control radial increments uniformly.
-/

noncomputable section
open MeasureTheory Filter Set Metric LatticeProb.LQG LatticeProb.Gauss

namespace HarmonicBalls

/-- A point of a compact disk and a nearby grid point lie in the same rescaled box. -/
theorem exists_circle_box_grid_point (R : ℝ) (S : ℕ → Finset ℂ)
    (hS : ∀ k m n,
      m ∈ Finset.Icc (-(⌈max R 0 * 2 ^ k⌉₊ : ℤ)) ⌈max R 0 * 2 ^ k⌉₊ →
      n ∈ Finset.Icc (-(⌈max R 0 * 2 ^ k⌉₊ : ℤ)) ⌈max R 0 * 2 ^ k⌉₊ →
      ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 0 ≤ z.im → z.im ≤ 1 →
      ∃ u : ℂ, 0 ≤ u.re ∧ u.re ≤ 1 ∧ 0 ≤ u.im ∧ u.im ≤ 1 ∧
        |z.re - u.re| < dyadicScale (k + 1) ∧
        |z.im - u.im| < dyadicScale (k + 1) ∧
        circleBoxCentre (dyadicScale k) m n + (dyadicScale k : ℂ) * u ∈ S k)
    (k : ℕ) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ∃ u : ℂ,
      (⌊z.re / dyadicScale k⌋, ⌊z.im / dyadicScale k⌋) ∈
        Finset.Icc (-(⌈max R 0 * 2 ^ k⌉₊ : ℤ)) ⌈max R 0 * 2 ^ k⌉₊ ×ˢ
        Finset.Icc (-(⌈max R 0 * 2 ^ k⌉₊ : ℤ)) ⌈max R 0 * 2 ^ k⌉₊ ∧
      0 ≤ u.re ∧ u.re ≤ 1 ∧ 0 ≤ u.im ∧ u.im ≤ 1 ∧
      |Int.fract (z.re / dyadicScale k) - u.re| < dyadicScale (k + 1) ∧
      |Int.fract (z.im / dyadicScale k) - u.im| < dyadicScale (k + 1) ∧
      circleBoxCentre (dyadicScale k) ⌊z.re / dyadicScale k⌋ ⌊z.im / dyadicScale k⌋ +
        (dyadicScale k : ℂ) * u ∈ S k := by
  have hε : 0 < dyadicScale k := by simp [dyadicScale]
  have h2ε : (2 : ℝ) ^ k * dyadicScale k = 1 := by
    simp only [dyadicScale]
    rw [← mul_pow]
    norm_num
  have hbound : ∀ t : ℝ, |t| ≤ ‖z‖ → |t / dyadicScale k| ≤ max R 0 * 2 ^ k := by
    intro t ht
    rw [abs_div, abs_of_pos hε, div_le_iff₀ hε, mul_assoc, h2ε, mul_one]
    exact ht.trans (hz.trans (le_max_left _ _))
  have hm := floor_mem_Icc_of_abs_le (hbound _ (Complex.abs_re_le_norm z)) (Nat.le_ceil _)
  have hn := floor_mem_Icc_of_abs_le (hbound _ (Complex.abs_im_le_norm z)) (Nat.le_ceil _)
  obtain ⟨u, hu0, hu1, hv0, hv1, hre, him, hmem⟩ := hS k _ _ hm hn
    ⟨Int.fract (z.re / dyadicScale k), Int.fract (z.im / dyadicScale k)⟩
    (Int.fract_nonneg _) (Int.fract_lt_one _).le (Int.fract_nonneg _) (Int.fract_lt_one _).le
  exact ⟨u, Finset.mem_product.mpr ⟨hm, hn⟩, hu0, hu1, hv0, hv1, hre, him, hmem⟩

/-- A box modulus bounds the spatial displacement to a same-box grid point. -/
theorem circle_box_spatial_bound {Ω : Type*} (hcirc : Ω → ℝ → ℂ → ℝ)
    (ω : Ω) (k : ℕ) (z u : ℂ) (s E : ℝ)
    (hs1 : dyadicScale k / 2 ≤ s) (hs2 : s ≤ dyadicScale k)
    (hu0 : 0 ≤ u.re) (hu1 : u.re ≤ 1) (hv0 : 0 ≤ u.im) (hv1 : u.im ≤ 1)
    (hre : |Int.fract (z.re / dyadicScale k) - u.re| < dyadicScale (k + 1))
    (him : |Int.fract (z.im / dyadicScale k) - u.im| < dyadicScale (k + 1))
    (hbox : ∀ x ∈ Set.Icc circleBoxLower circleBoxUpper,
      ∀ y ∈ Set.Icc circleBoxLower circleBoxUpper,
      dist x y < 1 / 2 ^ k →
      |circleRescaled hcirc (dyadicScale k)
          (circleBoxCentre (dyadicScale k) ⌊z.re / dyadicScale k⌋ ⌊z.im / dyadicScale k⌋) x ω -
        circleRescaled hcirc (dyadicScale k)
          (circleBoxCentre (dyadicScale k) ⌊z.re / dyadicScale k⌋ ⌊z.im / dyadicScale k⌋) y ω| ≤ E) :
    |hcirc ω s z - hcirc ω s
      (circleBoxCentre (dyadicScale k) ⌊z.re / dyadicScale k⌋ ⌊z.im / dyadicScale k⌋ +
        (dyadicScale k : ℂ) * u)| ≤ E := by
  have hε : 0 < dyadicScale k := by simp [dyadicScale]
  let x := circleBoxPoint (dyadicScale k) s z
  let y : Fin 3 → ℝ := ![s / dyadicScale k, u.re, u.im]
  have hx : x ∈ Set.Icc circleBoxLower circleBoxUpper := circleBoxPoint_mem hε hs1 hs2 z
  have hy : y ∈ Set.Icc circleBoxLower circleBoxUpper := by
    have h1 : (1 : ℝ) / 2 ≤ s / dyadicScale k := by rw [le_div_iff₀ hε]; linarith
    have h2 : s / dyadicScale k ≤ 1 := (div_le_one hε).2 hs2
    refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i <;>
      simp_all [y, circleBoxLower, circleBoxUpper]
  have hmesh : dyadicScale (k + 1) < 1 / 2 ^ k := by
    simp only [dyadicScale, pow_succ]
    have hp : (0 : ℝ) < ((2 : ℝ) ^ k)⁻¹ := by positivity
    rw [one_div, inv_pow]
    norm_num at hp ⊢
  have hdist : dist x y < 1 / 2 ^ k := by
    rw [dist_pi_lt_iff (by positivity)]
    intro i
    fin_cases i
    · simp [x, y, circleBoxPoint]
    · simpa [x, y, circleBoxPoint, Real.dist_eq] using hre.trans hmesh
    · simpa [x, y, circleBoxPoint, Real.dist_eq] using him.trans hmesh
  have h := hbox x hx y hy hdist
  rw [show circleRescaled hcirc (dyadicScale k)
      (circleBoxCentre (dyadicScale k) ⌊z.re / dyadicScale k⌋ ⌊z.im / dyadicScale k⌋) x ω =
      hcirc ω s z from circleRescaled_circleBoxPoint hcirc hε.ne' s z ω] at h
  have hyval : circleRescaled hcirc (dyadicScale k)
      (circleBoxCentre (dyadicScale k) ⌊z.re / dyadicScale k⌋ ⌊z.im / dyadicScale k⌋) y ω =
      hcirc ω s (circleBoxCentre (dyadicScale k) ⌊z.re / dyadicScale k⌋
        ⌊z.im / dyadicScale k⌋ + (dyadicScale k : ℂ) * u) := by
    simp [circleRescaled, y, mul_div_cancel₀ _ hε.ne']
  rwa [hyval] at h

/-- Radial circle-average oscillations are eventually sublinear, uniformly on
compact disks and over all radii in each dyadic band. -/
theorem ae_eventually_compact_radial_oscillation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (R : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, ∀ z : ℂ, ‖z‖ ≤ R → ∀ s,
      dyadicScale k / 2 ≤ s → s ≤ dyadicScale k →
      |hcirc ω s z - hcirc ω (dyadicScale k) z| ≤ δ * (k + 1) := by
  obtain ⟨S, hS⟩ := exists_compact_circle_box_grids R
  let c : ℝ := (2⁻¹ : ℝ) ^ (1 / 4 : ℝ)
  have hc0 : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hc1 : c < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
  let K : ℝ := 7 / (1 - c)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * K / δ)
  have hgrid := ae_eventually_grid_radial_oscillation hh (show 0 < δ / 2 by positivity)
    (show (0 : ℝ) < 16 by norm_num)
    (show 0 ≤ 676 * (2 * max R 0 + 3) ^ 2 by positivity) S (fun k => (hS k).1)
  have hbox := ae_eventually_circleRescaled_sub_le hh (a := 1) (by norm_num) R
  filter_upwards [hgrid, hbox] with ω hgridω hboxω
  filter_upwards [hgridω, hboxω, eventually_ge_atTop (max N 1)] with k hg hb hk z hz s hs1 hs2
  have hk1 : 1 ≤ k := (le_max_right _ _).trans hk
  have hkN : N ≤ k := (le_max_left _ _).trans hk
  have hkreal : (N : ℝ) ≤ k := by exact_mod_cast hkN
  have hlarge : 2 * K ≤ δ / 2 * ((k : ℝ) + 1) := by
    have := (div_lt_iff₀ hδ).mp hN
    nlinarith
  obtain ⟨u, hmn, hu0, hu1, hv0, hv1, hre, him, hmem⟩ :=
    exists_circle_box_grid_point R S (fun k => (hS k).2) k z hz
  have hb' := hb _ hmn
  simp only [one_mul, Nat.floor_natCast, max_eq_left hk1] at hb'
  let E : ℝ := 7 * c ^ k / (1 - c)
  have hE : E ≤ K := by
    dsimp [E, K]
    gcongr
    nlinarith [pow_le_one₀ hc0.le hc1.le (n := k)]
  have hs := circle_box_spatial_bound hcirc ω k z u s E hs1 hs2 hu0 hu1 hv0 hv1 hre him hb'
  have he := circle_box_spatial_bound hcirc ω k z u (dyadicScale k) E
    (by
      have hpos : 0 < dyadicScale k := by simp [dyadicScale]
      linarith) le_rfl
    hu0 hu1 hv0 hv1 hre him hb'
  have hr := hg _ hmem s hs1 hs2
  change |hcirc ω s _ - hcirc ω (dyadicScale k) _| ≤ δ / 2 * ((k : ℝ) + 1) at hr
  have htri := abs_sub_le (hcirc ω s z)
    (hcirc ω s (circleBoxCentre (dyadicScale k) ⌊z.re / dyadicScale k⌋
      ⌊z.im / dyadicScale k⌋ + (dyadicScale k : ℂ) * u))
    (hcirc ω (dyadicScale k) z)
  have htri' := abs_sub_le (hcirc ω s (circleBoxCentre (dyadicScale k)
      ⌊z.re / dyadicScale k⌋ ⌊z.im / dyadicScale k⌋ + (dyadicScale k : ℂ) * u))
    (hcirc ω (dyadicScale k) (circleBoxCentre (dyadicScale k)
      ⌊z.re / dyadicScale k⌋ ⌊z.im / dyadicScale k⌋ + (dyadicScale k : ℂ) * u))
    (hcirc ω (dyadicScale k) z)
  rw [abs_sub_comm] at he
  nlinarith

end HarmonicBalls
