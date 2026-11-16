import HarmonicBalls.Proofs.Potential.BrownianIncrementRieszMoment

/-! # Scaling of inverse-power time energies

The time-lag energy on an interval scales as a power of its length.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

private lemma map_restrict_interval_affine (u h : ℝ) (hh : 0 < h) :
    Measure.map (fun t : ℝ => u + h * t) (volume.restrict (Icc (0 : ℝ) 1)) =
      ENNReal.ofReal h⁻¹ • volume.restrict (Icc u (u + h)) := by
  have hpre : (fun t : ℝ => u + h * t) ⁻¹' Icc u (u + h) = Icc (0 : ℝ) 1 := by
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro ht <;> constructor <;> nlinarith
  have hmap : Measure.map (fun t : ℝ => u + h * t) volume = ENNReal.ofReal h⁻¹ • volume := by
    rw [show (fun t : ℝ => u + h * t) = (fun t : ℝ => u + t) ∘ (fun t : ℝ => h * t) from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), Real.map_volume_mul_left hh.ne',
      Measure.map_smul _ (by fun_prop)]
    simp [abs_of_pos (inv_pos.mpr hh), map_add_left_eq_self]
  rw [← hpre, ← Measure.restrict_map (by fun_prop) measurableSet_Icc, hmap,
    Measure.restrict_smul]


/-- The time-lag energy scales under an affine map. -/
private lemma time_energy_affine (u h q : ℝ) (hh : 0 < h) :
    let μ := volume.restrict (Icc (0 : ℝ) 1)
    let ν := volume.restrict (Icc u (u + h))
    (ENNReal.ofReal h⁻¹)^2 * (∫⁻ p : ℝ × ℝ,
      (ENNReal.ofReal |p.1 - p.2|) ^ (-q) ∂(ν.prod ν)) =
    (ENNReal.ofReal h) ^ (-q) * (∫⁻ p : ℝ × ℝ,
      (ENNReal.ofReal |p.1 - p.2|) ^ (-q) ∂(μ.prod μ)) := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let ν : Measure ℝ := volume.restrict (Icc u (u + h))
  let f : ℝ → ℝ := fun t => u + h * t
  let K : ℝ × ℝ → ℝ≥0∞ := fun p => (ENNReal.ofReal |p.1 - p.2|) ^ (-q)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hK : Measurable K := by dsimp [K]; fun_prop
  have hmap : μ.map f = ENNReal.ofReal h⁻¹ • ν := map_restrict_interval_affine u h hh
  have heq : (∫⁻ p, K p ∂((μ.map f).prod (μ.map f))) =
      ∫⁻ p, K (Prod.map f f p) ∂(μ.prod μ) := by
    rw [Measure.map_prod_map _ _ hf hf, lintegral_map hK (hf.prodMap hf)]
  rw [hmap, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    lintegral_smul_measure] at heq
  have hk : ∀ p : ℝ × ℝ, K (Prod.map f f p) = (ENNReal.ofReal h) ^ (-q) * K p := by
    intro p
    dsimp [K, f, Prod.map]
    have hid : u + h * p.1 - (u + h * p.2) = h * (p.1 - p.2) := by ring
    rw [hid, abs_mul, abs_of_pos hh, ENNReal.ofReal_mul (le_of_lt hh),
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
  simp_rw [hk] at heq
  rw [lintegral_const_mul _ hK] at heq
  simpa only [pow_two, smul_eq_mul] using heq


/-- The inverse-power time-lag energy of an interval has its expected scaling. -/
theorem lintegral_interval_abs_sub_rpow_scale (u h q : ℝ) (hh : 0 < h) :
    let μ := volume.restrict (Icc (0 : ℝ) 1)
    let ν := volume.restrict (Icc u (u + h))
    (∫⁻ p : ℝ × ℝ, (ENNReal.ofReal |p.1 - p.2|) ^ (-q) ∂(ν.prod ν)) =
      (ENNReal.ofReal h) ^ (2 - q) * (∫⁻ p : ℝ × ℝ,
        (ENNReal.ofReal |p.1 - p.2|) ^ (-q) ∂(μ.prod μ)) := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let ν : Measure ℝ := volume.restrict (Icc u (u + h))
  let K : ℝ × ℝ → ℝ≥0∞ := fun p => (ENNReal.ofReal |p.1 - p.2|) ^ (-q)
  let x : ℝ≥0∞ := ENNReal.ofReal h
  have hx0 : x ≠ 0 := (ENNReal.ofReal_pos.mpr hh).ne'
  have hxt : x ≠ ∞ := ENNReal.ofReal_ne_top
  have heq := time_energy_affine u h q hh
  change (ENNReal.ofReal h⁻¹)^2 * (∫⁻ p, K p ∂(ν.prod ν)) =
    x ^ (-q) * (∫⁻ p, K p ∂(μ.prod μ)) at heq
  rw [ENNReal.ofReal_inv_of_pos hh] at heq
  have hinv : x^2 * x⁻¹^2 = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel hx0 hxt, one_pow]
  change (∫⁻ p, K p ∂(ν.prod ν)) =
    x ^ (2 - q) * (∫⁻ p, K p ∂(μ.prod μ))
  calc
    _ = (x^2 * x⁻¹^2) * (∫⁻ p, K p ∂(ν.prod ν)) := by rw [hinv, one_mul]
    _ = x^2 * (x⁻¹^2 * (∫⁻ p, K p ∂(ν.prod ν))) := by rw [mul_assoc]
    _ = x^2 * (x ^ (-q) * (∫⁻ p, K p ∂(μ.prod μ))) := by rw [heq]
    _ = x ^ (2 - q) * (∫⁻ p, K p ∂(μ.prod μ)) := by
      rw [← mul_assoc, ← ENNReal.rpow_ofNat, ← ENNReal.rpow_add _ _ hx0 hxt]
      congr 2


/-- The subcritical extended-valued time-lag energy is finite on the unit square. -/
theorem lintegral_unit_square_ennreal_abs_sub_rpow_lt_top {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    (∫⁻ p : ℝ × ℝ, (ENNReal.ofReal |p.1 - p.2|) ^ (-q)
      ∂((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1)))) < ∞ := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hd : (μ.prod μ) (Set.diagonal ℝ) = 0 := by
    apply Measure.measure_prod_null_of_ae_null measurableSet_diagonal
    filter_upwards [] with t
    simp [Set.diagonal]
  have hae : ∀ᵐ p ∂(μ.prod μ), p.1 ≠ p.2 := by
    have h := measure_eq_zero_iff_ae_notMem.1 hd
    simpa [Set.diagonal] using h
  have heq : (∫⁻ p : ℝ × ℝ, (ENNReal.ofReal |p.1 - p.2|) ^ (-q) ∂(μ.prod μ)) =
      ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (|p.1 - p.2| ^ (-q)) ∂(μ.prod μ) := by
    apply lintegral_congr_ae
    filter_upwards [hae] with p hp
    exact ENNReal.ofReal_rpow_of_pos (abs_pos.mpr (sub_ne_zero.mpr hp))
  rw [show (volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1)) =
    μ.prod μ from rfl, heq]
  exact lintegral_unit_square_abs_sub_rpow_lt_top hq0 hq1


/-- Nonnegative time pushforward preserves the inverse-power energy of a nonnegative interval. -/
theorem lintegral_interval_time_lag_eq (u h q : ℝ) (hu : 0 ≤ u) :
    let μ := volume.restrict (Icc u (u + h))
    let ν := Measure.map Real.toNNReal μ
    (∫⁻ p : ℝ≥0 × ℝ≥0, (ENNReal.ofReal (nndist (p.1 : ℝ) (p.2 : ℝ))) ^ (-q)
      ∂(ν.prod ν)) =
    ∫⁻ p : ℝ × ℝ, (ENNReal.ofReal |p.1 - p.2|) ^ (-q) ∂(μ.prod μ) := by
  let μ : Measure ℝ := volume.restrict (Icc u (u + h))
  have hm : Measurable Real.toNNReal := continuous_real_toNNReal.measurable
  have hf : Measurable (fun p : ℝ≥0 × ℝ≥0 =>
      (ENNReal.ofReal (nndist (p.1 : ℝ) (p.2 : ℝ))) ^ (-q)) := by fun_prop
  change (∫⁻ p : ℝ≥0 × ℝ≥0, (ENNReal.ofReal (nndist (p.1 : ℝ) (p.2 : ℝ))) ^ (-q)
      ∂((Measure.map Real.toNNReal μ).prod (Measure.map Real.toNNReal μ))) = _
  rw [Measure.map_prod_map _ _ hm hm, lintegral_map hf (hm.prodMap hm)]
  have hmem : ∀ᵐ p ∂(μ.prod μ), p ∈ Icc u (u + h) ×ˢ Icc u (u + h) := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  apply lintegral_congr_ae
  filter_upwards [hmem] with p hp
  have h1 : 0 ≤ p.1 := hu.trans hp.1.1
  have h2 : 0 ≤ p.2 := hu.trans hp.2.1
  change (ENNReal.ofReal (nndist ((Real.toNNReal p.1 : ℝ≥0) : ℝ)
    ((Real.toNNReal p.2 : ℝ≥0) : ℝ))) ^ (-q) = _
  simp only [Real.toNNReal_of_nonneg h1, Real.toNNReal_of_nonneg h2, coe_nndist, Real.dist_eq]
  rfl


/-- The expected Brownian inverse-power energy on a time interval scales with its length. -/
theorem lintegral_planarBrownianMotion_interval_pair_enorm_rpow_neg
    (x : ℂ) (u h a : ℝ) (hu : 0 ≤ u) (hh : 0 < h) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc u (u + h)))
    let μ := volume.restrict (Icc (0 : ℝ) 1)
    (∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0,
      (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-a) ∂(ν.prod ν) ∂(planarBrownianMotion x)) =
    (ENNReal.ofReal h) ^ (2 - a / 2) *
      (∫⁻ p : ℝ × ℝ, (ENNReal.ofReal |p.1 - p.2|) ^ (-(a / 2)) ∂(μ.prod μ)) *
      ∫⁻ z, (ENNReal.ofReal ‖z‖) ^ (-a) ∂stdPlanarGaussian := by
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc u (u + h)))
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  dsimp only
  rw [lintegral_planarBrownianMotion_pair_enorm_rpow_neg]
  have hlag := lintegral_interval_time_lag_eq u h (a / 2) hu
  have hscale := lintegral_interval_abs_sub_rpow_scale u h (a / 2) hh
  rw [neg_div, hlag, hscale]


/-- Subcritical Brownian inverse-power interval energies have a finite scaling constant. -/
theorem exists_planarBrownianMotion_interval_pair_enorm_rpow_neg (x : ℂ) {a : ℝ}
    (ha : 0 < a) (ha2 : a < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (u h : ℝ), 0 ≤ u → 0 < h →
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc u (u + h)))
      (∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0,
        (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-a) ∂(ν.prod ν) ∂(planarBrownianMotion x)) =
      (ENNReal.ofReal h) ^ (2 - a / 2) * C := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  let C : ℝ≥0∞ := (∫⁻ p : ℝ × ℝ,
      (ENNReal.ofReal |p.1 - p.2|) ^ (-(a / 2)) ∂(μ.prod μ)) *
      ∫⁻ z, (ENNReal.ofReal ‖z‖) ^ (-a) ∂stdPlanarGaussian
  refine ⟨C, ?_, ?_⟩
  · exact ENNReal.mul_lt_top
      (lintegral_unit_square_ennreal_abs_sub_rpow_lt_top (by linarith) (by linarith))
      (lintegral_stdPlanarGaussian_enorm_rpow_neg_lt_top ha ha2)
  · intro u h hu hh
    dsimp only
    rw [lintegral_planarBrownianMotion_interval_pair_enorm_rpow_neg x u h a hu hh]
    exact mul_assoc _ _ _

end HarmonicBalls
