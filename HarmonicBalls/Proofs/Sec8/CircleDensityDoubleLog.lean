import HarmonicBalls.Proofs.Sec8.CircleDensityContinuousLimit
import Mathlib.Analysis.Convolution

/-! # Double-annulus logarithmic energy

Logarithmic potentials of smooth compactly supported densities are continuous.
The imported Section 8 argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

open MeasureTheory Set Metric Filter Real
open scoped Topology Convolution

namespace HarmonicBalls

/-- The logarithmic potential of a continuous compactly supported planar
density is continuous. -/
theorem continuous_log_potential_of_compact_support {g : ℂ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Continuous (fun w => ∫ x, g x * Real.log ‖x - w‖) := by
  have hl : LocallyIntegrable (fun x : ℂ => Real.log ‖x‖) := by
    simpa using (locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm (0 : ℂ))
  have hc := hgc.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hg hl
  convert hc using 1
  funext w
  rw [MeasureTheory.convolution_def]
  apply integral_congr_ae
  filter_upwards with x
  change g x * Real.log ‖x - w‖ = g x * Real.log ‖w - x‖
  rw [norm_sub_rev]

/-- Integrating uniformly close continuous functions against a compactly
supported probability density preserves their uniform distance bound. -/
theorem abs_integral_mul_sub_le_of_uniform_bound {g p q : ℂ → ℝ} {ε : ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgn : ∀ x, 0 ≤ g x)
    (hgm : ∫ x, g x = 1) (hp : Continuous p) (hq : Continuous q)
    (hbound : ∀ x, |p x - q x| ≤ ε) :
    |(∫ x, g x * p x) - ∫ x, g x * q x| ≤ ε := by
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hpi : Integrable (fun x => g x * p x) :=
    (hg.mul hp).integrable_of_hasCompactSupport hgc.mul_right
  have hqi : Integrable (fun x => g x * q x) :=
    (hg.mul hq).integrable_of_hasCompactSupport hgc.mul_right
  have hdiff : Integrable (fun x => g x * p x - g x * q x) := hpi.sub hqi
  rw [← integral_sub hpi hqi]
  calc
    _ ≤ ∫ x, |g x * p x - g x * q x| := abs_integral_le_integral_abs
    _ ≤ ∫ x, g x * ε := by
      apply integral_mono hdiff.abs (hgi.mul_const ε)
      intro x
      change |g x * p x - g x * q x| ≤ g x * ε
      rw [← mul_sub, abs_mul, abs_of_nonneg (hgn x)]
      exact mul_le_mul_of_nonneg_left (hbound x) (hgn x)
    _ = ε := by rw [integral_mul_const, hgm, one_mul]

/-- The double logarithmic energy of shrinking annular densities converges to
the iterated logarithmic potential of their limiting circles. -/
theorem circleDensity_double_log_tendsto {r η : ℝ} (hr : 0 < r) (hη : 0 < η)
    (z w : ℂ) :
    Tendsto (fun n => ∫ x,
      ((∫ y, circleDensity r (circleDensityWidth r η n)
        (circleDensityWidth_pos hr hη n) 0 y)⁻¹ *
        circleDensity r (circleDensityWidth r η n) (circleDensityWidth_pos hr hη n) w x) *
      (∫ y, (∫ t, circleDensity r (circleDensityWidth r η n)
        (circleDensityWidth_pos hr hη n) 0 t)⁻¹ *
        circleDensity r (circleDensityWidth r η n) (circleDensityWidth_pos hr hη n) z y *
        Real.log ‖y - x‖)) atTop
      (𝓝 (Real.circleAverage (fun x => Real.log (max r ‖z - x‖)) w r)) := by
  let q : ℂ → ℝ := fun x => Real.log (max r ‖z - x‖)
  have hq : Continuous q := by
    exact (continuous_const.max ((continuous_const.sub continuous_id).norm)).log
      (fun x => ne_of_gt (lt_of_lt_of_le hr (le_max_left _ _)))
  have hq_lim := circleDensity_circle_log_potential_tendsto hr hη hr w z
  rw [Metric.tendsto_atTop] at hq_lim ⊢
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := circleDensity_log_potential_tendsto_uniformly hr hη (ε / 2) (half_pos hε)
  obtain ⟨N₂, hN₂⟩ := hq_lim (ε / 2) (half_pos hε)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  let δ := circleDensityWidth r η n
  let hδ := circleDensityWidth_pos hr hη n
  let g : ℂ → ℝ := fun x => (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ w x
  let p : ℂ → ℝ := fun x => ∫ y, (∫ t, circleDensity r δ hδ 0 t)⁻¹ *
    circleDensity r δ hδ z y * Real.log ‖y - x‖
  have hg : Continuous g := continuous_const.mul (circleDensity_contDiff r δ hδ w).continuous
  have hgc : HasCompactSupport g := (circleDensity_hasCompactSupport hr.le hδ w).mul_left
  have hgn : ∀ x, 0 ≤ g x := fun x => mul_nonneg
    (inv_nonneg.mpr (circleDensity_integral_pos hr.le hδ 0).le)
    (circleDensity_nonneg r δ hδ w x)
  have hgm : ∫ x, g x = 1 := circleDensity_normalized_integral hr.le hδ w
  have hp : Continuous p := continuous_log_potential_of_compact_support
    (continuous_const.mul (circleDensity_contDiff r δ hδ z).continuous)
    ((circleDensity_hasCompactSupport hr.le hδ z).mul_left)
  have hbound : ∀ x, |p x - q x| ≤ ε / 2 := by
    intro x
    exact (hN₁ n (le_trans (le_max_left _ _) hn) z x).le
  have he := abs_integral_mul_sub_le_of_uniform_bound hg hgc hgn hgm hp hq hbound
  have hlim := hN₂ n (le_trans (le_max_right _ _) hn)
  rw [Real.dist_eq] at hlim ⊢
  have htriangle := abs_sub_le (∫ x, g x * p x) (∫ x, g x * q x)
    (Real.circleAverage q w r)
  change |(∫ x, g x * q x) - Real.circleAverage q w r| < ε / 2 at hlim
  change |(∫ x, g x * p x) - Real.circleAverage q w r| < ε
  linarith

/-- Integration of the whole-plane covariance against a compactly supported
probability density separates its normalization and logarithmic potential. -/
theorem integral_mul_wholePlaneCov {g : ℂ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgm : ∫ x, g x = 1) (x : ℂ) :
    (∫ y, g y * wholePlaneCov x y) = wholePlaneNormalization x +
      (∫ y, g y * wholePlaneNormalization y) - ∫ y, g y * Real.log ‖y - x‖ := by
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hni : Integrable (fun y => g y * wholePlaneNormalization y) :=
    (hg.mul continuous_wholePlaneNormalization).integrable_of_hasCompactSupport hgc.mul_right
  have hli : Integrable (fun y => g y * Real.log ‖y - x‖) := by
    have h := (locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm x
      ).integrable_smul_right_of_hasCompactSupport hg hgc
    simpa only [smul_eq_mul, mul_comm] using h
  have heq : (∫ y, g y * wholePlaneCov x y) =
      ∫ y, (g y * wholePlaneNormalization x + g y * wholePlaneNormalization y) -
        g y * Real.log ‖y - x‖ := by
    apply integral_congr_ae
    filter_upwards [ae_ne_complex x] with y hy
    have hxy : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy.symm)
    have hx : max ‖x‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    have hy' : max ‖y‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    rw [wholePlaneCov, Real.log_div (mul_ne_zero hx hy') hxy, Real.log_mul hx hy',
      norm_sub_rev]
    simp only [wholePlaneNormalization]
    ring
  have hai : Integrable (fun y => g y * wholePlaneNormalization x +
      g y * wholePlaneNormalization y) := (hgi.mul_const _).add hni
  have hsum : (∫ y, g y * wholePlaneNormalization x + g y * wholePlaneNormalization y) =
      (∫ y, g y * wholePlaneNormalization x) + ∫ y, g y * wholePlaneNormalization y :=
    integral_add (hgi.mul_const _) hni
  rw [heq, integral_sub hai hli, hsum, integral_mul_const, hgm, one_mul]

/-- Covariance of two compactly supported probability densities decomposes
into two normalization terms and their double logarithmic energy. -/
theorem wholePlaneGFFCov_pairing_probability {g h : ℂ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgm : ∫ x, g x = 1)
    (hh : Continuous h) (hhc : HasCompactSupport h) (hhm : ∫ x, h x = 1) :
    wholePlaneGFFCov (.pairing g) (.pairing h) =
      (∫ x, g x * wholePlaneNormalization x) +
      (∫ y, h y * wholePlaneNormalization y) -
      ∫ x, g x * (∫ y, h y * Real.log ‖y - x‖) := by
  let p : ℂ → ℝ := fun x => ∫ y, h y * Real.log ‖y - x‖
  have hp : Continuous p := continuous_log_potential_of_compact_support hh hhc
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hni : Integrable (fun x => g x * wholePlaneNormalization x) :=
    (hg.mul continuous_wholePlaneNormalization).integrable_of_hasCompactSupport hgc.mul_right
  have hpi : Integrable (fun x => g x * p x) :=
    (hg.mul hp).integrable_of_hasCompactSupport hgc.mul_right
  change (∫ x, g x * (∫ y, h y * wholePlaneCov x y)) = _
  simp_rw [integral_mul_wholePlaneCov hh hhc hhm]
  have heq : (fun x => g x * (wholePlaneNormalization x +
      (∫ y, h y * wholePlaneNormalization y) - p x)) =
      fun x => (g x * wholePlaneNormalization x +
        g x * (∫ y, h y * wholePlaneNormalization y)) - g x * p x := by
    funext x
    ring
  rw [heq]
  have hci := hgi.mul_const (∫ y, h y * wholePlaneNormalization y)
  have hai : Integrable (fun x => g x * wholePlaneNormalization x +
      g x * (∫ y, h y * wholePlaneNormalization y)) := hni.add hci
  rw [integral_sub hai hpi]
  have hsum : (∫ x, g x * wholePlaneNormalization x +
      g x * (∫ y, h y * wholePlaneNormalization y)) =
      (∫ x, g x * wholePlaneNormalization x) +
      ∫ x, g x * (∫ y, h y * wholePlaneNormalization y) := integral_add hni hci
  rw [hsum, integral_mul_const, hgm, one_mul]

/-- The corresponding decomposition for two circle averages. -/
theorem wholePlaneGFFCov_circles_normalization {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (z w : ℂ) :
    wholePlaneGFFCov (.circle r w) (.circle s z) =
      Real.circleAverage wholePlaneNormalization w r +
      Real.circleAverage wholePlaneNormalization z s -
      Real.circleAverage (fun x => Real.log (max s ‖z - x‖)) w r := by
  change Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) z s) w r = _
  simp_rw [circleAverage_wholePlaneCov_eq hs]
  let q : ℂ → ℝ := fun x => Real.log (max s ‖z - x‖)
  have hq : Continuous q := (continuous_const.max ((continuous_const.sub continuous_id).norm)).log
    (fun x => ne_of_gt (lt_of_lt_of_le hs (le_max_left _ _)))
  have hn : CircleIntegrable wholePlaneNormalization w r :=
    continuous_wholePlaneNormalization.continuousOn.circleIntegrable hr.le
  have hq' : CircleIntegrable q w r := hq.continuousOn.circleIntegrable hr.le
  change Real.circleAverage ((wholePlaneNormalization +
    (fun _ : ℂ => Real.circleAverage wholePlaneNormalization z s)) - q) w r = _
  rw [Real.circleAverage_sub (hn.add (circleIntegrable_const _ _ _)) hq',
    Real.circleAverage_add hn (circleIntegrable_const _ _ _), Real.circleAverage_const]

/-- The covariance of two shrinking annular pairings converges to that of
the corresponding circle averages. -/
theorem circleDensity_pairing_covariance_tendsto {r η : ℝ} (hr : 0 < r) (hη : 0 < η)
    (z w : ℂ) :
    Tendsto (fun n => wholePlaneGFFCov
      (.pairing (fun x => (∫ y, circleDensity r (circleDensityWidth r η n)
        (circleDensityWidth_pos hr hη n) 0 y)⁻¹ *
        circleDensity r (circleDensityWidth r η n) (circleDensityWidth_pos hr hη n) w x))
      (.pairing (fun y => (∫ t, circleDensity r (circleDensityWidth r η n)
        (circleDensityWidth_pos hr hη n) 0 t)⁻¹ *
        circleDensity r (circleDensityWidth r η n) (circleDensityWidth_pos hr hη n) z y)))
      atTop (𝓝 (wholePlaneGFFCov (.circle r w) (.circle r z))) := by
  rw [wholePlaneGFFCov_circles_normalization hr hr z w]
  have hlim := ((circleDensity_normalization_tendsto hr hη w).add
    (circleDensity_normalization_tendsto hr hη z)).sub (circleDensity_double_log_tendsto hr hη z w)
  apply hlim.congr'
  filter_upwards with n
  let δ := circleDensityWidth r η n
  let hδ := circleDensityWidth_pos hr hη n
  let g (v : ℂ) : ℂ → ℝ := fun x => (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ v x
  have hg (v : ℂ) : Continuous (g v) :=
    continuous_const.mul (circleDensity_contDiff r δ hδ v).continuous
  have hgc (v : ℂ) : HasCompactSupport (g v) :=
    (circleDensity_hasCompactSupport hr.le hδ v).mul_left
  have hgm (v : ℂ) : ∫ x, g v x = 1 := circleDensity_normalized_integral hr.le hδ v
  exact (wholePlaneGFFCov_pairing_probability (hg w) (hgc w) (hgm w)
    (hg z) (hgc z) (hgm z)).symm

/-- The covariance kernel is integrable against a compactly supported
continuous density at every fixed point. -/
theorem integrable_mul_wholePlaneCov {g : ℂ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (x : ℂ) :
    Integrable (fun y => g y * wholePlaneCov x y) := by
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hni : Integrable (fun y => g y * wholePlaneNormalization y) :=
    (hg.mul continuous_wholePlaneNormalization).integrable_of_hasCompactSupport hgc.mul_right
  have hli : Integrable (fun y => g y * Real.log ‖y - x‖) := by
    have h := (locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm x
      ).integrable_smul_right_of_hasCompactSupport hg hgc
    simpa only [smul_eq_mul, mul_comm] using h
  have hi : Integrable (fun y => (g y * wholePlaneNormalization x +
      g y * wholePlaneNormalization y) - g y * Real.log ‖y - x‖) :=
    ((hgi.mul_const _).add hni).sub hli
  apply hi.congr
  filter_upwards [ae_ne_complex x] with y hy
  have hxy : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy.symm)
  have hx : max ‖x‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  have hy' : max ‖y‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  rw [wholePlaneCov, Real.log_div (mul_ne_zero hx hy') hxy, Real.log_mul hx hy',
    norm_sub_rev]
  simp only [wholePlaneNormalization]
  ring

/-- The covariance potential of a compactly supported probability density is
continuous. -/
theorem continuous_wholePlaneCov_potential {g : ℂ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgm : ∫ x, g x = 1) :
    Continuous (fun x => ∫ y, g y * wholePlaneCov x y) := by
  have heq : (fun x => ∫ y, g y * wholePlaneCov x y) =
      fun x => wholePlaneNormalization x + (∫ y, g y * wholePlaneNormalization y) -
        ∫ y, g y * Real.log ‖y - x‖ := by
    funext x
    exact integral_mul_wholePlaneCov hg hgc hgm x
  rw [heq]
  exact (continuous_wholePlaneNormalization.add continuous_const).sub
    (continuous_log_potential_of_compact_support hg hgc)

/-- Bilinear expansion of the covariance of a difference of two compactly
supported probability densities. -/
theorem wholePlaneGFFCov_pairing_sub_self {g h : ℂ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgm : ∫ x, g x = 1)
    (hh : Continuous h) (hhc : HasCompactSupport h) (hhm : ∫ x, h x = 1) :
    wholePlaneGFFCov (.pairing (g - h)) (.pairing (g - h)) =
      wholePlaneGFFCov (.pairing g) (.pairing g) -
      wholePlaneGFFCov (.pairing g) (.pairing h) -
      wholePlaneGFFCov (.pairing h) (.pairing g) +
      wholePlaneGFFCov (.pairing h) (.pairing h) := by
  let p : ℂ → ℝ := fun x => ∫ y, g y * wholePlaneCov x y
  let q : ℂ → ℝ := fun x => ∫ y, h y * wholePlaneCov x y
  have hp : Continuous p := continuous_wholePlaneCov_potential hg hgc hgm
  have hq : Continuous q := continuous_wholePlaneCov_potential hh hhc hhm
  have hgp : Integrable (fun x => g x * p x) :=
    (hg.mul hp).integrable_of_hasCompactSupport hgc.mul_right
  have hgq : Integrable (fun x => g x * q x) :=
    (hg.mul hq).integrable_of_hasCompactSupport hgc.mul_right
  have hhp : Integrable (fun x => h x * p x) :=
    (hh.mul hp).integrable_of_hasCompactSupport hhc.mul_right
  have hhq : Integrable (fun x => h x * q x) :=
    (hh.mul hq).integrable_of_hasCompactSupport hhc.mul_right
  have hinner (x : ℂ) : (∫ y, (g y - h y) * wholePlaneCov x y) = p x - q x := by
    simp_rw [sub_mul]
    exact integral_sub (integrable_mul_wholePlaneCov hg hgc x)
      (integrable_mul_wholePlaneCov hh hhc x)
  change (∫ x, (g x - h x) * (∫ y, (g y - h y) * wholePlaneCov x y)) =
    (∫ x, g x * p x) - (∫ x, g x * q x) - (∫ x, h x * p x) + ∫ x, h x * q x
  simp_rw [hinner]
  have heq : (fun x => (g x - h x) * (p x - q x)) =
      fun x => (g x * p x - g x * q x) - (h x * p x - h x * q x) := by
    funext x
    ring
  rw [heq]
  have h₁ : Integrable (fun x => g x * p x - g x * q x) := hgp.sub hgq
  have h₂ : Integrable (fun x => h x * p x - h x * q x) := hhp.sub hhq
  rw [integral_sub h₁ h₂, integral_sub hgp hgq, integral_sub hhp hhq]
  ring

end HarmonicBalls
