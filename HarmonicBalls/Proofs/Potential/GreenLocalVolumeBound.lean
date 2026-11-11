import HarmonicBalls.Proofs.SecA.Basic
import HarmonicBalls.Proofs.Sec6.GreenIntegrability
import HarmonicBalls.Proofs.Sec6.GreenTranslation
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Logarithmic kernels and local volume

Scaling and limiting facts for the planar logarithmic kernel used in local Green
function estimates. The potential-theoretic infrastructure uses work of
Leonardo Bonanno. -/

namespace HarmonicBalls

open MeasureTheory Filter Topology Real Metric

/-- The total mass of the positive logarithmic kernel scales as area. -/
theorem integral_posLog_div_norm_scale {r : ℝ} (hr : 0 < r) :
    (∫ z : ℂ, log⁺ (r / ‖z‖)) =
      r ^ 2 * ∫ z : ℂ, log⁺ (1 / ‖z‖) := by
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure ℂ)
    (fun z : ℂ => log⁺ (1 / ‖z‖)) hr.le
  have heq : (fun z : ℂ => log⁺ (1 / ‖r⁻¹ • z‖)) =
      fun z : ℂ => log⁺ (r / ‖z‖) := by
    funext z
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hr.le)]
    congr 1
    field_simp
  rw [heq, Complex.finrank_real_complex] at h
  simpa only [smul_eq_mul] using h

/-- A logarithmic kernel at one scale splits into its small-scale part and
an additive term, including at the pole under the real logarithm convention. -/
theorem posLog_div_norm_le_scale {R r : ℝ} (hr : 0 < r) (z : ℂ) :
    log⁺ (R / ‖z‖) ≤ log⁺ (R / r) + log⁺ (r / ‖z‖) := by
  have h : R / ‖z‖ = (R / r) * (r / ‖z‖) := by
    field_simp
  rw [h]
  exact Real.posLog_mul

/-- The positive logarithmic kernel has a uniform local volume bound for
balls with arbitrary centre, even when they contain the pole. -/
theorem integral_posLog_div_norm_sub_ball_le {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (x c : ℂ) :
    (∫ z in Metric.ball c r, log⁺ (R / ‖z - x‖)) ≤
      Real.pi * r ^ 2 * log⁺ (R / r) +
        r ^ 2 * ∫ z : ℂ, log⁺ (1 / ‖z‖) := by
  let f : ℂ → ℝ := fun z => log⁺ (r / ‖z - x‖)
  have hf : Integrable f := by
    have h := (measurePreserving_add_right volume (-x)).integrable_comp_of_integrable
      (integrable_posLog_div_norm hr)
    simpa only [f, sub_eq_add_neg, Function.comp_def] using h
  have hF : IntegrableOn (fun z : ℂ => log⁺ (R / ‖z - x‖)) (Metric.ball c r) := by
    have h := (measurePreserving_add_right volume (-x)).integrable_comp_of_integrable
      (integrable_posLog_div_norm hR)
    have hglobal : Integrable (fun z : ℂ => log⁺ (R / ‖z - x‖)) := by
      simpa only [sub_eq_add_neg, Function.comp_def] using h
    exact hglobal.integrableOn
  have hc : IntegrableOn (fun _ : ℂ => log⁺ (R / r)) (Metric.ball c r) :=
    integrableOn_const measure_ball_lt_top.ne
  calc
    _ ≤ ∫ z in Metric.ball c r, (log⁺ (R / r) + f z) := by
      apply integral_mono_ae hF (hc.add hf.integrableOn)
      exact Filter.Eventually.of_forall fun z => posLog_div_norm_le_scale hr (z - x)
    _ = (∫ _z in Metric.ball c r, log⁺ (R / r)) + ∫ z in Metric.ball c r, f z :=
      integral_add hc hf.integrableOn
    _ ≤ (∫ _z in Metric.ball c r, log⁺ (R / r)) + ∫ z, f z := by
      apply add_le_add_right
      exact integral_mono_measure Measure.restrict_le_self
        (Filter.Eventually.of_forall fun _ => posLog_nonneg) hf
    _ = _ := by
      rw [integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, Complex.volume_ball]
      have hfint : (∫ z, f z) = ∫ z : ℂ, log⁺ (r / ‖z‖) := by
        simpa only [f, sub_eq_add_neg] using
          (integral_add_right_eq_self (μ := volume) (fun z : ℂ => log⁺ (r / ‖z‖)) (-x))
      rw [hfint, integral_posLog_div_norm_scale hr]
      simp [ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hr.le, smul_eq_mul, mul_comm]

/-- The Green function of a disc at its centre is the positive logarithmic
kernel, with the same zero convention at the pole. -/
theorem greenFunction_ball_center_eq_posLog {R : ℝ} (hR : 0 < R) (x y : ℂ) :
    greenFunction (ball x R) x y = (2 * Real.pi)⁻¹ * log⁺ (R / ‖y - x‖) := by
  have hset : (fun z : ℂ => z + x) '' ball 0 R = ball x R := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hw
    · intro hz
      refine ⟨z - x, ?_, sub_add_cancel z x⟩
      simpa only [mem_ball, dist_eq_norm, sub_zero] using hz
  have ht := Section6.greenFunction_translate (ball 0 R) x 0 (y - x)
  rw [hset, zero_add, sub_add_cancel] at ht
  rw [ht]
  by_cases hy : y - x = 0
  · rw [hy, greenFunction_self]
    simp [posLog_zero]
  · rw [greenFunction_ball_eq_max (mem_ball_self hR) hy]
    rw [greenBall, Real.posLog_apply, max_comm 0 _,
      mul_max_of_nonneg _ _ (by positivity : 0 ≤ (2 * Real.pi)⁻¹), mul_zero]
    congr 2
    simp only [map_zero, zero_mul, sub_zero, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hR.le, zero_sub, norm_neg]
    field_simp

/-- A bounded open set inside a disc has the same uniform local Green
volume bound for every pole and every observation-ball centre. -/
theorem greenFunction_local_volume_bound {U : Set ℂ} {R r : ℝ}
    (hU : IsOpen U) (hR : 0 < R) (hsub : U ⊆ ball 0 R) (hr : 0 < r) (x c : ℂ) :
    IntegrableOn (greenFunction U x) (ball c r) ∧
    (∫ z in ball c r, greenFunction U x z) ≤
      (2 * Real.pi)⁻¹ * (Real.pi * r ^ 2 * log⁺ (2 * R / r) +
        r ^ 2 * ∫ z : ℂ, log⁺ (1 / ‖z‖)) := by
  have hUb : Bornology.IsBounded U := isBounded_ball.subset hsub
  have hpoint : ∀ z, greenFunction U x z ≤
      (2 * Real.pi)⁻¹ * log⁺ (2 * R / ‖z - x‖) := by
    intro z
    by_cases hx : x ∈ U
    · have hxR := mem_ball_zero_iff.mp (hsub hx)
      have hs : U ⊆ ball x (2 * R) := by
        intro y hy
        have hyR := mem_ball_zero_iff.mp (hsub hy)
        rw [mem_ball, dist_eq_norm]
        have hh := norm_sub_le y x
        linarith
      calc
        _ ≤ greenFunction (ball x (2 * R)) x z :=
          Section6.greenFunction_le_of_subset hs isBounded_ball x z
        _ = _ := greenFunction_ball_center_eq_posLog (by positivity) x z
    · rw [greenFunction_of_notMem_left hx]
      exact mul_nonneg (by positivity) posLog_nonneg
  have hk : Integrable (fun z : ℂ => log⁺ (2 * R / ‖z - x‖)) := by
    have h := (measurePreserving_add_right volume (-x)).integrable_comp_of_integrable
      (integrable_posLog_div_norm (by positivity : 0 < 2 * R))
    simpa only [sub_eq_add_neg, Function.comp_def] using h
  have hm := hk.const_mul ((2 * Real.pi)⁻¹)
  have hi : IntegrableOn (greenFunction U x) (ball c r) := by
    apply hm.integrableOn.mono_nonneg (measurable_greenFunction hU x).aestronglyMeasurable
      (Filter.Eventually.of_forall (greenFunction_nonneg hUb x))
    exact Filter.Eventually.of_forall hpoint
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ z in ball c r, (2 * Real.pi)⁻¹ * log⁺ (2 * R / ‖z - x‖) :=
      integral_mono_ae hi hm.integrableOn (Filter.Eventually.of_forall hpoint)
    _ = (2 * Real.pi)⁻¹ * ∫ z in ball c r, log⁺ (2 * R / ‖z - x‖) :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_posLog_div_norm_sub_ball_le (by positivity) hr x c) (by positivity)

/-- The local Green estimate in the usual `C r² (1 + |log r|)` form. -/
theorem greenFunction_local_volume_bound_logarithmic {U : Set ℂ} {R : ℝ}
    (hU : IsOpen U) (hR : 0 < R) (hsub : U ⊆ ball 0 R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 < r → ∀ x c : ℂ,
      (∫ z in ball c r, greenFunction U x z) ≤ C * r ^ 2 * (1 + |Real.log r|) := by
  let K := ∫ z : ℂ, log⁺ (1 / ‖z‖)
  let C := (2 * Real.pi)⁻¹ * (Real.pi * (1 + |Real.log (2 * R)|) + K)
  have hK : 0 ≤ K := integral_nonneg fun _ => posLog_nonneg
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro r hr x c
  have hlog : log⁺ (2 * R / r) ≤ (1 + |Real.log (2 * R)|) * (1 + |Real.log r|) := by
    rw [Real.posLog_apply, Real.log_div (by positivity : (2 * R) ≠ 0) hr.ne']
    have hh := mul_nonneg (abs_nonneg (Real.log (2 * R))) (abs_nonneg (Real.log r))
    apply max_le <;> nlinarith [le_abs_self (Real.log (2 * R)), neg_abs_le (Real.log r),
      abs_nonneg (Real.log (2 * R)), abs_nonneg (Real.log r)]
  have hbase : Real.pi * log⁺ (2 * R / r) + K ≤
      (Real.pi * (1 + |Real.log (2 * R)|) + K) * (1 + |Real.log r|) := by
    calc
      _ ≤ Real.pi * ((1 + |Real.log (2 * R)|) * (1 + |Real.log r|)) +
          K * (1 + |Real.log r|) :=
        add_le_add (mul_le_mul_of_nonneg_left hlog Real.pi_pos.le)
          (by nlinarith [mul_nonneg hK (abs_nonneg (Real.log r))])
      _ = _ := by ring
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (Real.pi * r ^ 2 * log⁺ (2 * R / r) + r ^ 2 * K) :=
      (greenFunction_local_volume_bound hU hR hsub hr x c).2
    _ = (2 * Real.pi)⁻¹ * (r ^ 2 * (Real.pi * log⁺ (2 * R / r) + K)) := by ring
    _ ≤ (2 * Real.pi)⁻¹ * (r ^ 2 *
        ((Real.pi * (1 + |Real.log (2 * R)|) + K) * (1 + |Real.log r|))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbase (sq_nonneg r)) (by positivity)
    _ = _ := by dsimp [C]; ring

/-- Every bounded open planar set has a uniform local Green volume bound. -/
theorem exists_greenFunction_local_volume_bound {U : Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ), 0 < r → ∀ x c : ℂ,
      IntegrableOn (greenFunction U x) (ball c r) ∧
      (∫ z in ball c r, greenFunction U x z) ≤ C * r ^ 2 * (1 + |Real.log r|) := by
  obtain ⟨R, hR, hsub⟩ := hUb.subset_ball_lt 0 (0 : ℂ)
  obtain ⟨C, hC, hbound⟩ := greenFunction_local_volume_bound_logarithmic hU hR hsub
  exact ⟨C, hC, fun r hr x c =>
    ⟨(greenFunction_local_volume_bound hU hR hsub hr x c).1, hbound r hr x c⟩⟩

/-- The logarithmic area modulus tends to zero at small positive radii. -/
theorem tendsto_sq_mul_one_add_abs_log :
    Tendsto (fun r : ℝ => r ^ 2 * (1 + |Real.log r|)) (𝓝[>] 0) (𝓝 0) := by
  have hsq : Tendsto (fun r : ℝ => r ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using h.pow 2
  have hlog : Tendsto (fun r : ℝ => Real.log r * r ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_ofNat] using
      (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 2))
  have hnorm := hlog.norm
  have heq : ∀ᶠ r : ℝ in 𝓝[>] 0,
      r ^ 2 * (1 + |Real.log r|) = r ^ 2 + ‖Real.log r * r ^ 2‖ := by
    filter_upwards with r
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg r)]
    ring
  apply Tendsto.congr' (heq.mono fun _ h => h.symm)
  simpa using hsq.add hnorm

/-- The logarithmic term in the explicit local bound vanishes at small radii. -/
theorem tendsto_sq_mul_posLog_div {A : ℝ} (hA : 0 < A) :
    Tendsto (fun r : ℝ => r ^ 2 * log⁺ (A / r)) (𝓝[>] 0) (𝓝 0) := by
  have hsq : Tendsto (fun r : ℝ => r ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using h.pow 2
  have hlog : Tendsto (fun r : ℝ => Real.log r * r ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_ofNat] using
      (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 2))
  have hup : Tendsto (fun r : ℝ => |Real.log A| * r ^ 2 + ‖Real.log r * r ^ 2‖)
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hsq).add hlog.norm
  apply squeeze_zero' ?_ ?_ hup
  · filter_upwards with r
    exact mul_nonneg (sq_nonneg r) posLog_nonneg
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hrpos : 0 < r := hr
    have hp : log⁺ (A / r) ≤ |Real.log A| + |Real.log r| := by
      rw [Real.posLog_apply, Real.log_div hA.ne' hrpos.ne']
      exact max_le (add_nonneg (abs_nonneg _) (abs_nonneg _))
        (by linarith [le_abs_self (Real.log A), neg_abs_le (Real.log r)])
    calc
      _ ≤ r ^ 2 * (|Real.log A| + |Real.log r|) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg r)
      _ = _ := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg r)]
        ring

/-- The bound in `greenFunction_local_volume_bound` tends to zero uniformly
in both the pole and the centre of the observation ball. -/
theorem tendsto_greenFunction_local_volume_bound {R : ℝ} (hR : 0 < R) :
    Tendsto (fun r : ℝ => (2 * Real.pi)⁻¹ *
      (Real.pi * r ^ 2 * log⁺ (2 * R / r) +
        r ^ 2 * ∫ z : ℂ, log⁺ (1 / ‖z‖))) (𝓝[>] 0) (𝓝 0) := by
  have hsq : Tendsto (fun r : ℝ => r ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using h.pow 2
  have hp := tendsto_sq_mul_posLog_div (by positivity : 0 < 2 * R)
  have hsum : Tendsto (fun r : ℝ => Real.pi * (r ^ 2 * log⁺ (2 * R / r)) +
      r ^ 2 * ∫ z : ℂ, log⁺ (1 / ‖z‖)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hp).add (hsq.mul tendsto_const_nhds)
  simpa only [mul_assoc, mul_zero] using
    (tendsto_const_nhds.mul hsum : Tendsto (fun r : ℝ => (2 * Real.pi)⁻¹ *
      (Real.pi * (r ^ 2 * log⁺ (2 * R / r)) +
        r ^ 2 * ∫ z : ℂ, log⁺ (1 / ‖z‖))) (𝓝[>] 0) (𝓝 ((2 * Real.pi)⁻¹ * 0)))


end HarmonicBalls
