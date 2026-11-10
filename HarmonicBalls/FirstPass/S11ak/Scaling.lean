import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.FirstPass.S11i.LogPotential
import HarmonicBalls.Proofs.Sec5.LaplacianScaling

/-! # Coordinate scaling for the dilation step (fp-S11ak, owner z6)

Deterministic lemmas used to transport the punctured-ball decoder from `ball 0 7` to `ball 0 1`
(`Dilation.lean`):

* curve lengths and internal metrics of a metric `c · D(k·, k·)` are those of `D` on the dilated set, times `c`;
* the mean-zero observation of the dilated pairing `φ ↦ R⁻² hC(φ(·/R))` is the rescaled observation of `hC`
  (the constant `-c₀ ∫φ` drops out on mean-zero test functions).
-/

namespace HarmonicBalls.S11ak

open MeasureTheory Set Filter
open scoped ENNReal

/-- The extension of the image of a path under a continuous map `f` is `f` composed with the extension. -/
theorem extend_map_eq {a b : ℂ} (f : ℂ → ℂ) (hf : Continuous f) (P : Path a b) :
    (P.map hf).extend = fun t => f (P.extend t) := by
  funext t
  simp [Path.extend, Set.IccExtend, Path.map_coe]

/-- Length of a curve for the rescaled metric `c · D(k·, k·)` (`curveLength`, `Defs/LQGMetric.lean`). -/
theorem curveLength_const_mul_comp_smul (D : ℂ → ℂ → ℝ) {c k : ℝ} (hc : 0 ≤ c) (p : ℝ → ℂ) (a b : ℝ) :
    curveLength (fun x y => c * D ((k : ℂ) * x) ((k : ℂ) * y)) p a b =
      ENNReal.ofReal c * curveLength D (fun t => (k : ℂ) * p t) a b := by
  unfold curveLength
  rw [ENNReal.mul_iSup]
  congr 1
  funext q
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_mul hc]

/-- Internal metric of the rescaled metric `c · D(k·, k·)` on `U`: it is `c` times the internal metric of `D` on
the image `V` of `U` under `z ↦ k z` (the change of paths is `P ↦ k · P`, a bijection). -/
theorem internalMetric_const_mul_comp_smul (D : ℂ → ℂ → ℝ) {c k : ℝ} (hc : 0 < c) (hk : k ≠ 0)
    (U V : Set ℂ) (hUV : ∀ z, z ∈ U ↔ (k : ℂ) * z ∈ V) (x y : ℂ) :
    internalMetric (fun x y => c * D ((k : ℂ) * x) ((k : ℂ) * y)) U x y =
      ENNReal.ofReal c * internalMetric D V ((k : ℂ) * x) ((k : ℂ) * y) := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hcont : Continuous fun z : ℂ => (k : ℂ) * z := continuous_const.mul continuous_id
  have hcont' : Continuous fun z : ℂ => (k : ℂ)⁻¹ * z := continuous_const.mul continuous_id
  have hlen : ∀ {a b : ℂ} (P : Path a b),
      pathLength (fun x y => c * D ((k : ℂ) * x) ((k : ℂ) * y)) P =
        ENNReal.ofReal c * pathLength D (P.map hcont) := by
    intro a b P
    unfold pathLength
    rw [curveLength_const_mul_comp_smul D hc.le, extend_map_eq _ hcont P]
  unfold internalMetric
  simp only [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top]
  apply le_antisymm
  · refine le_iInf₂ fun Q hQ => ?_
    have hx : (k : ℂ)⁻¹ * ((k : ℂ) * x) = x := inv_mul_cancel_left₀ hk0 x
    have hy : (k : ℂ)⁻¹ * ((k : ℂ) * y) = y := inv_mul_cancel_left₀ hk0 y
    let P : Path x y := (Q.map hcont').cast hx.symm hy.symm
    have hPt : ∀ t, P t = (k : ℂ)⁻¹ * Q t := fun t => by
      simp [P, Path.cast_coe, Path.map_coe]
    have hPU : ∀ t, P t ∈ U := fun t => by
      rw [hUV, hPt, mul_inv_cancel_left₀ hk0]
      exact hQ t
    have hPQ : P.map hcont = Q := by
      refine Path.ext (funext fun t => ?_)
      rw [Path.map_coe, Function.comp_apply, hPt, mul_inv_cancel_left₀ hk0]
    refine (iInf₂_le P hPU).trans (le_of_eq ?_)
    rw [hlen P, hPQ]
  · refine le_iInf₂ fun P hP => ?_
    have hPV : ∀ t, (P.map hcont) t ∈ V := by
      intro t
      rw [Path.map_coe]
      exact (hUV (P t)).mp (hP t)
    refine (iInf₂_le (P.map hcont) hPV).trans (le_of_eq ?_)
    exact (hlen P).symm

/-- Mean-zero scaling identity for the logarithmic weight: `∫ φ(y/R) log|y| dy = R² (log R ∫ φ + ∫ φ log|x|)`. -/
theorem integral_div_mul_log_norm {R : ℝ} (hR : 0 < R) (φ : ℂ → ℝ) (hc : Continuous φ)
    (hs : HasCompactSupport φ) :
    ∫ y : ℂ, φ (y / (R : ℂ)) * Real.log ‖y‖ =
      R ^ 2 * (Real.log R * (∫ x : ℂ, φ x) + ∫ x : ℂ, φ x * Real.log ‖x‖) := by
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have h1 : ∫ y : ℂ, φ (y / (R : ℂ)) * Real.log ‖y‖ =
      ∫ y : ℂ, φ (y / (R : ℂ)) * (Real.log R + Real.log ‖y / (R : ℂ)‖) := by
    refine integral_congr_ae ?_
    have hae : ∀ᵐ y : ℂ ∂volume, y ≠ 0 := by
      have : volume ({0} : Set ℂ) = 0 := measure_singleton 0
      exact compl_mem_ae_iff.mpr this
    filter_upwards [hae] with y hy
    have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    have hnR : ‖(R : ℂ)‖ = R := by simp [abs_of_pos hR]
    rw [norm_div, hnR, Real.log_div hn hR.ne']
    ring
  have hsmul : ∀ y : ℂ, y / (R : ℂ) = (R⁻¹ : ℝ) • y := by
    intro y
    rw [Complex.real_smul]
    push_cast
    rw [div_eq_inv_mul]
  have hfin : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have h3 : ∫ y : ℂ, φ (y / (R : ℂ)) * (Real.log R + Real.log ‖y / (R : ℂ)‖) =
      R ^ 2 * ∫ x : ℂ, φ x * (Real.log R + Real.log ‖x‖) := by
    have key := MeasureTheory.Measure.integral_comp_smul (volume : Measure ℂ)
      (fun x : ℂ => φ x * (Real.log R + Real.log ‖x‖)) R⁻¹
    rw [hfin] at key
    have habs : |((R⁻¹ : ℝ) ^ 2)⁻¹| = R ^ 2 := by
      rw [inv_pow, inv_inv, abs_of_pos (by positivity)]
    rw [habs, smul_eq_mul] at key
    simp only [hsmul]
    exact key
  have hint1 : Integrable (fun x : ℂ => φ x) := hc.integrable_of_hasCompactSupport hs
  have hint2 : Integrable (fun x : ℂ => φ x * Real.log ‖x‖) := by
    have hloc : LocallyIntegrable (fun x : ℂ => φ x * Real.log ‖x‖) volume :=
      locallyIntegrable_log_norm_complex.continuous_mul hc
    have hIO : IntegrableOn (fun x : ℂ => φ x * Real.log ‖x‖) (tsupport φ) volume :=
      hloc.integrableOn_isCompact hs.isCompact
    exact (integrableOn_iff_integrable_of_support_subset
      (fun x hx => subset_tsupport φ (left_ne_zero_of_mul hx))).mp hIO
  have h4 : ∫ x : ℂ, φ x * (Real.log R + Real.log ‖x‖) =
      Real.log R * (∫ x : ℂ, φ x) + ∫ x : ℂ, φ x * Real.log ‖x‖ := by
    have hfun : (fun x : ℂ => φ x * (Real.log R + Real.log ‖x‖)) =
        fun x : ℂ => Real.log R * φ x + φ x * Real.log ‖x‖ := by
      funext x
      ring
    rw [hfun, integral_add (hint1.const_mul _) hint2, integral_const_mul]
  rw [h1, h3, h4]

/-- Division by a positive real is a real dilation: `y / R = R⁻¹ • y`. -/
theorem div_ofReal_eq_smul {R : ℝ} (y : ℂ) : y / (R : ℂ) = (R⁻¹ : ℝ) • y := by
  rw [Complex.real_smul]
  push_cast
  rw [div_eq_inv_mul]

/-- Real dilation of a test function: `y ↦ φ (y / R)` is a test function on `ball c r` when `φ` is one on
`ball (c / R) (r / R)`. -/
theorem isTestFunction_div_ball {c : ℂ} {r R : ℝ} (hR : 0 < R) {φ : ℂ → ℝ}
    (hφ : IsTestFunction (Metric.ball (c / (R : ℂ)) (r / R)) φ) :
    IsTestFunction (Metric.ball c r) (fun y => φ (y / (R : ℂ))) := by
  have h := hφ.comp_real_smul (k := R⁻¹) (inv_ne_zero hR.ne')
  have hpre : (fun z : ℂ => (R⁻¹ : ℝ) • z) ⁻¹' Metric.ball (c / (R : ℂ)) (r / R) = Metric.ball c r := by
    ext z
    simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm, Complex.real_smul]
    have hz : ((R⁻¹ : ℝ) : ℂ) * z - c / (R : ℂ) = ((R⁻¹ : ℝ) : ℂ) * (z - c) := by
      push_cast
      ring
    rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hR, div_eq_inv_mul]
    exact mul_lt_mul_iff_right₀ (inv_pos.mpr hR)
  have hfun : (fun z : ℂ => φ ((R⁻¹ : ℝ) • z)) = fun y => φ (y / (R : ℂ)) := by
    funext y
    rw [div_ofReal_eq_smul]
  rw [hpre, hfun] at h
  exact h

/-- Dilation keeps mean-zero test functions mean-zero: `∫ φ(y/R) dy = R² ∫ φ`. -/
theorem integral_div_ofReal_eq_zero {R : ℝ} (hR : 0 < R) (φ : ℂ → ℝ) (h : ∫ x : ℂ, φ x = 0) :
    ∫ y : ℂ, φ (y / (R : ℂ)) = 0 := by
  have key := MeasureTheory.Measure.integral_comp_smul (volume : Measure ℂ) φ R⁻¹
  rw [Complex.finrank_real_complex] at key
  have habs : |((R⁻¹ : ℝ) ^ 2)⁻¹| = R ^ 2 := by
    rw [inv_pow, inv_inv, abs_of_pos (by positivity)]
  rw [habs, h, smul_zero] at key
  simp only [div_ofReal_eq_smul]
  exact key

/-- Transport of the mean-zero observation under the real dilation `φ ↦ φ(·/R)`: the pairing
`φ ↦ R⁻² hC(φ(·/R)) - c₀ ∫ φ` (the dilated whole-plane field, with its normalising constant) and `φ ↦ hC(φ(·/R))`
with the insertion `-α log|·|` agree on mean-zero test functions, up to the factor `R⁻²`. -/
theorem fieldPairing_dilate (hC : (ℂ → ℝ) → ℝ) {R : ℝ} (hR : 0 < R) (α c₀ : ℝ) (φ : ℂ → ℝ)
    (hc : Continuous φ) (hs : HasCompactSupport φ) (hmean : ∫ x, φ x = 0) :
    fieldPairing α (fun ψ => (R ^ 2)⁻¹ * hC (fun y => ψ (y / (R : ℂ))) - c₀ * ∫ x, ψ x) φ =
      (R ^ 2)⁻¹ * fieldPairing α hC (fun y => φ (y / (R : ℂ))) := by
  unfold fieldPairing
  dsimp only
  rw [integral_div_mul_log_norm hR φ hc hs, hmean]
  have hR2 : R ^ 2 ≠ 0 := by positivity
  field_simp
  ring

end HarmonicBalls.S11ak
