import HarmonicBalls.FirstPass.S11s.Scaling
import HarmonicBalls.FirstPass.S11q.Metric

/-!
# B1 transfer of the LQG measure and metric under `h ↦ h̃ = h(·/2 ·) - h_{1/2}(0)`

Ruling section 3, eqs. (9)-(11), with `r = 1/2`:

* `isLQGLimit_dilate_half`: the LQG limit of the dilated circle averages `dilatedCircleAverage H (1/2)` is
  `e^{-γ c} · m.map (· / (1/2))`, `c = dilationConstant γ H (1/2)` (Duplantier-Sheffield scaling of the measure).
* `ae_isLQGMeasureOfField_affinePullback`: the LQG measure of the affine pullback model is the constant times the
  pushforward of `μ` (a.s., for every whole-plane GFF model with an LQG measure).
* `ae_isLQGMetricOfField_affinePullback`: the LQG metric of the affine pullback model is the constant times the
  dilated metric (a.s.), by the Weyl-scaling identity `ae_weylScaling_affinePullback_background` (S11q/Metric.lean).

Only the scalar factors are tracked; their values are not needed for the covariance statement.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Two families of circle averages that agree at every positive radius have the same LQG limit (the LQG
approximations `lqgApprox` are evaluated only at the dyadic scales `dyadicScale k > 0`). -/
theorem isLQGLimit_congr_pos {γ : ℝ} {H H' : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (hH : ∀ ε : ℝ, 0 < ε → ∀ z : ℂ, H' ε z = H ε z) (hm : IsLQGLimit γ H m) : IsLQGLimit γ H' m := by
  have hk : ∀ k : ℕ, lqgApprox γ H' (dyadicScale k) = lqgApprox γ H (dyadicScale k) := by
    intro k
    simp only [lqgApprox, hH _ (dyadicScale_pos k)]
  refine ⟨hm.isLocallyFiniteMeasure, fun f hf hfs => ?_⟩
  simp only [hk]
  exact hm.tendsto_integral f hf hfs

/-- The dyadic index shift: `(1/2) · 2^{-k} = 2^{-(k+1)}`. -/
theorem half_mul_dyadicScale (k : ℕ) : (1 / 2 : ℝ) * dyadicScale k = dyadicScale (k + 1) := by
  unfold dyadicScale
  rw [pow_succ']
  ring

/-- **LQG limit under the dilation by `1/2`.** If `m` is the LQG limit of the circle averages `H`, then the
dilated circle averages `dilatedCircleAverage H (1/2)` have LQG limit `e^{-γ c} · m.map (· / (1/2))`,
`c = dilationConstant γ H (1/2)`. The proof is `integral_lqgApprox_dilate` (FirstPass/S11q.lean) with the
dyadic shift `(1/2) · dyadicScale k = dyadicScale (k+1)`. -/
theorem isLQGLimit_dilate_half {γ : ℝ} {H : ℝ → ℂ → ℝ} {m : Measure ℂ} (hm : IsLQGLimit γ H m) (hγ : 0 < γ)
    (hmeas : ∀ r : ℝ, 0 < r → Measurable (H r)) :
    IsLQGLimit γ (dilatedCircleAverage H (1 / 2))
      (ENNReal.ofReal (Real.exp (-(γ * dilationConstant γ H (1 / 2))))
        • m.map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ))) := by
  have := hm.isLocallyFiniteMeasure
  have hR : (0 : ℝ) < 1 / 2 := by norm_num
  have hRC : ((1 / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  let hom : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero (((1 / 2 : ℝ) : ℂ))⁻¹ (inv_ne_zero hRC)
  have hw : ∀ w : ℂ, hom w = w / ((1 / 2 : ℝ) : ℂ) := by
    intro w
    show (((1 / 2 : ℝ) : ℂ))⁻¹ • w = w / ((1 / 2 : ℝ) : ℂ)
    rw [smul_eq_mul]
    exact (div_eq_inv_mul _ _).symm
  have hfun : (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) = ⇑hom := by
    funext w
    exact (hw w).symm
  have hdiv : Measurable (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) := by fun_prop
  have hfin : IsFiniteMeasureOnCompacts (m.map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ))) := by
    rw [hfun]
    exact MeasureTheory.Measure.IsFiniteMeasureOnCompacts.map m hom
  have hfin' : IsFiniteMeasureOnCompacts (ENNReal.ofReal (Real.exp (-(γ * dilationConstant γ H (1 / 2))))
      • m.map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ))) :=
    IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top
  have := hfin'
  refine ⟨inferInstance, fun f hf hfs => ?_⟩
  have hcont : Continuous (fun w : ℂ => f (w / ((1 / 2 : ℝ) : ℂ))) := hf.comp (by fun_prop)
  have hcs : HasCompactSupport (fun w : ℂ => f (w / ((1 / 2 : ℝ) : ℂ))) := by
    have h := hfs.comp_homeomorph hom
    have e : (f ∘ ⇑hom) = fun w : ℂ => f (w / ((1 / 2 : ℝ) : ℂ)) := by
      funext w
      simp only [Function.comp_apply, hw]
    rw [e] at h
    exact h
  have key : ∀ k : ℕ, ∫ z, f z ∂(lqgApprox γ (dilatedCircleAverage H (1 / 2)) (dyadicScale k))
      = Real.exp (-(γ * dilationConstant γ H (1 / 2)))
        * ∫ w, f (w / ((1 / 2 : ℝ) : ℂ)) ∂(lqgApprox γ H (dyadicScale (k + 1))) := by
    intro k
    rw [integral_lqgApprox_dilate H hγ hR (dyadicScale_pos k)
      (hmeas _ (mul_pos hR (dyadicScale_pos k))) f, half_mul_dyadicScale k]
  have ht := ((hm.tendsto_integral _ hcont hcs).comp (tendsto_add_atTop_nat 1)).const_mul
    (Real.exp (-(γ * dilationConstant γ H (1 / 2))))
  simp only [key]
  rw [integral_smul_measure, integral_map hdiv.aemeasurable hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  exact ht

/-- Continuity of the field circle averages in the centre, at a positive radius, from the joint continuity
of `(r, z) ↦ h_r(z)` on `(0, ∞) × ℂ` (`IsWholePlaneGFF.ae_continuousOn_circle`). -/
theorem measurable_fieldCircleAverage {α : ℝ} {h : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2) (Ioi 0 ×ˢ univ)) {ρ : ℝ} (hρ : 0 < ρ) :
    Measurable (fieldCircleAverage α h ρ) := by
  have h1 : Continuous (fun z : ℂ => h ρ z) :=
    hcont.comp_continuous (f := fun z : ℂ => (ρ, z)) (by fun_prop) (fun z => ⟨hρ, mem_univ z⟩)
  have h2 : (fun z : ℂ => Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z ρ)
      = fun z : ℂ => Real.log ρ + Real.posLog (ρ⁻¹ * ‖z‖) := by
    funext z
    have := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := (0 : ℂ)) (c := z) hρ.ne'
    simpa only [sub_zero] using this
  have h3 : Continuous (fun z : ℂ => Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z ρ) := by
    rw [h2]
    fun_prop
  unfold fieldCircleAverage
  exact (h1.sub (continuous_const.mul h3)).measurable

/-- **Measure half of the B1 transfer.** For a whole-plane GFF model with LQG measure `μ` of
`h = h^ℂ - α log|·|`, the pulled-back field `h̃ = h^ℂ(·/2 ·) - h^ℂ_{1/2}(0)` (the pairing of
`WholePlaneGFFAffineInvariance` with `a = 1/2`, `b = 0`) has LQG measure `e^{-γ c} · μ.map (· / (1/2))`
almost surely, `c = h_{1/2}(0) - α log(1/2)` plus `Q log(1/2)`. -/
theorem ae_isLQGMeasureOfField_affinePullback {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {γ α : ℝ}
    (hγ : 0 < γ) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    IsLQGMeasureOfField P γ α
      (fun ω ρ z => hcirc ω ((1 / 2 : ℝ) * ρ) (((1 / 2 : ℝ) : ℂ) * z) - hcirc ω (1 / 2) 0)
      (fun ω => ENNReal.ofReal (Real.exp (-(γ * dilationConstant γ (fieldCircleAverage α (hcirc ω)) (1 / 2))))
        • (μ ω).map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ))) := by
  unfold IsLQGMeasureOfField IsLQGMeasure at hμ ⊢
  filter_upwards [hμ, hG.ae_continuousOn_circle] with ω hω hcont
  refine isLQGLimit_congr_pos (fun ε hε z => ?_)
    (isLQGLimit_dilate_half hω hγ (fun r hr => measurable_fieldCircleAverage hcont hr))
  exact fieldCircleAverage_affinePullback α (hcirc ω) (by norm_num : (0 : ℝ) < 1 / 2) hε.ne' z

/-- **Metric half of the B1 transfer.** For a whole-plane GFF model (`Ω : Type`, as required by
`ae_weylScaling_affinePullback_background`) with LQG metric `D` of `h = h^ℂ - α log|·|`, the function
`D̃ ω u v = e^{-ξ c_ω} D ω (u/2) (v/2)`, with `c_ω = h^ℂ_{1/2}(0) - α log(1/2) + Q log(1/2)`, is an LQG metric of the
pulled-back pairing `normDilatePairing (hC ω) (h^ℂ_{1/2}(0)) (1/2)` (ruling eqs. (10)-(11)). -/
theorem ae_isLQGMetricOfField_affinePullback {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ α hC D) :
    IsLQGMetricOfField P γ ξ α
      (fun ω => normDilatePairing (hC ω) (hcirc ω (1 / 2) 0) (1 / 2))
      (fun ω u v => Real.exp (-(ξ * (fieldCircleAverage α (hcirc ω) (1 / 2) 0 + lqgQ γ * Real.log (1 / 2))))
        * D ω (((1 / 2 : ℝ) : ℂ) * u) (((1 / 2 : ℝ) : ℂ) * v)) := by
  obtain ⟨𝔇, h𝔇, hDae⟩ := hD
  have hc : Measurable (fun ω => hcirc ω (1 / 2) 0 + lqgQ γ * Real.log (1 / 2)) :=
    (hG.measurable_circle (1 / 2) 0 (by norm_num)).add_const _
  refine ⟨𝔇, h𝔇, ?_⟩
  filter_upwards [hDae, ae_weylScaling_affinePullback_background hG 𝔇 h𝔇 (R := 1 / 2) (by norm_num)
    (fun ω => hcirc ω (1 / 2) 0 + lqgQ γ * Real.log (1 / 2)) hc α] with ω hω hW
  have hP : addFunPairing (affinePullbackPairing (hC ω) (1 / 2) 0)
      (fun _ => lqgQ γ * Real.log (1 / 2) - (hcirc ω (1 / 2) 0 + lqgQ γ * Real.log (1 / 2)))
      = normDilatePairing (hC ω) (hcirc ω (1 / 2) 0) (1 / 2) := by
    rw [normDilatePairing_eq_addFunPairing]
    congr 1
    funext x
    ring
  have hexp : -(ξ * ((hcirc ω (1 / 2) 0 + lqgQ γ * Real.log (1 / 2)) - α * Real.log (1 / 2)))
      = -(ξ * (fieldCircleAverage α (hcirc ω) (1 / 2) 0 + lqgQ γ * Real.log (1 / 2))) := by
    have h0 : fieldCircleAverage α (hcirc ω) (1 / 2) 0 = hcirc ω (1 / 2) 0 - α * Real.log (1 / 2) := by
      unfold fieldCircleAverage
      rw [circleAverage_log_norm_zero (by norm_num)]
    rw [h0]
    ring
  rw [hP] at hW
  intro u v
  refine ⟨mul_nonneg (Real.exp_nonneg _) (hω (((1 / 2 : ℝ) : ℂ) * u) (((1 / 2 : ℝ) : ℂ) * v)).1, ?_⟩
  rw [hW u v, ENNReal.ofReal_mul (Real.exp_nonneg _),
    (hω (((1 / 2 : ℝ) : ℂ) * u) (((1 / 2 : ℝ) : ℂ) * v)).2, hexp]

end HarmonicBalls
