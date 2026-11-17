import HarmonicBalls.Proofs.Potential.GreenGeneralHolder
import HarmonicBalls.Proofs.Potential.LQGSingularGreenPotentialHolder

/-! # Green potentials on smooth bounded domains -/

noncomputable section

namespace HarmonicBalls
namespace GreenGeneral
open MeasureTheory Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology
open Filter

theorem negMoment_restrict_of_upper {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {R r₀ βplus : ℝ}
    (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < βplus)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, μ (ball z r) ≤ ENNReal.ofReal (r ^ βplus)) {O : Set ℂ} (hO : O ⊆ ball (0 : ℂ) R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ closedBall (0 : ℂ) R,
      ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-greenPotentialHolderExponent βplus)) ∂(μ.restrict O) ≤
        ENNReal.ofReal K ∧ μ.restrict O {x} = 0 := by
  have hfin : μ (ball (0 : ℂ) R) ≠ ⊤ := measure_ball_lt_top.ne
  set m := (μ (ball (0 : ℂ) R)).toReal with hm_def
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  have hα := greenPotentialHolderExponent_pos hβ
  have hball := fun x (hx : x ∈ closedBall (0 : ℂ) R) r (hr : 0 < r) =>
    restrict_ball_closedBall_le hR hr₀ hβ hup hfin hx hr
  have hν : μ.restrict (ball 0 R) univ ≤ ENNReal.ofReal m := by
    rw [Measure.restrict_apply_univ, hm_def, ENNReal.ofReal_toReal hfin]
  have hle : μ.restrict O ≤ μ.restrict (ball 0 R) := Measure.restrict_mono hO le_rfl
  refine ⟨greenPotentialRieszBound βplus r₀ m, greenPotentialRieszBound_nonneg hβ hr₀ hm,
    fun x hx => ⟨?_, ?_⟩⟩
  · exact (lintegral_mono' hle le_rfl).trans (lintegral_norm_sub_rpow_neg_le hα
      (greenPotentialHolderExponent_lt hβ) hm (volumeGrowthAllScalesConstant_nonneg hr₀ hm) hν (hball x hx))
  · exact nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 hle {x}).trans
      (measure_singleton_eq_zero_of_le_rpow hβ (hball x hx)).le)



theorem newtonPotential_holder_of_upper {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    {R r₀ βplus : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < βplus)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, μ (ball z r) ≤ ENNReal.ofReal (r ^ βplus)) {O : Set ℂ}
    (hOm : MeasurableSet O) (hO : O ⊆ ball (0 : ℂ) R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℂ → ℝ) (M : ℝ), AEStronglyMeasurable f (μ.restrict O) → 0 ≤ M →
      (∀ᵐ y ∂μ.restrict O, |f y| ≤ M) →
      (∀ x ∈ closedBall (0 : ℂ) R, Integrable (fun y => newtonKernel x y * f y) (μ.restrict O)) ∧
      ∀ x ∈ closedBall (0 : ℂ) R, ∀ x' ∈ closedBall (0 : ℂ) R,
        |∫ y, newtonKernel x y * f y ∂(μ.restrict O) - ∫ y, newtonKernel x' y * f y ∂(μ.restrict O)| ≤
          C * M * ‖x - x'‖ ^ greenPotentialHolderExponent βplus := by
  obtain ⟨K, hK0, hK⟩ := negMoment_restrict_of_upper hR hr₀ hβ hup hO
  have := isFiniteMeasure_restrict_of_subset_ball (μ := μ) hO
  have hα := greenPotentialHolderExponent_pos hβ
  have hsupp : ∀ᵐ y ∂μ.restrict O, ‖y‖ ≤ R :=
    (ae_restrict_iff' hOm).2 (Filter.Eventually.of_forall fun y hy => (mem_ball_zero_iff.1 (hO hy)).le)
  refine ⟨(Real.pi * greenPotentialHolderExponent βplus)⁻¹ * K,
    mul_nonneg (inv_nonneg.2 (mul_nonneg Real.pi_pos.le hα.le)) hK0, fun f M hf hM hfM => ?_⟩
  exact newtonPotential_integrable_and_sub_le hα (greenPotentialHolderExponent_le_one βplus) hK0 hsupp
    (fun x hx => (hK x hx).1) (fun x hx => (hK x hx).2) hf hM hfM



theorem integrableOn_greenFunction_mul_of_upper {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    {R r₀ βplus : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < βplus)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, μ (ball z r) ≤ ENNReal.ofReal (r ^ βplus)) {O : Set ℂ}
    (hOo : IsOpen O) (hO : O ⊆ ball (0 : ℂ) R) {f : ℂ → ℝ} {M : ℝ}
    (hf : AEStronglyMeasurable f (μ.restrict O)) (hfM : ∀ᵐ y ∂μ.restrict O, |f y| ≤ M) :
    ∀ x ∈ closedBall (0 : ℂ) R, IntegrableOn (fun y => greenFunction O x y * f y) O μ := by
  intro x hx
  obtain ⟨K, hK0, hK⟩ := negMoment_restrict_of_upper hR hr₀ hβ hup hO
  set α := greenPotentialHolderExponent βplus with hα_def
  have hα : 0 < α := greenPotentialHolderExponent_pos hβ
  have hint := (integrable_norm_sub_rpow_neg hK0 (hK x hx).1).1
  have hne : ∀ᵐ y ∂μ.restrict O, y ≠ x := ae_iff.2 (by simpa using (hK x hx).2)
  have hOb : Bornology.IsBounded O := isBounded_ball.subset hO
  have hπ : 0 ≤ (2 * Real.pi)⁻¹ := inv_nonneg.2 (by positivity)
  set c := (2 * Real.pi)⁻¹ * (α⁻¹ * (2 * R) ^ α) with hc_def
  have hc : 0 ≤ c := mul_nonneg hπ (mul_nonneg (inv_nonneg.2 hα.le) (Real.rpow_nonneg (by positivity) _))
  have hdom : Integrable (fun y => |M| * (c * ‖x - y‖ ^ (-α))) (μ.restrict O) :=
    (hint.const_mul _).const_mul _
  refine hdom.mono' ((measurable_greenFunction hOo x).aestronglyMeasurable.mul hf) ?_
  filter_upwards [hne, hfM] with y hyx hy
  have hpos : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
  have hG0 := greenFunction_nonneg hOb x y
  have hG : greenFunction O x y ≤ c * ‖x - y‖ ^ (-α) := by
    refine (greenFunction_le_posLog_div_norm hR hO x y).trans ?_
    rw [hc_def, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hπ
    refine (posLog_le_inv_mul_rpow (by positivity) hα).trans (le_of_eq ?_)
    rw [Real.div_rpow (by positivity) hpos.le, Real.rpow_neg (norm_nonneg _), norm_sub_rev, div_eq_mul_inv]
    ring
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hG0, mul_comm]
  exact mul_le_mul (hy.trans (le_abs_self M)) hG hG0 (abs_nonneg M)



theorem continuousOn_greenPotential_of_upper {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    {R r₀ βplus : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < βplus)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, μ (ball z r) ≤ ENNReal.ofReal (r ^ βplus)) {O : Set ℂ}
    (hO : IsSmoothBoundedOpen O) (hOR : O ⊆ ball (0 : ℂ) R) {f : ℂ → ℝ} {M : ℝ}
    (hf : AEStronglyMeasurable f (μ.restrict O)) (hfM : ∀ᵐ y ∂μ.restrict O, |f y| ≤ M) :
    ContinuousOn (fun x => ∫ y in O, greenFunction O x y * f y ∂μ) (closure O) := by
  intro x₀ hx₀
  have hOo := isOpen_of_isSmoothBoundedOpen hO
  obtain ⟨K, hK0, hK⟩ := negMoment_restrict_of_upper hR hr₀ hβ hup hOR
  have := isFiniteMeasure_restrict_of_subset_ball (μ := μ) hOR
  set α := greenPotentialHolderExponent βplus with hα_def
  have hα : 0 < α := greenPotentialHolderExponent_pos hβ
  set c := (2 * Real.pi)⁻¹ * ((α / 2)⁻¹ * (2 * R) ^ (α / 2)) with hc_def
  have hcl : closure O ⊆ closedBall (0 : ℂ) R :=
    (closure_mono hOR).trans closure_ball_subset_closedBall
  have hsq : ∀ x ∈ closure O, AEStronglyMeasurable (greenFunction O x) (μ.restrict O) ∧
      Integrable (fun y => greenFunction O x y ^ 2) (μ.restrict O) ∧
      ∫ y, greenFunction O x y ^ 2 ∂μ.restrict O ≤ c ^ 2 * K := by
    intro x hx
    have hint := integrable_norm_sub_rpow_neg hK0 (hK x (hcl hx)).1
    have hne : ∀ᵐ y ∂μ.restrict O, y ≠ x := ae_iff.2 (by simpa using (hK x (hcl hx)).2)
    have hpt : ∀ᵐ y ∂μ.restrict O, ‖greenFunction O x y ^ 2‖ ≤ c ^ 2 * ‖x - y‖ ^ (-α) := by
      filter_upwards [hne] with y hyx
      have hG0 := greenFunction_nonneg (isBounded_ball.subset hOR) x y
      have hG := greenFunction_le_mul_rpow_neg hR hOR (half_pos hα) hyx
      rw [← hc_def] at hG
      have hpow : (‖x - y‖ ^ (-(α / 2))) ^ 2 = ‖x - y‖ ^ (-α) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
        norm_num
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← hpow, ← mul_pow]
      exact pow_le_pow_left₀ hG0 hG 2
    have hmeas := (measurable_greenFunction hOo x).aestronglyMeasurable (μ := μ.restrict O)
    have hI : Integrable (fun y => greenFunction O x y ^ 2) (μ.restrict O) :=
      (hint.1.const_mul _).mono' (hmeas.pow 2) hpt
    refine ⟨hmeas, hI, ?_⟩
    calc ∫ y, greenFunction O x y ^ 2 ∂μ.restrict O ≤ ∫ y, c ^ 2 * ‖x - y‖ ^ (-α) ∂μ.restrict O :=
          integral_mono_ae hI (hint.1.const_mul _)
            (hpt.mono fun y hy => (le_abs_self _).trans (by rwa [← Real.norm_eq_abs]))
      _ = c ^ 2 * ∫ y, ‖x - y‖ ^ (-α) ∂μ.restrict O := integral_const_mul _ _
      _ ≤ c ^ 2 * K := mul_le_mul_of_nonneg_left hint.2 (sq_nonneg _)
  have hlim : ∀ᵐ y ∂μ.restrict O, Filter.Tendsto (fun x => greenFunction O x y)
      (nhdsWithin x₀ (closure O)) (nhds (greenFunction O x₀ y)) := by
    have hne : ∀ᵐ y ∂μ.restrict O, y ≠ x₀ := ae_iff.2 (by simpa using (hK x₀ (hcl hx₀)).2)
    filter_upwards [hne, ae_restrict_mem hOo.measurableSet] with y hyx hyO
    exact tendsto_greenFunction_nhdsWithin_closure hO hx₀ hyO hyx
  exact tendsto_integral_mul_of_sq_integral_le (abs_nonneg M)
    (eventually_nhdsWithin_of_forall hsq) (hsq x₀ hx₀).1 (hsq x₀ hx₀).2.1 (hsq x₀ hx₀).2.2 hlim hf
    (hfM.mono fun y hy => hy.trans (le_abs_self M))



theorem harmonicOnNhd_newtonPotential_sub_greenPotential_of_upper {μ : Measure ℂ}
    [IsLocallyFiniteMeasure μ] {R r₀ βplus : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < βplus)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, μ (ball z r) ≤ ENNReal.ofReal (r ^ βplus))
    {O : Set ℂ} (hO : IsSmoothBoundedOpen O) (hOR : O ⊆ ball (0 : ℂ) R) {f : ℂ → ℝ} {M : ℝ}
    (hf : AEStronglyMeasurable f (μ.restrict O)) (hfM : ∀ᵐ y ∂μ.restrict O, |f y| ≤ M) :
    HarmonicOnNhd (fun x => ∫ y in O, newtonKernel x y * f y ∂μ -
      ∫ y in O, greenFunction O x y * f y ∂μ) O := by
  have hOo := isOpen_of_isSmoothBoundedOpen hO
  have hOb : Bornology.IsBounded O := hO.1
  obtain ⟨K, hK0, hK⟩ := negMoment_restrict_of_upper hR hr₀ hβ hup hOR
  have := isFiniteMeasure_restrict_of_subset_ball (μ := μ) hOR
  set α := greenPotentialHolderExponent βplus with hα_def
  have hα : 0 < α := greenPotentialHolderExponent_pos hβ
  have hcl : closure O ⊆ closedBall (0 : ℂ) R :=
    (closure_mono hOR).trans closure_ball_subset_closedBall
  have hOcl : O ⊆ closedBall (0 : ℂ) R := subset_closure.trans hcl
  have hfM' : ∀ᵐ y ∂μ.restrict O, |f y| ≤ |M| := hfM.mono fun y hy => hy.trans (le_abs_self M)
  obtain ⟨C, -, hVC⟩ := newtonPotential_holder_of_upper hR hr₀ hβ hup hOo.measurableSet hOR
  obtain ⟨hVint, hVhol⟩ := hVC f |M| hf (abs_nonneg M) hfM'
  have hGint := integrableOn_greenFunction_mul_of_upper hR hr₀ hβ hup hOo hOR hf hfM
  have hW : ∀ ξ ∈ closedBall (0 : ℂ) R, (∫ y in O, newtonKernel ξ y * f y ∂μ -
      ∫ y in O, greenFunction O ξ y * f y ∂μ) =
        ∫ y in O, (newtonKernel ξ y - greenFunction O ξ y) * f y ∂μ := by
    intro ξ hξ
    rw [← integral_sub (hVint ξ hξ) (hGint ξ hξ)]
    congr 1
    funext y
    ring
  have hVcont : ContinuousOn (fun x => ∫ y in O, newtonKernel x y * f y ∂μ) (closedBall (0 : ℂ) R) := by
    intro x₀ hx₀
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (g := fun x => C * |M| * ‖x - x₀‖ ^ α) (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (eventually_nhdsWithin_of_forall fun x hx => ?_) ?_
    · rw [Real.norm_eq_abs]
      exact hVhol x hx x₀ hx₀
    · have h : Filter.Tendsto (fun x => C * |M| * ‖x - x₀‖ ^ α) (nhdsWithin x₀ (closedBall (0 : ℂ) R))
          (nhds (C * |M| * ‖x₀ - x₀‖ ^ α)) :=
        (((continuous_id.sub continuous_const).norm.rpow_const fun _ => Or.inr hα.le).tendsto x₀
          |>.const_mul _).mono_left nhdsWithin_le_nhds
      simpa [Real.zero_rpow hα.ne'] using h
  have hcont : ContinuousOn (fun x => ∫ y in O, newtonKernel x y * f y ∂μ -
      ∫ y in O, greenFunction O x y * f y ∂μ) O :=
    (hVcont.mono hOcl).sub
      ((continuousOn_greenPotential_of_upper hR hr₀ hβ hup hO hOR hf hfM).mono subset_closure)
  refine harmonicOnNhd_of_circleAverage_eq hOo hcont fun x hx r hr hxr => ?_
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hpi' : (2 * Real.pi) ≠ 0 := by positivity
  have hcm : ∀ θ, circleMap x r θ ∈ O := fun θ =>
    hxr (sphere_subset_closedBall (circleMap_mem_sphere x hr.le θ))
  set A := (2 * Real.pi)⁻¹ * α⁻¹ * (2 * R) ^ α with hA_def
  set B := (2 * Real.pi)⁻¹ * α⁻¹ with hB_def
  set c := (2 * Real.pi)⁻¹ * (α⁻¹ * (2 * R) ^ α) with hc_def
  have hA : 0 ≤ A := by positivity
  have hBc : 0 ≤ B + c := by positivity
  have hmeas1 : Measurable fun p : ℝ × ℂ => (circleMap x r p.1, p.2) :=
    ((continuous_circleMap x r).measurable.comp measurable_fst).prodMk measurable_snd
  have hNm : Measurable fun p : ℂ × ℂ => newtonKernel p.1 p.2 := by
    unfold newtonKernel
    fun_prop
  have hDm : Measurable fun p : ℝ × ℂ =>
      newtonKernel (circleMap x r p.1) p.2 - greenFunction O (circleMap x r p.1) p.2 :=
    (hNm.comp hmeas1).sub ((measurable_greenFunction_uncurry hOo).comp hmeas1)
  have htm : Measurable fun p : ℝ × ℂ => ‖circleMap x r p.1 - p.2‖ ^ (-α) :=
    ((((continuous_circleMap x r).measurable.comp measurable_fst).sub measurable_snd).norm).pow_const _
  have hmom : ∀ θ, Integrable (fun y => ‖circleMap x r θ - y‖ ^ (-α)) (μ.restrict O) ∧
      ∫ y, ‖circleMap x r θ - y‖ ^ (-α) ∂μ.restrict O ≤ K := fun θ =>
    integrable_norm_sub_rpow_neg hK0 (hK _ (hOcl (hcm θ))).1
  have htint : Integrable (fun p : ℝ × ℂ => ‖circleMap x r p.1 - p.2‖ ^ (-α))
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod (μ.restrict O)) := by
    refine (integrable_prod_iff htm.aestronglyMeasurable).2 ⟨ae_of_all _ fun θ => (hmom θ).1, ?_⟩
    refine (integrable_const K).mono' htm.aestronglyMeasurable.norm.integral_prod_right'
      (ae_of_all _ fun θ => ?_)
    have hnn : ∀ y : ℂ, ‖‖circleMap x r θ - y‖ ^ (-α)‖ = ‖circleMap x r θ - y‖ ^ (-α) := fun y =>
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
    simp only [hnn]
    rw [Real.norm_of_nonneg (integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg _) _)]
    exact (hmom θ).2
  have hFint : Integrable (Function.uncurry fun θ y =>
      (newtonKernel (circleMap x r θ) y - greenFunction O (circleMap x r θ) y) * f y)
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod (μ.restrict O)) := by
    refine ((htint.const_mul (|M| * (B + c))).add (integrable_const (|M| * A))).mono'
      (hDm.aestronglyMeasurable.mul
      (hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)) ?_
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hfM',
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hOo.measurableSet)] with p hp hpO
    have hb := abs_newtonKernel_sub_greenFunction_le hR hOR hα
      (mem_closedBall_zero_iff.1 (hOcl (hcm p.1))) (mem_ball_zero_iff.1 (hOR hpO)).le
    rw [← hA_def, ← hB_def, ← hc_def] at hb
    rw [Real.norm_eq_abs]
    change |(newtonKernel (circleMap x r p.1) p.2 - greenFunction O (circleMap x r p.1) p.2) * f p.2| ≤ _
    rw [abs_mul]
    calc |newtonKernel (circleMap x r p.1) p.2 - greenFunction O (circleMap x r p.1) p.2| * |f p.2|
        ≤ (A + B * ‖circleMap x r p.1 - p.2‖ ^ (-α) + c * ‖circleMap x r p.1 - p.2‖ ^ (-α)) * |M| :=
          mul_le_mul hb hp (abs_nonneg _) (by positivity)
      _ = |M| * (B + c) * ‖circleMap x r p.1 - p.2‖ ^ (-α) + |M| * A := by ring
  have hinner : ∀ᵐ y ∂μ.restrict O, ∫ θ in Ioc 0 (2 * Real.pi),
      (newtonKernel (circleMap x r θ) y - greenFunction O (circleMap x r θ) y) * f y =
        2 * Real.pi * ((newtonKernel x y - greenFunction O x y) * f y) := by
    have hne : ∀ᵐ y ∂μ.restrict O, y ≠ x := ae_iff.2 (by simpa using (hK x (hOcl hx)).2)
    filter_upwards [hne, ae_restrict_mem hOo.measurableSet] with y hyx hyO
    have hh := harmonicOnNhd_greatestHarmonicMinorant_newtonKernel hOo hOb hyO
    have hball : HarmonicOnNhd (fun ξ => (greatestHarmonicMinorant O (newtonKernelEReal y) ξ).toReal)
        (closedBall x |r|) := fun z hz => hh z (hxr (by rwa [abs_of_pos hr] at hz))
    have hmv := hball.circleAverage_eq
    rw [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le hpi] at hmv
    have hI : ∫ θ in Ioc 0 (2 * Real.pi),
        (newtonKernel (circleMap x r θ) y - greenFunction O (circleMap x r θ) y) =
          ∫ θ in Ioc 0 (2 * Real.pi),
            (greatestHarmonicMinorant O (newtonKernelEReal y) (circleMap x r θ)).toReal :=
      integral_congr_ae ((ae_restrict_of_ae (ae_circleMap_ne hr.ne')).mono fun θ hθ =>
        newtonKernel_sub_greenFunction_eq hOo hOb (hcm θ) hyO hθ)
    rw [integral_mul_const, hI, ← mul_inv_cancel_left₀ hpi' (∫ θ in Ioc 0 (2 * Real.pi), _), hmv,
      newtonKernel_sub_greenFunction_eq hOo hOb hx hyO (Ne.symm hyx)]
    ring
  rw [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le hpi]
  have h1 : ∫ θ in Ioc 0 (2 * Real.pi), (∫ y in O, newtonKernel (circleMap x r θ) y * f y ∂μ -
      ∫ y in O, greenFunction O (circleMap x r θ) y * f y ∂μ) =
        ∫ θ in Ioc 0 (2 * Real.pi), ∫ y in O,
          (newtonKernel (circleMap x r θ) y - greenFunction O (circleMap x r θ) y) * f y ∂μ :=
    integral_congr_ae (ae_of_all _ fun θ => hW _ (hOcl (hcm θ)))
  rw [h1, integral_integral_swap hFint, integral_congr_ae hinner, integral_const_mul,
    hW x (hOcl hx), inv_mul_cancel_left₀ hpi']


theorem greenPotential_local_holder_of_upper {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    {R r₀ βplus : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < βplus)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, μ (ball z r) ≤ ENNReal.ofReal (r ^ βplus)) {O : Set ℂ}
    (hO : IsSmoothBoundedOpen O) (hOR : O ⊆ ball (0 : ℂ) R) {f : ℂ → ℝ} {M : ℝ}
    (hf : AEStronglyMeasurable f (μ.restrict O)) (hfM : ∀ᵐ y ∂μ.restrict O, |f y| ≤ M) :
    ∃ C κ : ℝ, 0 < κ ∧ ∀ x ∈ closure O, ∀ x' ∈ closure O, dist x x' ≤ 1 →
      |(∫ y in O, greenFunction O x y * f y ∂μ) - ∫ y in O, greenFunction O x' y * f y ∂μ| ≤
        C * dist x x' ^ κ := by
  have hOo := isOpen_of_isSmoothBoundedOpen hO
  set α := greenPotentialHolderExponent βplus with hα_def
  have hα : 0 < α := greenPotentialHolderExponent_pos hβ
  have hcl : closure O ⊆ closedBall (0 : ℂ) R :=
    (closure_mono hOR).trans closure_ball_subset_closedBall
  have hfM' : ∀ᵐ y ∂μ.restrict O, |f y| ≤ |M| := hfM.mono fun y hy => hy.trans (le_abs_self M)
  obtain ⟨C, hC0, hVC⟩ := newtonPotential_holder_of_upper hR hr₀ hβ hup hOo.measurableSet hOR
  obtain ⟨-, hVhol⟩ := hVC f |M| hf (abs_nonneg M) hfM'
  set V : ℂ → ℝ := fun x => ∫ y in O, newtonKernel x y * f y ∂μ with hV_def
  set q : ℂ → ℝ := fun x => ∫ y in O, greenFunction O x y * f y ∂μ with hq_def
  have hVcont : ContinuousOn V (closedBall (0 : ℂ) R) := by
    intro x₀ hx₀
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (g := fun x => C * |M| * ‖x - x₀‖ ^ α)
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (eventually_nhdsWithin_of_forall fun x hx => ?_) ?_
    · rw [Real.norm_eq_abs]
      exact hVhol x hx x₀ hx₀
    · have h : Filter.Tendsto (fun x => C * |M| * ‖x - x₀‖ ^ α) (nhdsWithin x₀ (closedBall (0 : ℂ) R))
          (nhds (C * |M| * ‖x₀ - x₀‖ ^ α)) :=
        (((continuous_id.sub continuous_const).norm.rpow_const fun _ => Or.inr hα.le).tendsto x₀
          |>.const_mul _).mono_left nhdsWithin_le_nhds
      simpa [Real.zero_rpow hα.ne'] using h
  have hqc : ContinuousOn q (closure O) := continuousOn_greenPotential_of_upper hR hr₀ hβ hup hO hOR hf hfM
  have hu : HarmonicOnNhd (fun x => V x - q x) O :=
    harmonicOnNhd_newtonPotential_sub_greenPotential_of_upper hR hr₀ hβ hup hO hOR hf hfM
  have huc : ContinuousOn (fun x => V x - q x) (closure O) := (hVcont.mono hcl).sub hqc
  have hq0 : ∀ ξ ∈ frontier O, q ξ = 0 := by
    intro ξ hξ
    have hξO : ξ ∉ O := fun h => hξ.2 (by rw [hOo.interior_eq]; exact h)
    simp [hq_def, greenFunction_of_notMem_left hξO]
  have hub : ∀ ξ ∈ frontier O, V ξ - q ξ = V ξ := fun ξ hξ => by rw [hq0 ξ hξ, sub_zero]
  have hfrB : frontier O ⊆ closedBall (0 : ℂ) R := frontier_subset_closure.trans hcl
  have hgL : ∀ x ∈ frontier O, ∀ y ∈ frontier O, |V x - V y| ≤ C * |M| * dist x y ^ α := by
    intro x hx y hy
    rw [dist_eq_norm]
    exact hVhol x (hfrB hx) y (hfrB hy)
  obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hVcont
  have hgB : ∀ x ∈ frontier O, |V x| ≤ max B₀ 0 := fun x hx =>
    (Real.norm_eq_abs (V x) ▸ hB₀ x (hfrB hx)).trans (le_max_left _ _)
  have hT : ∀ x ∈ closure O, ∀ y ∈ closure O, dist x y ≤ 2 * R := by
    intro x hx y hy
    have hx' := mem_closedBall_zero_iff.mp (hcl hx)
    have hy' := mem_closedBall_zero_iff.mp (hcl hy)
    linarith [dist_le_norm_add_norm x y]
  obtain ⟨d, hd, hgeom⟩ :=
    HarmonicBalls.SmoothDomainExteriorSphere.exists_half_radius_geometry_of_isSmoothBoundedOpen hO
  have hbm := boundary_modulus hOo subset_rfl hOo hO.1 subset_rfl hd hT hgeom hα
    (mul_nonneg hC0 (abs_nonneg M)) (le_max_right B₀ 0) hgL hgB hu huc hub
  have hW := holder_of_boundary_modulus hOo hO.1 subset_rfl hu huc hub hbm
  set C' := C * |M| + 2 * max B₀ 0 / (barrierConst d (2 * R) * d) with hC'_def
  set κ := α / (α + 2) with hκ_def
  have hκ : 0 < κ := div_pos hα (by linarith)
  have hκα : κ ≤ α := div_le_self hα.le (by linarith)
  refine ⟨C * |M| + C', κ, hκ, fun x hx x' hx' hxx' => ?_⟩
  have h1 := hW x hx x' hx' hxx'
  have h2 : |V x - V x'| ≤ C * |M| * dist x x' ^ α := by
    rw [dist_eq_norm]
    exact hVhol x (hcl hx) x' (hcl hx')
  have h3 : dist x x' ^ α ≤ dist x x' ^ κ :=
    Real.rpow_le_rpow_of_exponent_ge' dist_nonneg hxx' hκ.le hκα
  have h4 : C * |M| * dist x x' ^ α ≤ C * |M| * dist x x' ^ κ :=
    mul_le_mul_of_nonneg_left h3 (mul_nonneg hC0 (abs_nonneg M))
  have h5 : q x - q x' = (V x - V x') - ((V x - q x) - (V x' - q x')) := by ring
  change |q x - q x'| ≤ _
  rw [h5]
  calc |(V x - V x') - ((V x - q x) - (V x' - q x'))|
      ≤ |V x - V x'| + |(V x - q x) - (V x' - q x')| := abs_sub _ _
    _ ≤ C * |M| * dist x x' ^ κ + C' * dist x x' ^ κ := add_le_add (h2.trans h4) h1
    _ = (C * |M| + C') * dist x x' ^ κ := by ring



theorem greenPotential_holder_of_upper {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    {R r₀ βplus : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < βplus)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R, μ (ball z r) ≤ ENNReal.ofReal (r ^ βplus)) {O : Set ℂ}
    (hO : IsSmoothBoundedOpen O) (hOR : O ⊆ ball (0 : ℂ) R) {f : ℂ → ℝ} {M : ℝ}
    (hf : AEStronglyMeasurable f (μ.restrict O)) (hfM : ∀ᵐ y ∂μ.restrict O, |f y| ≤ M) :
    ∃ C r : ℝ≥0, 0 < r ∧
      HolderOnWith C r (fun x => ∫ y in O, greenFunction O x y * f y ∂μ) (closure O) := by
  obtain ⟨C, κ, hκ, hloc⟩ := greenPotential_local_holder_of_upper hR hr₀ hβ hup hO hOR hf hfM
  set q : ℂ → ℝ := fun x => ∫ y in O, greenFunction O x y * f y ∂μ with hq_def
  obtain ⟨Q, hQ⟩ := hO.1.isCompact_closure.exists_bound_of_continuousOn
    (continuousOn_greenPotential_of_upper hR hr₀ hβ hup hO hOR hf hfM)
  set D : ℝ := max C (2 * Q) with hD_def
  have hD0 : 0 ≤ max D 0 := le_max_right _ _
  refine ⟨⟨max D 0, hD0⟩, ⟨κ, hκ.le⟩, by exact_mod_cast hκ, holderOnWith_of_bound ?_⟩
  intro x hx x' hx'
  have hp : 0 ≤ dist x x' ^ κ := Real.rpow_nonneg dist_nonneg κ
  rcases le_or_gt (dist x x') 1 with h | h
  · calc |q x - q x'| ≤ C * dist x x' ^ κ := hloc x hx x' hx' h
      _ ≤ max D 0 * dist x x' ^ κ :=
        mul_le_mul_of_nonneg_right ((le_max_left C _).trans (le_max_left _ _)) hp
  · have h1 : 1 ≤ dist x x' ^ κ := Real.one_le_rpow h.le hκ.le
    have hqx := hQ x hx
    have hqx' := hQ x' hx'
    rw [Real.norm_eq_abs] at hqx hqx'
    calc |q x - q x'| ≤ |q x| + |q x'| := abs_sub _ _
      _ ≤ 2 * Q := by linarith
      _ ≤ max D 0 := (le_max_right C _).trans (le_max_left _ _)
      _ ≤ max D 0 * dist x x' ^ κ := le_mul_of_one_le_right hD0 h1


end GreenGeneral

open MeasureTheory Metric Set
open scoped NNReal ENNReal

/-- The singular measure has Hölder Green potentials on every smooth bounded
open set, simultaneously for all bounded densities. -/
theorem IsWholePlaneGFF.ae_singular_greenPotential_smooth_holder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (O : Set ℂ), IsSmoothBoundedOpen O → ∀ f : ℂ → ℝ,
      MemLp f ⊤ ((μ ω).restrict (closure O)) →
      (∀ x ∈ closure O, IntegrableOn (fun y => greenFunction O x y * f y) O (μ ω)) ∧
      ∃ C r : ℝ≥0, 0 < r ∧ HolderOnWith C r
        (fun x => ∫ y in O, greenFunction O x y * f y ∂(μ ω)) (closure O) := by
  filter_upwards [hh.ae_singular_limit_and_approximant_ball_power hγ hγ2 hαQ hμ, hμ] with ω hb hlim
  let _ := hlim.isLocallyFiniteMeasure
  intro O hO f hf
  obtain ⟨R₀, hR₀⟩ := hO.1.subset_ball (0 : ℂ)
  let R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hOR : O ⊆ ball (0 : ℂ) R := hR₀.trans (ball_subset_ball (le_max_left _ _))
  obtain ⟨C, β, r₀, hC, hβ, hr₀, hp⟩ := hb R
  obtain ⟨δ, hδ, hup⟩ := small_ball_power_absorb_constant hC hβ hr₀
    (fun z hz r hr hrr => (hp z hz r hr hrr).1)
  have hβ' : 0 < β / 2 := by positivity
  have hOo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hO
  let M := (eLpNorm f ⊤ ((μ ω).restrict (closure O))).toReal
  have hfM' : ∀ᵐ y ∂(μ ω).restrict (closure O), |f y| ≤ M := by
    filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := (μ ω).restrict (closure O))] with y hy
    rw [Real.enorm_eq_ofReal_abs] at hy
    exact (ENNReal.ofReal_le_iff_le_toReal hf.eLpNorm_ne_top).1 (hy.trans eLpNormEssSup_le_eLpNorm_top)
  have hfM : ∀ᵐ y ∂(μ ω).restrict O, |f y| ≤ M :=
    ae_restrict_of_ae_restrict_of_subset subset_closure hfM'
  have hf' : AEStronglyMeasurable f ((μ ω).restrict O) :=
    hf.aestronglyMeasurable.mono_set subset_closure
  have hcl : closure O ⊆ closedBall (0 : ℂ) R :=
    (closure_mono hOR).trans closure_ball_subset_closedBall
  exact ⟨fun x hx => GreenGeneral.integrableOn_greenFunction_mul_of_upper hR hδ hβ' hup
      hOo hOR hf' hfM x (hcl hx),
    GreenGeneral.greenPotential_holder_of_upper hR hδ hβ' hup hO hOR hf' hfM⟩

end HarmonicBalls
