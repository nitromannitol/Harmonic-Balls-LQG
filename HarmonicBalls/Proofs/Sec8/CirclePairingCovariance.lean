import HarmonicBalls.Proofs.Sec8.ContinuousLocalVersions

/-! # Covariance criterion for local circle-average approximations

The probabilistic convergence of test pairings is reduced to a deterministic
limit of the GFF covariance kernel. The imported Section 8 frequency argument
uses Leonardo Bonanno's LatticeProb formalization of the ergodic theorem.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ProbabilityTheory ENNReal

namespace HarmonicBalls

/-- For centered square-integrable errors, vanishing variance implies
convergence in probability. -/
theorem tendstoInMeasure_of_centered_variance_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (G : Ω → ℝ)
    (hLp : ∀ n, MemLp (fun ω => F n ω - G ω) 2 P)
    (hmean : ∀ n, ∫ ω, (F n ω - G ω) ∂P = 0)
    (hvar : Tendsto (fun n => variance (fun ω => F n ω - G ω) P) atTop (𝓝 0)) :
    TendstoInMeasure P F atTop G := by
  apply tendstoInMeasure_iff_dist.mpr
  intro ε hε
  have hlim : Tendsto (fun n => ENNReal.ofReal
      (variance (fun ω => F n ω - G ω) P / ε ^ 2)) atTop (𝓝 0) := by
    have hv : Tendsto (fun n => variance (fun ω => F n ω - G ω) P / ε ^ 2)
        atTop (𝓝 0) := by simpa using hvar.div_const (ε ^ 2)
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) ?_
  intro n
  have h := meas_ge_le_variance_div_sq (hLp n) hε
  simpa only [hmean n, sub_zero, Real.dist_eq] using h

/-- The centered circle-minus-pairing variance is given by its six kernel
covariances. -/
theorem IsWholePlaneGFF.variance_pairing_sub_circle_difference
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ)
    (φ : ℂ → ℝ) (hφ : IsTestFunction univ φ) :
    variance (fun ω => hC ω φ - (hcirc ω r z - hcirc ω r 0)) P =
      wholePlaneGFFCov (.pairing φ) (.pairing φ) +
      wholePlaneGFFCov (.circle r z) (.circle r z) +
      wholePlaneGFFCov (.circle r 0) (.circle r 0) -
      2 * wholePlaneGFFCov (.circle r z) (.circle r 0) -
      2 * wholePlaneGFFCov (.pairing φ) (.circle r z) +
      2 * wholePlaneGFFCov (.pairing φ) (.circle r 0) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hp : MemLp (fun ω => hC ω φ) 2 P :=
    (hGFF.isGaussianProcess.hasGaussianLaw_eval
      (⟨.pairing φ, hφ⟩ : GFFObservable.Admissible)).memLp (by simp)
  have hz : MemLp (fun ω => hcirc ω r z) 2 P := (hGFF.hasGaussianLaw_circle hr z).memLp (by simp)
  have h0 : MemLp (fun ω => hcirc ω r 0) 2 P := (hGFF.hasGaussianLaw_circle hr 0).memLp (by simp)
  change variance ((fun ω => hC ω φ) - ((fun ω => hcirc ω r z) -
    (fun ω => hcirc ω r 0))) P = _
  rw [variance_sub hp (hz.sub h0), variance_sub hz h0,
    covariance_sub_right hp hz h0]
  rw [← covariance_self hp.aemeasurable, ← covariance_self hz.aemeasurable,
    ← covariance_self h0.aemeasurable]
  have hpp := hGFF.covariance_eq (.pairing φ) (.pairing φ) hφ hφ
  have hzz := hGFF.covariance_eq (.circle r z) (.circle r z) hr hr
  have h00 := hGFF.covariance_eq (.circle r 0) (.circle r 0) hr hr
  have hz0 := hGFF.covariance_eq (.circle r z) (.circle r 0) hr hr
  have hpz := hGFF.covariance_eq (.pairing φ) (.circle r z) hφ hr
  have hp0 := hGFF.covariance_eq (.pairing φ) (.circle r 0) hφ hr
  simp only [GFFObservable.eval] at hpp hzz h00 hz0 hpz hp0
  rw [hpp, hzz, h00, hz0, hpz, hp0]
  ring

/-- Vanishing covariance-kernel error for local zero-integral tests gives a
joint local version of the centered circle-average field. -/
theorem IsWholePlaneGFF.exists_joint_centered_circle_version_of_covariance_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {ε r : ℝ} (hr : 0 < r)
    (happrox : ∀ z, closedBall z r ⊆ ball 0 ε → ∃ φ : ℕ → ℂ → ℝ,
      (∀ n, IsTestFunction (ball 0 ε) (φ n) ∧ ∫ x, φ n x = 0) ∧
      Tendsto (fun n =>
        wholePlaneGFFCov (.pairing (φ n)) (.pairing (φ n)) +
        wholePlaneGFFCov (.circle r z) (.circle r z) +
        wholePlaneGFFCov (.circle r 0) (.circle r 0) -
        2 * wholePlaneGFFCov (.circle r z) (.circle r 0) -
        2 * wholePlaneGFFCov (.pairing (φ n)) (.circle r z) +
        2 * wholePlaneGFFCov (.pairing (φ n)) (.circle r 0)) atTop (𝓝 0)) :
    ∃ d : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ
        ((Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)).prod inferInstance) _
        (Function.uncurry d) ∧
      ∀ᵐ ω ∂P, ∀ z, closedBall z r ⊆ ball 0 ε →
        d ω z = fieldCircleAverage α₀ (hcirc ω) r z -
          fieldCircleAverage α₀ (hcirc ω) r 0 := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  apply hGFF.exists_joint_centered_circle_version_of_pointwise hr
  intro z hz
  obtain ⟨φ, hφ, hkernel⟩ := happrox z hz
  have htest (n : ℕ) : IsTestFunction univ (φ n) :=
    ⟨(hφ n).1.1, (hφ n).1.2.1, subset_univ _⟩
  have hp (n : ℕ) : MemLp (fun ω => hC ω (φ n)) 2 P :=
    (hGFF.isGaussianProcess.hasGaussianLaw_eval
      (⟨.pairing (φ n), htest n⟩ : GFFObservable.Admissible)).memLp (by simp)
  have hzLp : MemLp (fun ω => hcirc ω r z) 2 P :=
    (hGFF.hasGaussianLaw_circle hr z).memLp (by simp)
  have h0Lp : MemLp (fun ω => hcirc ω r 0) 2 P :=
    (hGFF.hasGaussianLaw_circle hr 0).memLp (by simp)
  have hm : ∀ n, ∫ ω, (hC ω (φ n) - (hcirc ω r z - hcirc ω r 0)) ∂P = 0 := by
    intro n
    have hp0 := hGFF.integral_eq_zero (.pairing (φ n)) (htest n)
    have hz0 := hGFF.integral_eq_zero (.circle r z) hr
    have h00 := hGFF.integral_eq_zero (.circle r 0) hr
    simp only [GFFObservable.eval] at hp0 hz0 h00
    have hxy : Integrable (fun ω => hcirc ω r z - hcirc ω r 0) P :=
      (hzLp.sub h0Lp).integrable (by simp)
    rw [integral_sub ((hp n).integrable (by simp)) hxy,
      integral_sub (hzLp.integrable (by simp)) (h0Lp.integrable (by simp)), hp0, hz0, h00]
    ring
  have hvar : Tendsto (fun n => variance
      (fun ω => hC ω (φ n) - (hcirc ω r z - hcirc ω r 0)) P) atTop (𝓝 0) := by
    convert hkernel using 1
    funext n
    exact hGFF.variance_pairing_sub_circle_difference hr z (φ n) (htest n)
  have hprob : TendstoInMeasure P (fun n ω => hC ω (φ n)) atTop
      (fun ω => hcirc ω r z - hcirc ω r 0) :=
    tendstoInMeasure_of_centered_variance_tendsto_zero P _ _
      (fun n => (hp n).sub (hzLp.sub h0Lp)) hm hvar
  have hpair (n : ℕ) : @Measurable Ω ℝ
      (Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)) _ (fun ω => hC ω (φ n)) := by
    have h := measurable_fieldPairing_modConst α₀ hC (ball 0 ε) (φ n) (hφ n)
    have h' := h.add_const (α₀ * ∫ x, φ n x * Real.log ‖x‖)
    simpa only [fieldPairing, sub_add_cancel] using h'
  obtain ⟨g, hg, hge⟩ := exists_measurable_version_of_tendstoInMeasure
    (Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)) _ _ hpair hprob
  refine ⟨fun ω => g ω - α₀ * (Real.circleAverage (fun x => Real.log ‖x‖) z r -
    Real.circleAverage (fun x => Real.log ‖x‖) 0 r), hg.sub_const _, ?_⟩
  filter_upwards [hge] with ω hω
  dsimp only [fieldCircleAverage]
  rw [← hω]
  ring

end HarmonicBalls
