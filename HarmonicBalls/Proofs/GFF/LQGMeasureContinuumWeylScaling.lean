import HarmonicBalls.Proofs.GFF.LQGMeasureContinuumConvergence
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling
import HarmonicBalls.Proofs.Sec8.VagueMassConvergence
import HarmonicBalls.FirstPass.Phase2.MassFunctionalDerived
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4

/-!
# Weyl scaling of the continuum convergence of whole-plane GMC test integrals

Adding a deterministic continuous function `f` to the field multiplies the LQG measure by
`exp (γ f)` (Fact 2.1 III). For a whole-plane field with a subcritical logarithmic insertion,
on one almost sure event, the circle-average approximations of every perturbed field `h + f`
converge at all positive radii to the reweighted measure, simultaneously for every continuous
compactly supported test function.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LatticeProb.LQG LatticeProb.Gauss

namespace HarmonicBalls

/-- Along any sequence of radii tending to zero, the exponential circle-average weights of a
continuous function, multiplied by a continuous test, converge uniformly on compact sets. -/
theorem tendstoUniformlyOn_test_exp_circleAverage_seq (γ : ℝ) (f φ : ℂ → ℝ)
    (hf : Continuous f) (hφ : Continuous φ) {K : Set ℂ} (hK : IsCompact K)
    {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n z => φ z * Real.exp (γ * Real.circleAverage f z (τ n)))
      (fun z => φ z * Real.exp (γ * f z)) atTop K := by
  let U : Set ℝ := Icc (-1) 1
  have hU : U ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hc : Continuous (fun p : ℝ × ℂ => φ p.2 * Real.exp (γ * Real.circleAverage f p.2 p.1)) :=
    (hφ.comp continuous_snd).mul (Real.continuous_exp.comp
      (continuous_const.mul (Section6.continuous_circleAverage_radius_center hf)))
  have hu : UniformContinuousOn
      (fun p : ℝ × ℂ => φ p.2 * Real.exp (γ * Real.circleAverage f p.2 p.1)) (U ×ˢ K) :=
    (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hc.continuousOn
  have ht := hu.tendstoUniformlyOn
    (F := fun r z => φ z * Real.exp (γ * Real.circleAverage f z r)) (mem_of_mem_nhds hU)
  have ht' : TendstoUniformlyOn (fun r z => φ z * Real.exp (γ * Real.circleAverage f z r))
      (fun z => φ z * Real.exp (γ * f z)) (𝓝 0) K := by
    simpa only [nhdsWithin_eq_nhds.mpr hU, Real.circleAverage_zero] using ht
  rw [Metric.tendstoUniformlyOn_iff] at ht' ⊢
  intro ε hε
  exact hτ.eventually (ht' ε hε)

/-- **Weyl scaling at all positive radii.** For a whole-plane field `h = h^ℂ - α log |·|` with
`0 < γ < 2` and `α < Q`, almost surely, for every continuous function `f` and every continuous
compactly supported test `φ`, the circle-average approximations of `h + f` converge at all
positive radii to the measure `e^{γ f} dμ_h`. -/
theorem ae_tendsto_integral_lqgApprox_continuum_add_continuous
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : HarmonicBalls.IsWholePlaneGFF P hC hcirc)
    {γ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun s : ℝ =>
          ∫ z, φ z ∂(lqgApprox γ (addCircleAverage (fieldCircleAverage α (hcirc ω)) f) s))
        (𝓝[>] 0)
        (𝓝 (∫ z, φ z ∂((μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * f z))))) := by
  have hlp : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc :=
    (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  have hlpμ : LatticeProb.LQG.IsLQGMeasureOfField P γ α hcirc μ :=
    (LPBridge.isLQGMeasureOfField_iff P γ α hcirc μ).mp hμ
  filter_upwards [ae_tendsto_integral_singular_lqgApprox_continuum_all hlp hγ0 hγ2 hαQ hlpμ,
    hlp.ae_continuousOn_circle, hμ] with ω hconv hc hm f hf φ hφ hφc
  have : IsLocallyFiniteMeasure (μ ω) := hm.isLocallyFiniteMeasure
  have hslice : ∀ r : ℝ, 0 < r → Continuous (fieldCircleAverage α (hcirc ω) r) := by
    intro r hr
    have h1 : Continuous (hcirc ω r) := GMCRatioLimit.continuous_slice hc hr
    exact h1.sub (continuous_const.mul (MassFunctionalDerived.continuous_circleAverage_log_norm hr))
  have hfexp : Continuous (fun z => Real.exp (γ * f z)) :=
    Real.continuous_exp.comp (continuous_const.mul hf)
  have hK : IsCompact (tsupport φ) := hφc
  rw [Section6.integral_withDensity_exp (μ ω) γ f φ hf]
  apply tendsto_iff_seq_tendsto.mpr
  intro σ hσ
  have hσpos : ∀ᶠ n in atTop, 0 < σ n := hσ.eventually self_mem_nhdsWithin
  let τ : ℕ → ℝ := fun n => if 0 < σ n then σ n else 1
  have hτpos : ∀ n, 0 < τ n := by
    intro n
    simp only [τ]
    split <;> positivity
  have hτσ : τ =ᶠ[atTop] σ := hσpos.mono fun n hn => ite_eq_left hn
  have hτ : Tendsto τ atTop (𝓝[>] (0 : ℝ)) := hσ.congr' hτσ.symm
  let ν : ℕ → Measure ℂ := fun n => lqgApprox γ (fieldCircleAverage α (hcirc ω)) (τ n)
  have : ∀ n, IsLocallyFiniteMeasure (ν n) := fun n =>
    isLocallyFiniteMeasure_lqgApprox_of_continuous γ _ (τ n) (hslice _ (hτpos n))
  let g : ℕ → ℂ → ℝ := fun n z => φ z * Real.exp (γ * Real.circleAverage f z (τ n))
  have hav : ∀ n, Continuous (fun z => Real.circleAverage f z (τ n)) := fun n =>
    (Section6.continuous_circleAverage_radius_center hf).comp
      (continuous_const.prodMk continuous_id)
  have hg : ∀ n, Integrable (g n) (ν n) := fun n =>
    (hφ.mul (Real.continuous_exp.comp (continuous_const.mul (hav n)))).integrable_of_hasCompactSupport
      hφc.mul_right
  have hoff : ∀ n z, z ∉ tsupport φ → g n z = φ z * Real.exp (γ * f z) := by
    intro n z hz
    have hz' : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
    simp [g, hz']
  have hlim := Section6.tendsto_integral_of_uniformOn_compact ν (μ ω)
    (fun ψ hψ hψc => (hconv ψ hψ hψc).comp hτ) hK (hφ.mul hfexp) hφc.mul_right hg
    (tendstoUniformlyOn_test_exp_circleAverage_seq γ f φ hf hφ hK
      (hτ.mono_right nhdsWithin_le_nhds)) hoff
  have heq : ∀ n, (∫ z, φ z ∂(lqgApprox γ (addCircleAverage (fieldCircleAverage α (hcirc ω)) f)
      (τ n))) = ∫ z, g n z ∂(ν n) := by
    intro n
    rw [Section6.lqgApprox_addCircleAverage γ (τ n) (hτpos n).le _ (hslice _ (hτpos n)) f hf]
    exact Section6.integral_withDensity_exp (ν n) γ (fun z => Real.circleAverage f z (τ n)) φ
      (hav n)
  have hlimτ : Tendsto (fun n => ∫ z, φ z ∂(lqgApprox γ
      (addCircleAverage (fieldCircleAverage α (hcirc ω)) f) (τ n))) atTop
      (𝓝 (∫ z, φ z * Real.exp (γ * f z) ∂(μ ω))) := by
    simp_rw [heq]
    exact hlim
  apply hlimτ.congr'
  filter_upwards [hτσ] with n hn
  simp only [Function.comp_def, hn]

end HarmonicBalls
