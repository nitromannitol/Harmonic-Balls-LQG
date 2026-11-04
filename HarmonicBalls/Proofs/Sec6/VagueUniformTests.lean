import HarmonicBalls.Proofs.Sec6.ContinuousWeylCircleAverage

/-! # Uniformly converging tests under vague convergence -/

namespace HarmonicBalls.Section6

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

/-- For vaguely convergent locally finite measures, uniformly small errors
supported in one compact set have integrals converging to zero. -/
theorem tendsto_integral_sub_zero_of_uniformOn_compact
    (ν : ℕ → Measure ℂ) (μ : Measure ℂ)
    [∀ n, IsLocallyFiniteMeasure (ν n)] [IsLocallyFiniteMeasure μ]
    (hvague : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun n => ∫ x, f x ∂(ν n)) atTop (𝓝 (∫ x, f x ∂μ)))
    {K : Set ℂ} (hK : IsCompact K) {g : ℕ → ℂ → ℝ} {f : ℂ → ℝ}
    (hunif : TendstoUniformlyOn g f atTop K)
    (hoff : ∀ n x, x ∉ K → g n x = f x) :
    Tendsto (fun n => ∫ x, (g n x - f x) ∂(ν n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let C : ℝ := μ.real K + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hδ : 0 < ε / (C + 1) := div_pos hε (by linarith)
  have hu := (Metric.tendstoUniformlyOn_iff.mp hunif) (ε / (C + 1)) hδ
  have hm := eventually_measureReal_compact_le_of_vague ν μ hvague hK
  filter_upwards [hu, hm] with n hn hmass
  have hbound : ‖∫ x in K, (g n x - f x) ∂(ν n)‖ ≤
      (ε / (C + 1)) * (ν n).real K := by
    apply norm_setIntegral_le_of_norm_le_const_ae' hK.measure_lt_top
    filter_upwards [] with x hx
    have hx' := hn x hx
    rw [Real.dist_eq] at hx'
    simpa only [Real.norm_eq_abs, abs_sub_comm] using hx'.le
  have heq : (∫ x, (g n x - f x) ∂(ν n)) =
      ∫ x in K, (g n x - f x) ∂(ν n) := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp only [hoff n x hx, sub_self]
  rw [Real.dist_eq, sub_zero, heq]
  have hmass' : (ν n).real K ≤ C := by simpa only [C] using hmass
  have hnonneg : 0 ≤ (ν n).real K := measureReal_nonneg
  have hcalc : (ε / (C + 1)) * (ν n).real K < ε := by
    have hh : (ε / (C + 1)) * (C + 1) = ε := div_mul_cancel₀ ε (by linarith)
    nlinarith
  exact lt_of_le_of_lt hbound hcalc

/-- Uniformly convergent, integrable perturbations of a compactly supported
continuous test have the expected integral limit under vague convergence. -/
theorem tendsto_integral_of_uniformOn_compact
    (ν : ℕ → Measure ℂ) (μ : Measure ℂ)
    [∀ n, IsLocallyFiniteMeasure (ν n)] [IsLocallyFiniteMeasure μ]
    (hvague : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun n => ∫ x, f x ∂(ν n)) atTop (𝓝 (∫ x, f x ∂μ)))
    {K : Set ℂ} (hK : IsCompact K) {g : ℕ → ℂ → ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hgi : ∀ n, Integrable (g n) (ν n))
    (hunif : TendstoUniformlyOn g f atTop K)
    (hoff : ∀ n x, x ∉ K → g n x = f x) :
    Tendsto (fun n => ∫ x, g n x ∂(ν n)) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hsub := tendsto_integral_sub_zero_of_uniformOn_compact ν μ hvague hK hunif hoff
  have hsum := hsub.add (hvague f hf hfc)
  simp only [zero_add] at hsum
  convert hsum using 1
  funext n
  rw [integral_sub (hgi n) (hf.integrable_of_hasCompactSupport hfc), sub_add_cancel]

end HarmonicBalls.Section6
