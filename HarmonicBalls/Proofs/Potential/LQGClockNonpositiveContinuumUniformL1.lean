import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveUniformL1

/-! # Inner occupation bounds for nonpositive insertions

A uniform bound controls the inner occupation at every positive smoothing
radius and every Brownian starting point.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The expected inner occupation for a nonpositive insertion obeys one
power bound uniformly in the Brownian starting point and smoothing radius. -/
theorem exists_uniform_lintegral_prod_brownian_inner_nonpositive_inserted_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (x : ℂ) {α ε δ : ℝ}, 0 ≤ γ → α ≤ 0 →
      0 < ε → ε ≤ 1/2 → 0 < δ → δ ≤ 1/2 →
      (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < δ}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal)))
        ∂(P.prod (planarBrownianMotion x))) ≤ (ENNReal.ofReal δ) ^ (1/2 : ℝ) * C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_lintegral_prod_brownian_inner_zero_le hh γ
  refine ⟨C, hC, ?_⟩
  intro x α ε δ hγ hα hε hεhalf hδ hδhalf
  have hcomp (ω : Ω) (z : ℂ) (hz : ‖z‖ < δ) :
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z ≤
      LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z := by
    have hlog : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z ε =
        Real.log (max ε ‖z‖) := by
      simpa using (LatticeProb.Gauss.circleAverage_log_norm_sub_eq z 0 hε)
    have hlogle : Real.log (max ε ‖z‖) ≤ 0 :=
      Real.log_nonpos (le_of_lt (lt_max_of_lt_left hε)) (max_le (by linarith) (by linarith))
    have hmul := mul_nonneg_of_nonpos_of_nonpos hα hlogle
    dsimp [LatticeProb.Gauss.fieldCircleAverage]
    rw [hlog]
    linarith
  calc
    _ ≤ (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < δ}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) ε z)) (q.2 s.toNNReal)))
        ∂(P.prod (planarBrownianMotion x))) := by
      apply lintegral_mono
      intro q
      apply lintegral_mono
      intro s
      apply ENNReal.ofReal_le_ofReal
      simp only [Set.indicator_apply]
      split_ifs with hz
      · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (hcomp q.1 _ hz) hγ))
          (Real.rpow_nonneg (le_of_lt hε) _)
      · exact le_rfl
    _ ≤ _ := hbound x hε hεhalf hδ hδhalf

/-- Almost-everywhere convergence of nonnegative functions and convergence
of their integrals imply convergence in L¹ along a countably generated filter. -/
theorem tendsto_integral_abs_sub_of_nonnegative_of_ae_tendsto
    {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    {l : Filter ι} [l.IsCountablyGenerated] (f : ι → X → ℝ) (g : X → ℝ)
    (hf : ∀ᶠ i in l, Integrable (f i) μ) (hg : Integrable g μ)
    (hf0 : ∀ᶠ i in l, ∀ᵐ x ∂μ, 0 ≤ f i x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun i => f i x) l (𝓝 (g x)))
    (hmean : Tendsto (fun i => ∫ x, f i x ∂μ) l (𝓝 (∫ x, g x ∂μ))) :
    Tendsto (fun i => ∫ x, |f i x - g x| ∂μ) l (𝓝 0) := by
  have hm : ∀ᶠ i in l, AEStronglyMeasurable (fun x => min (f i x) (g x)) μ := by
    filter_upwards [hf] with i hi
    exact (hi.aemeasurable.min hg.aemeasurable).aestronglyMeasurable
  have hb : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖min (f i x) (g x)‖ ≤ g x := by
    filter_upwards [hf0] with i hi
    filter_upwards [hi, hg0] with x hix hx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hix hx)]
    exact min_le_right _ _
  have hc : ∀ᵐ x ∂μ, Tendsto (fun i => min (f i x) (g x)) l (𝓝 (g x)) := by
    filter_upwards [hconv] with x hx
    simpa using hx.min (tendsto_const_nhds : Tendsto (fun _ : ι => g x) l (𝓝 (g x)))
  have hmin := tendsto_integral_filter_of_dominated_convergence g hm hb hg hc
  have heq : ∀ᶠ i in l, (∫ x, |f i x - g x| ∂μ) =
      (∫ x, f i x ∂μ) + (∫ x, g x ∂μ) - 2 * (∫ x, min (f i x) (g x) ∂μ) := by
    filter_upwards [hf] with i hi
    have hmi : Integrable (fun x => min (f i x) (g x)) μ := by
      convert hi.inf hg using 1
    have hp : (fun x => |f i x - g x|) =
        (fun x => f i x + g x - 2 * min (f i x) (g x)) := by
      funext x
      rcases le_total (f i x) (g x) with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
        ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
        ring
    rw [hp]
    rw [integral_sub (f := fun x => f i x + g x) (g := fun x => 2 * min (f i x) (g x)) (hi.add hg) (hmi.const_mul 2)]
    rw [integral_add hi hg, integral_const_mul]
  have ht := (hmean.add (tendsto_const_nhds : Tendsto (fun _ : ι => ∫ x, g x ∂μ) l (𝓝 (∫ x, g x ∂μ)))).sub
    ((tendsto_const_nhds : Tendsto (fun _ : ι => (2 : ℝ)) l (𝓝 2)).mul hmin)
  have ht' : Tendsto (fun i => (∫ x, f i x ∂μ) + (∫ x, g x ∂μ) -
      2 * (∫ x, min (f i x) (g x) ∂μ)) l (𝓝 0) := by
    convert ht using 1; ring
  apply ht'.congr'
  filter_upwards [heq] with i hi
  exact hi.symm

end HarmonicBalls
