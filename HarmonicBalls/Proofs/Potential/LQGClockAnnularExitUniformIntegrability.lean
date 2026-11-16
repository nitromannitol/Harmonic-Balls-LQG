import HarmonicBalls.Proofs.Potential.LQGClockAnnularUniformIntegrability
import HarmonicBalls.Proofs.Potential.BrownianExpectedExitGreen

/-! # Annular clock integrability at Brownian exit

Continuous densities restricted to a compact annulus have integrable occupation
up to the exit time of a bounded open domain.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Filter Set
open scoped NNReal ENNReal Topology

namespace HarmonicBalls

/-- The annular occupation of a continuous density up to Brownian exit is integrable. -/
theorem integrable_annular_clock_exit_of_continuous {D : Set ℂ} (hD : IsOpen D)
    (hDb : Bornology.IsBounded D) (x : ℂ) (f : ℂ → ℝ) (hf : Continuous f) (δ : ℝ) :
    Integrable (fun b : ContinuousPath ℂ => ∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal))
      (planarBrownianMotion x) := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let g : ℂ → ℝ := A.indicator f
  have hg : Measurable g := hf.measurable.indicator hA
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (1/2 : ℝ)).bddAbove_image hf.norm.continuousOn
  have hgK : ∀ z, ‖g z‖ ≤ max K 0 := by
    intro z
    by_cases hz : z ∈ A
    · have hzk : z ∈ Metric.closedBall (0 : ℂ) (1/2 : ℝ) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
      rw [show g z = f z from Set.indicator_of_mem hz _]
      exact (hK ⟨z, hzk, rfl⟩).trans (le_max_left K 0)
    · rw [show g z = 0 from Set.indicator_of_notMem hz _, norm_zero]
      exact le_max_right K 0
  let τ : ContinuousPath ℂ → ℝ := fun b => (ContinuousPath.exitTime D b).toReal
  have hτ : Measurable τ := ENNReal.measurable_toReal.comp (ContinuousPath.measurable_exitTime D hD)
  have hτint : Integrable τ (planarBrownianMotion x) :=
    GreenOccupation.integrable_exitTime_toReal hD hDb x
  have heval : Measurable (fun p : ContinuousPath ℂ × ℝ => p.1 p.2.toNNReal) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  have hF : Measurable (fun p : ContinuousPath ℂ × ℝ => g (p.1 p.2.toNNReal)) := hg.comp heval
  let S : Set (ContinuousPath ℂ × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ τ p.1}
  have hS : MeasurableSet S := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (hτ.comp measurable_fst))
  have hI : StronglyMeasurable (fun b : ContinuousPath ℂ =>
      ∫ s in (0 : ℝ)..τ b, g (b s.toNNReal)) := by
    have h := (hF.indicator hS).stronglyMeasurable.integral_prod_right' (ν := volume)
    convert h using 1
    funext b
    rw [intervalIntegral.integral_of_le ENNReal.toReal_nonneg]
    change (∫ s in Set.Ioc 0 (τ b), g (b s.toNNReal)) = _
    rw [← integral_indicator measurableSet_Ioc]
    rfl
  refine (hτint.const_mul (max K 0)).mono' hI.aestronglyMeasurable
    (Filter.Eventually.of_forall ?_)
  intro b
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := τ b) (fun s _ => hgK (b s.toNNReal))
  simpa [τ, g, A, abs_of_nonneg ENNReal.toReal_nonneg, le_max_right K 0] using hbound

/-- Each dyadic annular clock is integrable up to the actual Brownian exit,
for almost every field and a fixed Brownian starting point. -/
theorem ae_integrable_annular_clock_exit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    (γ α δ : ℝ) (x : ℂ) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, Integrable (fun b : ContinuousPath ℂ =>
      ∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (dyadicScale k)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z))
          (b s.toNNReal)) (planarBrownianMotion x) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  filter_upwards [hcont, ae_recentered_inserted_circle_average hh α] with ω hcont hrec
  intro k
  have hr := dyadicScale_pos k
  have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) =
      fun z => hcirc ω (dyadicScale k) z - hcirc ω 1 0 -
        α * Real.log (max (dyadicScale k) ‖z‖) := by
    funext z
    exact (hrec _ z hr).symm
  have hc : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) := by
    rw [heq]
    exact ((hcont _ hr).sub continuous_const).sub
      (continuous_const.mul ((continuous_const.max continuous_norm).log
        (fun _ => (lt_max_of_lt_left hr).ne')))
  exact integrable_annular_clock_exit_of_continuous hD hDb x _
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc))) δ

end HarmonicBalls
