import HarmonicBalls.Proofs.Potential.LQGClockInsertedFixedHorizon

/-! # Fixed-horizon cutoff convergence

Summable inserted-clock increments yield a limit at each fixed spatial cutoff.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

private theorem continuous_integrable_unit_path_occupation (b : ContinuousPath ℂ)
    (f : ℂ → ℝ) (hf : Continuous f) :
    Integrable f (Measure.map (fun t => b t)
      (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) := by
  have ht : Integrable (fun s : ℝ => f (b s.toNNReal))
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (hf.comp (b.continuous.comp continuous_real_toNNReal)).integrableOn_Icc
  have hν : Integrable (fun t : ℝ≥0 => f (b t))
      (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))) :=
    (integrable_map_measure (hf.comp b.continuous).aestronglyMeasurable
      continuous_real_toNNReal.measurable.aemeasurable).2 ht
  exact (integrable_map_measure hf.aestronglyMeasurable b.continuous.measurable.aemeasurable).2 hν

/-- The actual inserted cutoff occupations converge along dyadic smoothing
scales at unit time, for almost every path and then almost every field. -/
theorem planarBrownianMotion_ae_field_ae_tendsto_inserted_closedBall_occupation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂planarBrownianMotion x, ∀ δ : ℝ, ∀ᵐ ω ∂P,
      let μ := Measure.map (fun t => b t) ν
      ∃ L : ℝ, Tendsto (fun n : ℕ =>
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        ∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) z ∂μ) atTop (𝓝 L) := by
  have hs := planarBrownianMotion_ae_field_ae_summable_inserted_closedBall_increments
    hh x hq0 hq2 hγ hsub
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  filter_upwards [hs] with b hb
  intro δ
  filter_upwards [hb δ, hcont, ae_recentered_inserted_circle_average hh α] with ω hs hc hr
  let ε : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hstep (n : ℕ) : ε (n+1) = ε n / 2 := by
    dsimp [ε]
    rw [show n+1+1 = (n+1)+1 by omega, pow_succ]
    ring
  let μ := Measure.map (fun t => b t)
    (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
  let D : ℕ → ℂ → ℝ := fun n z => (ε n)^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε n) z)
  let E : Set ℂ := {z | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}
  have hE : MeasurableSet E :=
    (measurableSet_le measurable_norm measurable_const).inter
      (measurableSet_le measurable_norm measurable_const)
  have hD (n : ℕ) : Continuous (D n) := by
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε n) z) =
        fun z => hcirc ω (ε n) z - hcirc ω 1 0 - α * Real.log (max (ε n) ‖z‖) := by
      funext z
      exact (hr (ε n) z (hε n)).symm
    have hcircins : Continuous
        (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε n) z) := by
      rw [heq]
      exact ((hc _ (hε n)).sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left (hε n)).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hcircins))
  have hint (n : ℕ) : Integrable (E.indicator (D n)) μ :=
    (continuous_integrable_unit_path_occupation b (D n) (hD n)).indicator hE
  let A : ℕ → ℝ := fun n => ∫ z, E.indicator (D n) z ∂μ
  have hsum : Summable (fun n => dist (A n) (A (n+1))) := by
    apply hs.congr
    intro n
    change |∫ z, E.indicator (fun z => (ε n/2)^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε n/2) z) -
      (ε n)^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε n) z)) z ∂μ| = _
    rw [← hstep n]
    change |∫ z, E.indicator (fun z => D (n+1) z - D n z) z ∂μ| = _
    rw [show E.indicator (fun z => D (n+1) z - D n z) =
        fun z => E.indicator (D (n+1)) z - E.indicator (D n) z from by
          funext z
          by_cases hz : z ∈ E <;> simp [hz]]
    rw [integral_sub (hint (n+1)) (hint n), Real.dist_eq, abs_sub_comm]
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsum)

end HarmonicBalls
