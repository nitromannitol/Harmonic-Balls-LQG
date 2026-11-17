import HarmonicBalls.Proofs.Potential.LQGClockInsertedIncrementExpectation
import HarmonicBalls.Proofs.Potential.LQGClockShiftedIncrementEnvelope
import HarmonicBalls.Proofs.Potential.LQGClockClosedOpenOccupation

/-! # Expected fine-scale inner occupations

Expected inner occupations vanish uniformly over finer dyadic smoothing scales.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- For a fixed Brownian start, expected closed-ball occupations vanish uniformly
over finer dyadic smoothing scales in the displayed parameter regime. -/
theorem tendsto_lintegral_iSup_inserted_inner_closed_occupation_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ * α) (hq1 : γ * α < 1) (hγ : 0 < γ)
    (hsub : γ^2/2 < 2*(1-γ*α)) :
    Tendsto (fun n : ℕ => ∫⁻ q : ContinuousPath ℂ × Ω, ⨆ i : ℕ,
      let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+i+1)
      ENNReal.ofReal |∫ z,
        {z : ℂ | ‖z‖ ≤ (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator
          (fun z => ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) ε z)) z
          ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
            (volume.restrict (Icc (0 : ℝ) 1))))|
      ∂((planarBrownianMotion x).prod P)) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let d : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n+1)
  have hd (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have hdhalf (n : ℕ) : d n ≤ 1/2 := by
    dsimp [d]
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hdstep (n : ℕ) : d (n+1) = d n / 2 := by
    dsimp [d]
    rw [show n+1+1 = (n+1)+1 by omega, pow_succ]
    ring
  have hdlt (n : ℕ) : d (n+1) < d n := by rw [hdstep]; linarith [hd n]
  let X (n i : ℕ) (q : ContinuousPath ℂ × Ω) : ℝ := ∫ z,
    {z : ℂ | ‖z‖ ≤ d (n+1) ∧ ‖z‖ ≤ 1/2}.indicator
      (fun z => (d (n+i))^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (d (n+i)) z)) z
      ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))))
  have hX (n i : ℕ) : AEMeasurable (X n i) ((planarBrownianMotion x).prod P) :=
    aemeasurable_inserted_closedBall_occupation hh (planarBrownianMotion x) γ α
      (d (n+1)) (d (n+i)) (hd _)
  obtain ⟨A, hAs, hA⟩ := exists_summable_uniform_inserted_cutoff_increment_bound hh x hq0 hq1 hγ hsub
  obtain ⟨C, hCs, hC⟩ := exists_summable_uniform_inner_inserted_expectation_bound hh x γ α 1 hq0 hq1 (by norm_num)
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  have hpoint : ∀ᵐ q : ContinuousPath ℂ × Ω ∂((planarBrownianMotion x).prod P),
      ∀ n : ℕ, ENNReal.ofReal |X n 0 q| ≤
        ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < d n}.indicator (fun z => (d n)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (d n) z)) (q.1 s.toNNReal)) := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd
      (μ := planarBrownianMotion x) (ν := P)).ae hcont,
      (Measure.quasiMeasurePreserving_snd
      (μ := planarBrownianMotion x) (ν := P)).ae
        (ae_recentered_inserted_circle_average hh α)] with q hc hr n
    let f : ℂ → ℝ := fun z => (d n)^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (d n) z)
    have hfeq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (d n) z) =
        fun z => hcirc q.2 (d n) z - hcirc q.2 1 0 - α * Real.log (max (d n) ‖z‖) := by
      funext z
      exact (hr (d n) z (hd n)).symm
    have hf : Continuous f := by
      have hfc : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (d n) z) := by
        rw [hfeq]
        exact ((hc (d n) (hd n)).sub continuous_const).sub (continuous_const.mul
          ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left (hd n)).ne')))
      exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hfc))
    have hf0 (z : ℂ) : 0 ≤ f z :=
      mul_nonneg (Real.rpow_nonneg (hd n).le _) (Real.exp_pos _).le
    simpa [X, f] using closed_unit_occupation_le_lintegral_inner_time q.1 f hf hf0 (hdlt n) (hdhalf n)
  have hinit : Tendsto (fun n => ∫⁻ q, ENNReal.ofReal |X n 0 q|
      ∂((planarBrownianMotion x).prod P)) atTop (𝓝 0) := by
    have ht : Tendsto C atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hCs.ne
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
    intro n
    calc
      _ ≤ ∫⁻ q : ContinuousPath ℂ × Ω, (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < d n}.indicator (fun z => (d n)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (d n) z)) (q.1 s.toNNReal)))
          ∂((planarBrownianMotion x).prod P) := lintegral_mono_ae (hpoint.mono fun q hq => hq n)
      _ = ∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < d n}.indicator (fun z => (d n)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (d n) z)) (q.2 s.toNNReal)))
          ∂(P.prod (planarBrownianMotion x)) := by
            let F (q : Ω × ContinuousPath ℂ) := ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
              ({z : ℂ | ‖z‖ < d n}.indicator (fun z => (d n)^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (d n) z)) (q.2 s.toNNReal))
            change (∫⁻ q, F q.swap ∂((planarBrownianMotion x).prod P)) =
              ∫⁻ q, F q ∂(P.prod (planarBrownianMotion x))
            exact lintegral_prod_swap F
      _ ≤ C n := hC n (d n) (hd n) (hdhalf n)
  have hinc (n i : ℕ) : (∫⁻ q, ENNReal.ofReal |X n (i+1) q - X n i q|
      ∂((planarBrownianMotion x).prod P)) ≤ A (n+i) := by
    have h := hA (n+i) (d (n+1))
    simpa only [X, ← Nat.add_assoc, hdstep, d] using h
  have h := tendsto_lintegral_iSup_ofReal_abs_zero_of_shifted_envelope
    ((planarBrownianMotion x).prod P) X hX A hAs.ne hinit hinc
  simpa only [X, d, Nat.add_assoc] using h

end HarmonicBalls
