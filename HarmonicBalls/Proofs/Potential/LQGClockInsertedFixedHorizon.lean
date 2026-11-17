import HarmonicBalls.Proofs.Potential.LQGClockInnerOccupationTransfer

/-! # Fixed-horizon inserted clock increments

The inner and moving-annular estimates combine at a fixed outer cutoff.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set
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

/-- For a fixed start, localized inserted-clock increments are absolutely
summable at unit time on almost every path and then almost every field. -/
theorem planarBrownianMotion_ae_field_ae_summable_inserted_closedBall_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂planarBrownianMotion x, ∀ δ : ℝ, ∀ᵐ ω ∂P,
      let μ := Measure.map (fun t => b t) ν
      Summable (fun n : ℕ =>
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        |∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (ε/2)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
          ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) z ∂μ|) := by
  let ε : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεhalf (n : ℕ) : ε n ≤ 1/2 := by
    dsimp [ε]
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  let p : ℝ := (2 + γ*α)/2
  have hqp : γ*α < p := by dsimp [p]; linarith
  have hp : p < 2 := by dsimp [p]; linarith
  have hinner := planarBrownianMotion_ae_field_ae_summable_inner_inserted_sequence
    hh x γ α p ε hε hεhalf hq0 hqp hp
  have hfiner := planarBrownianMotion_ae_field_ae_summable_inner_inserted_sequence
    hh x γ α p (fun n => ε n / 2) (fun n => by positivity)
      (fun n => by linarith [hεhalf n]) hq0 hqp hp
  have hann := planarBrownianMotion_ae_field_ae_summable_inserted_moving_annulus_increment
    hh x hq0 hq2 hγ hsub
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  filter_upwards [hann, hinner, hfiner] with b hb hi hf
  intro δ
  filter_upwards [hb (fun _ => δ), hi, hf, hcont,
    ae_recentered_inserted_circle_average hh α] with ω ha hi hf hc hr
  let μ := Measure.map (fun t => b t)
    (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
  let D : ℝ → ℂ → ℝ := fun r z => r^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)
  have hD (r : ℝ) (hr0 : 0 < r) : Continuous (D r) := by
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) =
        fun z => hcirc ω r z - hcirc ω 1 0 - α * Real.log (max r ‖z‖) := by
      funext z
      exact (hr r z hr0).symm
    have hcircins : Continuous
        (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) := by
      rw [heq]
      exact ((hc r hr0).sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hr0).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hcircins))
  have hD0 (r : ℝ) (hr0 : 0 < r) (z : ℂ) : 0 ≤ D r z :=
    mul_nonneg (Real.rpow_nonneg hr0.le _) (Real.exp_pos _).le
  have ha' : Summable (fun n : ℕ =>
      |∫ z, {z : ℂ | ε n ≤ ‖z‖ ∧ ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => D (ε n/2) z - D (ε n) z) z ∂μ|) := by
    apply ha.congr
    intro n
    change |∫ z, {z : ℂ | ε n ≤ ‖z‖ ∧ ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
      (ε n/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε n/2) z-hcirc ω 1 0 - α*Real.log (max (ε n/2) ‖z‖))) -
      (ε n)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε n) z-hcirc ω 1 0 - α*Real.log (max (ε n) ‖z‖)))) z ∂μ| = _
    apply congrArg abs
    apply integral_congr_ae
    filter_upwards with z
    simp only [Set.indicator_apply]
    split_ifs
    · dsimp [D]
      rw [← hr (ε n/2) z (by positivity), ← hr (ε n) z (hε n)]
    · rfl
  exact summable_closedBall_increment_of_annulus_and_inner μ ε δ
    (fun n => D (ε n/2)) (fun n => D (ε n))
    (fun n => continuous_integrable_unit_path_occupation b _ (hD _ (by positivity)))
    (fun n => continuous_integrable_unit_path_occupation b _ (hD _ (hε n)))
    (fun n => hD0 _ (by positivity)) (fun n => hD0 _ (hε n)) ha' hf hi


end HarmonicBalls
