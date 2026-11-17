import HarmonicBalls.Proofs.Potential.LQGClockFineInnerExpectation
import HarmonicBalls.Proofs.Potential.LQGClockInnerCoarseDyadic

/-! # Pathwise convergence from decreasing expected bounds

Decreasing nonnegative random variables with vanishing expectations converge
almost surely to zero.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- A decreasing sequence of extended nonnegative random variables converges
almost surely to zero when its expectations tend to zero. -/
theorem ae_tendsto_zero_of_antitone_lintegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ≥0∞)
    (hX : ∀ n, AEMeasurable (X n) P)
    (hmono : ∀ᵐ ω ∂P, Antitone (fun n => X n ω))
    (hmean : Tendsto (fun n => ∫⁻ ω, X n ω ∂P) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  have hle : ∀ n, (∫⁻ ω, ⨅ j, X j ω ∂P) ≤ ∫⁻ ω, X n ω ∂P := by
    intro n
    exact lintegral_mono (fun ω => iInf_le (fun j => X j ω) n)
  have hzero : (∫⁻ ω, ⨅ j, X j ω ∂P) = 0 :=
    le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds hmean (Eventually.of_forall hle)) bot_le
  have hae : ∀ᵐ ω ∂P, (⨅ j, X j ω) = 0 :=
    (lintegral_eq_zero_iff' (AEMeasurable.iInf hX)).mp hzero
  filter_upwards [hmono, hae] with ω hω hzero
  simpa only [hzero] using tendsto_atTop_iInf hω

/-- The fine-scale closed-cutoff occupations vanish almost surely under the
path-field product law in the stated parameter range. -/
theorem ae_tendsto_iSup_inserted_fine_inner_occupation_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ * α) (hq1 : γ * α < 1) (hγ : 0 < γ)
    (hsub : γ^2/2 < 2*(1-γ*α)) :
    ∀ᵐ q : ContinuousPath ℂ × Ω ∂((planarBrownianMotion x).prod P),
      Tendsto (fun n : ℕ => ⨆ i : ℕ,
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+i+1)
        ENNReal.ofReal |∫ z,
          {z : ℂ | ‖z‖ ≤ (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator
            (fun z => ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) ε z)) z
          ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
            (volume.restrict (Icc (0 : ℝ) 1))))|) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let d : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n+1)
  have hd (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  let E : ℕ → Set ℂ := fun n => {z | ‖z‖ ≤ d (n+1) ∧ ‖z‖ ≤ 1/2}
  let μ (q : ContinuousPath ℂ × Ω) := Measure.map (fun t => q.1 t)
    (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
  let F (q : ContinuousPath ℂ × Ω) (i : ℕ) (z : ℂ) := (d i)^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (d i) z)
  let A (n i : ℕ) (q : ContinuousPath ℂ × Ω) := ∫ z, (E n).indicator (F q i) z ∂(μ q)
  let X (n : ℕ) (q : ContinuousPath ℂ × Ω) := ⨆ i : ℕ, ENNReal.ofReal |A n (n+i) q|
  have hX (n : ℕ) : AEMeasurable (X n) ((planarBrownianMotion x).prod P) := by
    apply AEMeasurable.iSup
    intro i
    exact ((aemeasurable_inserted_closedBall_occupation hh (planarBrownianMotion x) γ α
      (d (n+1)) (d (n+i)) (hd _)).abs).ennreal_ofReal
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  have hmono : ∀ᵐ q : ContinuousPath ℂ × Ω ∂((planarBrownianMotion x).prod P),
      Antitone (fun n => X n q) := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd
      (μ := planarBrownianMotion x) (ν := P)).ae hcont,
      (Measure.quasiMeasurePreserving_snd (μ := planarBrownianMotion x) (ν := P)).ae
        (ae_recentered_inserted_circle_average hh α)] with q hc hr
    have hF (i : ℕ) : Continuous (F q i) := by
      have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (d i) z) =
          fun z => hcirc q.2 (d i) z - hcirc q.2 1 0 - α * Real.log (max (d i) ‖z‖) := by
        funext z
        exact (hr (d i) z (hd i)).symm
      have hi : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (d i) z) := by
        rw [heq]
        exact ((hc _ (hd i)).sub continuous_const).sub (continuous_const.mul
          ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left (hd i)).ne')))
      exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hi))
    have hF0 (i : ℕ) (z : ℂ) : 0 ≤ F q i z :=
      mul_nonneg (Real.rpow_nonneg (hd i).le _) (Real.exp_pos _).le
    have hE (n : ℕ) : MeasurableSet (E n) :=
      (measurableSet_le measurable_norm measurable_const).inter
        (measurableSet_le measurable_norm measurable_const)
    have hint (n i : ℕ) : Integrable ((E n).indicator (F q i)) (μ q) := by
      have ht : Integrable (fun s : ℝ => F q i (q.1 s.toNNReal))
          (volume.restrict (Icc (0 : ℝ) 1)) :=
        ((hF i).comp (q.1.continuous.comp continuous_real_toNNReal)).integrableOn_Icc
      have hu : Integrable (fun t : ℝ≥0 => F q i (q.1 t))
          (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))) :=
        (integrable_map_measure ((hF i).comp q.1.continuous).aestronglyMeasurable
          continuous_real_toNNReal.measurable.aemeasurable).2 ht
      exact ((integrable_map_measure (hF i).aestronglyMeasurable
        q.1.continuous.measurable.aemeasurable).2 hu).indicator (hE n)
    have hA0 (n i : ℕ) : 0 ≤ A n i q := by
      apply integral_nonneg
      intro z
      exact Set.indicator_nonneg (fun z _ => hF0 i z) z
    have hEsub (n : ℕ) : E (n+1) ⊆ E n := by
      intro z hz
      refine ⟨hz.1.trans ?_, hz.2⟩
      dsimp [d]
      rw [show n+1+1+1 = (n+1+1)+1 by omega, pow_succ]
      have hp : 0 ≤ (2 : ℝ)⁻¹ ^ (n+1+1) := by positivity
      nlinarith
    apply antitone_nat_of_succ_le
    intro n
    dsimp only [X]
    apply iSup_le
    intro i
    have hle : A (n+1) (n+1+i) q ≤ A n (n+1+i) q := by
      apply integral_mono_ae (hint (n+1) _) (hint n _)
      exact Eventually.of_forall (Set.indicator_le_indicator_of_subset (hEsub n) (hF0 _))
    rw [abs_of_nonneg (hA0 _ _)]
    calc
      _ ≤ ENNReal.ofReal (A n (n+1+i) q) := ENNReal.ofReal_le_ofReal hle
      _ = ENNReal.ofReal |A n (n+1+i) q| := by rw [abs_of_nonneg (hA0 _ _)]
      _ ≤ _ := by
        simpa only [show n + (i + 1) = n + 1 + i by omega] using
          le_iSup (fun j : ℕ => ENNReal.ofReal |A n (n+j) q|) (i+1)
  have hmean : Tendsto (fun n => ∫⁻ q, X n q ∂((planarBrownianMotion x).prod P)) atTop (𝓝 0) := by
    simpa only [X, A, E, F, μ, d, Nat.add_assoc] using
      tendsto_lintegral_iSup_inserted_inner_closed_occupation_zero hh x hq0 hq1 hγ hsub
  simpa only [X, A, E, F, μ, d, Nat.add_assoc] using
    ae_tendsto_zero_of_antitone_lintegral _ X hX hmono hmean

end HarmonicBalls
