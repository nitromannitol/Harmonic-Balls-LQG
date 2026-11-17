import HarmonicBalls.Proofs.Potential.LQGClockAnnularContinuumUniformL1
import HarmonicBalls.Proofs.Potential.LQGClockAnnularCellSecondMoment

/-! # Product moments of annular clocks

The stopped annular clocks have a uniform product second-moment bound on
finite time intervals.
-/

open MeasureTheory MarkovProcess Set Filter
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- A nonnegative annular clock stopped before a fixed horizon is bounded by
its unstopped nonnegative occupation integral. -/
theorem ofReal_stopped_annular_clock_le_lintegral (f : ℂ → ℝ) (hf : Continuous f)
    (hf0 : ∀ z, 0 ≤ f z) (δ : ℝ) (b : ContinuousPath ℂ) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 ≤ τ) :
    ENNReal.ofReal (∫ s in (0 : ℝ)..min T τ,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal)) ≤
      ∫⁻ s in Ioc 0 T, ENNReal.ofReal
        ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal)) := by
  let g : ℝ → ℝ := fun s =>
    {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal)
  have hg0 (s : ℝ) : 0 ≤ g s := by
    simp only [g, Set.indicator_apply]
    split_ifs
    · exact hf0 _
    · exact le_rfl
  have hmin : 0 ≤ min T τ := le_min hT hτ
  have hi := intervalIntegrable_annular_density f hf δ b 0 (min T τ)
  change ENNReal.ofReal (∫ s in (0 : ℝ)..min T τ, g s) ≤ ∫⁻ s in Ioc 0 T, ENNReal.ofReal (g s)
  rw [intervalIntegral.integral_of_le hmin,
    ofReal_integral_eq_lintegral_ofReal hi.1 (Filter.Eventually.of_forall hg0)]
  exact lintegral_mono_set (Ioc_subset_Ioc_right (min_le_left _ _))

/-- The square of the stopped annular clock has a uniform integral bound over the
field and Brownian path as the positive smoothing radius tends to zero. -/
theorem exists_lintegral_prod_stopped_annular_clock_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ : γ ≠ 0) (hγ2 : γ ^ 2 < 2) (α δ : ℝ)
    (D : Set ℂ) {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ δ →
      (∫⁻ p : Ω × ContinuousPath ℂ, ENNReal.ofReal (∫ s in (0 : ℝ)..
        min T (ContinuousPath.exitTime D p.2).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z))
          (p.2 s.toNNReal)) ^ 2 ∂(P.prod (planarBrownianMotion x))) ≤ C := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨C, hC, hbound⟩ :=
    exists_lintegral_prod_brownian_annular_inserted_cell_sq_le hh x hγ hγ2 α δ
  refine ⟨C * (ENNReal.ofReal T) ^ (2 - γ ^ 2 / 2), ?_, ?_⟩
  · exact ENNReal.mul_lt_top hC (ENNReal.rpow_lt_top_of_nonneg (by nlinarith) ENNReal.ofReal_ne_top)
  intro ε hε hεδ
  have hcont : ∀ᵐ ω ∂P, Continuous (fun z : ℂ => ε ^ (γ ^ 2 / 2) * Real.exp
      (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) := by
    obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec
    have hc : Continuous (hcirc ω ε) := by
      rw [← funext (hω ε)]
      exact hHc ω ε hε
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z) =
        fun z => hcirc ω ε z - hcirc ω 1 0 - α * Real.log (max ε ‖z‖) := by
      funext z
      exact (hrec ε z hε).symm
    have hci : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z) := by
      rw [heq]
      exact (hc.sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hε).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hci))
  have hp : ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      Continuous (fun z : ℂ => ε ^ (γ ^ 2 / 2) * Real.exp
        (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) :=
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hcont
  calc
    _ ≤ ∫⁻ p : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) T, ENNReal.ofReal
        ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z))
          (p.2 s.toNNReal))) ^ 2 ∂(P.prod (planarBrownianMotion x)) := by
      apply lintegral_mono_ae
      filter_upwards [hp] with p hc
      gcongr
      exact ofReal_stopped_annular_clock_le_lintegral _ hc
        (fun z => mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le)
        δ p.2 hT.le ENNReal.toReal_nonneg
    _ ≤ _ := by simpa using hbound hε hεδ 0 T le_rfl hT

end HarmonicBalls
