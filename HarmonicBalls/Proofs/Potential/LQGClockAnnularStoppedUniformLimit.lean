import HarmonicBalls.Proofs.Potential.LQGClockAnnularLimitRegularity
import HarmonicBalls.Proofs.Potential.LQGClockAnnularExitUniformIntegrability

/-! # Stopped annular clock limits

Uniform convergence on the unit interval passes to the Brownian exit time.
-/

open MeasureTheory MarkovProcess Set Filter HarmonicBalls.Section6
open scoped NNReal ENNReal Topology

namespace HarmonicBalls

/-- The actual annular clocks stopped at Brownian exit converge uniformly on the unit interval.
For each fixed start, the event has full field-path product measure. -/
theorem exists_ae_continuous_monotone_limit_annularClock_stopped_unit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hDb : Bornology.IsBounded D) :
    ∃ K : ℕ, ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ContinuousPath.exitTime D p.2 < ⊤ ∧
      ∃ F : Icc (0 : ℝ) 1 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : Icc (0 : ℝ) 1,
          |(∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D p.2).toReal,
            {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale (j+K))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K)) z))
                  (p.2 s.toNNReal)) - F t| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨K, hK⟩ := exists_ae_continuous_monotone_limit_stoppedAnnularClock hh x hγ hγ2 α hδ
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hdensity : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (fun z =>
      (dyadicScale k)^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z)) := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec k
    have hc : Continuous (hcirc ω (dyadicScale k)) := by
      rw [← funext (hω (dyadicScale k))]
      exact hHc ω (dyadicScale k) (dyadicScale_pos k)
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) =
        fun z => hcirc ω (dyadicScale k) z - hcirc ω 1 0 - α * Real.log (max (dyadicScale k) ‖z‖) := by
      funext z
      exact (hrec _ z (dyadicScale_pos k)).symm
    have hci : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) := by
      rw [heq]
      exact (hc.sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log
          (fun _ => (lt_max_of_lt_left (dyadicScale_pos k)).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hci))
  refine ⟨K, ?_⟩
  filter_upwards [hK,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hdensity,
    (Measure.quasiMeasurePreserving_snd (μ := P) (ν := planarBrownianMotion x)).ae
      (ae_planarBrownian_exitTime_bounded_lt_top x hDb)] with p hp hc hfin
  obtain ⟨F, hFc, hF0, hFm, hF⟩ := hp
  let r : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun t =>
    ⟨min (t : ℝ) (ContinuousPath.exitTime D p.2).toReal,
      ⟨le_min t.2.1 ENNReal.toReal_nonneg, (min_le_left _ _).trans t.2.2⟩⟩
  have hrc : Continuous r := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.min continuous_const
  have hrm : Monotone r := by
    intro s t hst
    change min (s : ℝ) _ ≤ min (t : ℝ) _
    exact min_le_min_right _ hst
  refine ⟨hfin, F ∘ r, hFc.comp hrc, (fun t => hF0 (r t)), hFm.comp hrm, ?_⟩
  intro η hη
  filter_upwards [hF η hη] with j hj t
  have heq := stoppedAnnularClock_eq_time_integral _ (hc (j+K)).measurable δ
    (fun _ => ((r t : ℝ).toNNReal)) p.2
  have hr0 : 0 ≤ (r t : ℝ) := (r t).2.1
  have hr1 : (r t : ℝ) ≤ 1 := (r t).2.2
  simp only [NNReal.coe_one, Real.coe_toNNReal', max_eq_left hr0,
    min_eq_right hr1] at heq
  change |(∫ s in (0 : ℝ)..(r t : ℝ), _) - F (r t)| < η
  rw [← heq]
  exact hj (r t)

/-- For each fixed start, the stopped unit-interval conclusion holds for almost every field
and then for almost every Brownian path. -/
theorem exists_ae_field_ae_path_continuous_monotone_limit_annularClock_stopped_unit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hDb : Bornology.IsBounded D) :
    ∃ K : ℕ, ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x,
      ContinuousPath.exitTime D b < ⊤ ∧
      ∃ F : Icc (0 : ℝ) 1 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : Icc (0 : ℝ) 1,
          |(∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
            {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale (j+K))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (j+K)) z))
                  (b s.toNNReal)) - F t| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨K, hK⟩ :=
    exists_ae_continuous_monotone_limit_annularClock_stopped_unit hh x hγ hγ2 α hδ hDb
  exact ⟨K, Measure.ae_ae_of_ae_prod hK⟩

end HarmonicBalls
