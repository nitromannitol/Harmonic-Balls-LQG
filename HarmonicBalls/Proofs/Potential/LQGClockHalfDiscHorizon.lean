import HarmonicBalls.Proofs.Potential.LQGClockHalfDiscConvergence
import HarmonicBalls.Proofs.Potential.LQGClockAnnularStoppedUniformLimit

/-! # Half-disc clock convergence on finite horizons

The dyadic inserted half-disc clocks converge locally uniformly in time in the
parameter range where the inner cutoff estimates apply.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- Half-disc convergence holds simultaneously after all integer time shifts. -/
theorem ae_exists_uniform_limit_integer_shift_halfDiscClock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ) (hγ2 : γ^2 < 2)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) :
    ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∀ n : ℕ, ∃ F : Icc (0 : ℝ) 1 → ℝ,
        ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : Icc (0 : ℝ) 1,
          |stoppedAnnularClock (fun z => (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z)) 0
              (fun _ => ((t : ℝ).toNNReal)) (ContinuousPath.shift n p.2) - F t| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨M, hMm, hMc, hMae⟩ := exists_measurable_stoppedAnnularClock_time hh γ α 0
  let A (j : ℕ) (p : Ω × ContinuousPath ℂ) : C(Icc (0 : ℝ) 1, ℝ) :=
    ⟨fun t => M (j+1) (p, t), hMc (j+1) p⟩
  have hAm (j : ℕ) : Measurable (A j) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (hMm (j+1)).comp (measurable_id.prodMk measurable_const)
  let S : Set (Ω × ContinuousPath ℂ) := {p | ∃ F, Tendsto (fun j => A j p) atTop (𝓝 F)}
  have hSm : MeasurableSet S := measurableSet_exists_tendsto hAm
  have hS (y : ℂ) : ∀ᵐ p ∂(P.prod (planarBrownianMotion y)), p ∈ S := by
    filter_upwards [ae_prod_exists_regular_uniform_limit_halfDiscClock hh y hq0 hq2 hγ hγ2 hsub,
      (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion y)).ae hMae] with p hp hM
    obtain ⟨F, hFc, _, _, hF⟩ := hp
    let G : C(Icc (0 : ℝ) 1, ℝ) := ⟨F, hFc⟩
    refine ⟨G, ?_⟩
    apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
    rw [Metric.tendstoUniformly_iff] at hF ⊢
    intro η hη
    filter_upwards [hF η hη] with j hj t
    change dist (F t) (M (j+1) (p, t)) < η
    rw [hM (j+1) p.2 t]
    exact hj t
  apply ae_all_iff.mpr
  intro n
  have hshift := ae_prod_planarBrownianMotion_shift_of_forall_ae P x n S hSm hS
  filter_upwards [hshift, (Measure.quasiMeasurePreserving_fst
    (μ := P) (ν := planarBrownianMotion x)).ae hMae] with p hp hM
  obtain ⟨F, hF⟩ := hp
  refine ⟨F, ?_⟩
  have hu := ContinuousMap.tendsto_iff_tendstoUniformly.mp hF
  rw [Metric.tendstoUniformly_iff] at hu
  intro η hη
  filter_upwards [hu η hη] with j hj t
  have heq := hM (j+1) (ContinuousPath.shift n p.2) t
  change |stoppedAnnularClock _ _ _ _ - F t| < η
  rw [← heq, ← Real.dist_eq, dist_comm]
  exact hj t

/-- At each start, the dyadic half-disc clocks converge locally uniformly in time. -/
theorem ae_exists_locally_uniform_limit_halfDiscClock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ) (hγ2 : γ^2 < 2)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) :
    ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ),
            {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                  (p.2 s.toNNReal)) - F t| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hdensity : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (fun z =>
      (dyadicScale (k+1))^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (k+1)) z)) := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec k
    have hc : Continuous (hcirc ω (dyadicScale (k+1))) := by
      rw [← funext (hω (dyadicScale (k+1)))]
      exact hHc ω (dyadicScale (k+1)) (dyadicScale_pos (k+1))
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (k+1)) z) =
        fun z => hcirc ω (dyadicScale (k+1)) z - hcirc ω 1 0 - α * Real.log (max (dyadicScale (k+1)) ‖z‖) := by
      funext z
      exact (hrec _ z (dyadicScale_pos (k+1))).symm
    have hci : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (k+1)) z) := by
      rw [heq]
      exact (hc.sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log
          (fun _ => (lt_max_of_lt_left (dyadicScale_pos (k+1))).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hci))
  filter_upwards [ae_exists_uniform_limit_integer_shift_halfDiscClock hh x hq0 hq2 hγ hγ2 hsub,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hdensity] with p hp hc
  let f (j : ℕ) : ℂ → ℝ := fun z => (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z)
  let g (j : ℕ) (t : ℝ) : ℝ :=
    {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (f j) (p.2 t.toNNReal)
  let A (j : ℕ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, g j s
  have hblock : ∀ n : ℕ, ∃ F : Icc (0 : ℝ) 1 → ℝ,
      ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ u : Icc (0 : ℝ) 1,
        |(A j ((n : ℝ) + u) - A j n) - F u| < η := by
    intro n
    obtain ⟨F, hF⟩ := hp n
    refine ⟨F, fun η hη => ?_⟩
    filter_upwards [hF η hη] with j hj u
    have heq := stoppedAnnularClock_shift_eq_time_increment (f j) (hc j) 0 p.2 n u
    change stoppedAnnularClock (f j) 0 _ _ = A j (n + u) - A j n at heq
    rw [← heq]
    exact hj u
  have hnat := exists_uniform_limit_on_nat_intervals_of_unit_blocks A
    (fun j => intervalIntegral.integral_same) hblock
  let B (j : ℕ) (t : ℝ≥0) := A j t
  have hBc (j : ℕ) : Continuous (B j) := by
    have h := intervalIntegral.continuous_primitive
      (fun a b => intervalIntegrable_annular_density (f j) (hc j) 0 p.2 a b) 0
    exact h.comp continuous_subtype_val
  have hf0 (j : ℕ) (z : ℂ) : 0 ≤ f j z :=
    mul_nonneg (Real.rpow_nonneg (dyadicScale_pos (j+1)).le _) (Real.exp_pos _).le
  have hg0 (j : ℕ) (t : ℝ) : 0 ≤ g j t :=
    Set.indicator_nonneg (fun z _ => hf0 j z) _
  have hB0 (j : ℕ) (t : ℝ≥0) : 0 ≤ B j t :=
    intervalIntegral.integral_nonneg_of_forall t.coe_nonneg (hg0 j)
  have hBm (j : ℕ) : Monotone (B j) := by
    intro s t hst
    exact intervalIntegral.integral_mono_interval le_rfl s.coe_nonneg hst
      (Eventually.of_forall (hg0 j))
      (intervalIntegrable_annular_density (f j) (hc j) 0 p.2 0 t)
  have hnatB (N : ℕ) : ∃ G : ℝ≥0 → ℝ, ∀ η : ℝ, 0 < η →
      ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ N → |B j t - G t| < η := by
    obtain ⟨G, hG⟩ := hnat N
    refine ⟨fun t => G t, fun η hη => ?_⟩
    filter_upwards [hG η hη] with j hj t ht
    exact hj t ⟨t.coe_nonneg, by exact_mod_cast ht⟩
  exact exists_continuous_monotone_limit_of_uniform_on_nat_intervals B hBc hB0 hBm hnatB


end HarmonicBalls
