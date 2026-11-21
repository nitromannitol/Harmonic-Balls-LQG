import HarmonicBalls.Proofs.Potential.LQGClockOfLocallyUniformLimit
import HarmonicBalls.Proofs.Potential.GreenOccupationCharacterization

/-! # Unstopped clocks from clocks stopped at the exit of large balls

On every bounded time interval a continuous path stays in some ball, and planar Brownian
motion leaves every ball in finite time. Hence locally uniform limits of clocks stopped at the
exit of the balls of integer radius give a jointly measurable locally uniform limit of the
unstopped clocks. Applied to the exterior clocks of the inserted field, this gives the actual
inserted LQG clock for almost every field from limits of exterior clocks stopped at the exit
of balls.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- Almost every planar Brownian path stays, on each bounded time interval, before the exit
time from every sufficiently large ball centred at the origin. -/
theorem ae_eventually_le_exitTime_ball (x : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ T : ℝ≥0, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (T : ℝ) ≤ (ContinuousPath.exitTime (Metric.ball (0 : ℂ) ((N : ℝ) + 1)) b).toReal := by
  have hfin : ∀ N : ℕ, ∀ᵐ b ∂(planarBrownianMotion x),
      ContinuousPath.exitTime (Metric.ball (0 : ℂ) ((N : ℝ) + 1)) b < ⊤ := by
    intro N
    exact ae_lt_top (ContinuousPath.measurable_exitTime _ Metric.isOpen_ball)
      (GreenOccupation.lintegral_exitTime_planarBrownianMotion_lt_top Metric.isOpen_ball
        Metric.isBounded_ball x).ne
  filter_upwards [ae_all_iff.mpr hfin] with b hb T
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ s : ℝ≥0, s ≤ T → ‖b s‖ ≤ R := by
    obtain ⟨R, hR⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
      b.continuous.continuousOn
    exact ⟨R, fun s hs => hR s ⟨zero_le, hs⟩⟩
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge R
  refine ⟨N₀, fun N hN => ?_⟩
  have hle : ((T : ℝ≥0) : ℝ≥0∞) ≤ ContinuousPath.exitTime (Metric.ball (0 : ℂ) ((N : ℝ) + 1)) b := by
    rw [ContinuousPath.le_exitTime_iff]
    intro v hv
    by_contra hlt
    push Not at hlt
    have hvT : v ≤ T := by exact_mod_cast hlt.le
    apply hv
    rw [Metric.mem_ball, dist_zero_right]
    have hNR : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
    linarith [hR v hvT]
  have h := ENNReal.toReal_mono (hb N).ne hle
  simpa using h

/-- Locally uniform limits of clocks stopped at the exit of the balls of integer radius give a
jointly measurable locally uniform limit of the unstopped clocks. -/
theorem exists_ae_eventually_uniform_of_stopped_balls {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (x : ℂ) (A : ℕ → Ω × ContinuousPath ℂ → ℝ → ℝ)
    (hstop : ∀ N : ℕ, ∃ G : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable G ∧
      ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
        ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |A j p (min (t : ℝ)
            (ContinuousPath.exitTime (Metric.ball (0 : ℂ) ((N : ℝ) + 1)) p.2).toReal) -
              G (p, t)| < η) :
    ∃ G : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable G ∧
      ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
        ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T → |A j p (t : ℝ) - G (p, t)| < η := by
  choose G hGm hG using hstop
  refine ⟨fun q => liminf (fun N => G N q) atTop, Measurable.liminf hGm, ?_⟩
  filter_upwards [ae_all_iff.mpr hG, (Measure.quasiMeasurePreserving_snd (μ := P)
    (ν := planarBrownianMotion x)).ae (ae_eventually_le_exitTime_ball x)] with p hp hexit T η hη
  obtain ⟨N₀, hN₀⟩ := hexit T
  have hmin (N : ℕ) (hN : N₀ ≤ N) (t : ℝ≥0) (ht : t ≤ T) :
      min (t : ℝ) (ContinuousPath.exitTime (Metric.ball (0 : ℂ) ((N : ℝ) + 1)) p.2).toReal =
        t := by
    apply min_eq_left
    have : (t : ℝ) ≤ T := by exact_mod_cast ht
    linarith [hN₀ N hN]
  have htend (N : ℕ) (hN : N₀ ≤ N) (t : ℝ≥0) (ht : t ≤ T) :
      Tendsto (fun j => A j p (t : ℝ)) atTop (𝓝 (G N (p, t))) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hp N T ε hε] with j hj
    rw [Real.dist_eq]
    simpa only [hmin N hN t ht] using hj t ht
  have hval (t : ℝ≥0) (ht : t ≤ T) :
      liminf (fun N => G N (p, t)) atTop = G N₀ (p, t) := by
    apply Tendsto.liminf_eq
    apply (tendsto_const_nhds (x := G N₀ (p, t))).congr'
    rw [EventuallyEq, eventually_atTop]
    exact ⟨N₀, fun N hN => tendsto_nhds_unique (htend N₀ le_rfl t ht) (htend N hN t ht)⟩
  filter_upwards [hp N₀ T η hη] with j hj t ht
  rw [hval t ht]
  simpa only [hmin N₀ le_rfl t ht] using hj t ht

/-- For a nonpositive insertion and `γ ^ 2 < 2`, locally uniform limits of the exterior clocks
stopped at the exit of the balls of integer radius give an LQG clock of the inserted field
for almost every field. -/
theorem exists_ae_isLQGClock_fieldCircleAverage_of_stopped_exterior_of_nonpos
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (hα : α ≤ 0)
    (hstop : ∀ N : ℕ, ∃ G : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable G ∧
      ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
        ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..min (t : ℝ)
            (ContinuousPath.exitTime (Metric.ball (0 : ℂ) ((N : ℝ) + 1)) p.2).toReal,
            {z : ℂ | 1/2 < ‖z‖}.indicator (fun z =>
              (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                  (p.2 s.toNNReal)) - G (p,t)| < η) :
    ∃ F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ, ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) x (F ω) :=
  exists_ae_isLQGClock_fieldCircleAverage_of_exterior_of_nonpos hh x hγ hγ2 hα
    (exists_ae_eventually_uniform_of_stopped_balls x (fun j p u =>
      ∫ s in (0 : ℝ)..u, {z : ℂ | 1/2 < ‖z‖}.indicator (fun z =>
        (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
            (p.2 s.toNNReal)) hstop)

/-- For a positive insertion in the range of the inner occupation estimates and
`γ ^ 2 < 2`, locally uniform limits of the exterior clocks stopped at the exit of the balls
of integer radius give an LQG clock of the inserted field for almost every field. -/
theorem exists_ae_isLQGClock_fieldCircleAverage_of_stopped_exterior_of_pos
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ) (hγ2 : γ^2 < 2)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α))
    (hstop : ∀ N : ℕ, ∃ G : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable G ∧
      ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
        ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..min (t : ℝ)
            (ContinuousPath.exitTime (Metric.ball (0 : ℂ) ((N : ℝ) + 1)) p.2).toReal,
            {z : ℂ | 1/2 < ‖z‖}.indicator (fun z =>
              (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                  (p.2 s.toNNReal)) - G (p,t)| < η) :
    ∃ F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ, ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) x (F ω) :=
  exists_ae_isLQGClock_fieldCircleAverage_of_exterior_of_pos hh x hq0 hq2 hγ hγ2 hsub
    (exists_ae_eventually_uniform_of_stopped_balls x (fun j p u =>
      ∫ s in (0 : ℝ)..u, {z : ℂ | 1/2 < ‖z‖}.indicator (fun z =>
        (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
            (p.2 s.toNNReal)) hstop)

end HarmonicBalls
