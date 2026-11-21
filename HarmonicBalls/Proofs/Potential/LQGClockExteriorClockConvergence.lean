import HarmonicBalls.Proofs.Potential.LQGClockStoppedDomainHalfDiscGluing
import HarmonicBalls.Proofs.Potential.LQGClockAnnularScaleRecursion

/-! # Convergence of the exterior, exit-stopped and unstopped clocks

The dyadic time-cell moment bound for the bounded exterior occupation holds for every radius,
every Brownian start and `γ ^ 2 < 4` (`exists_exterior_dyadic_cell_moment`). It discharges the
moment premise of the conditional convergence theorems. For `0 < γ < 2` and any insertion, the
exterior clocks stopped at the exit of a bounded domain converge uniformly on the unit interval
and locally uniformly on `[0, ∞)`, almost surely under the field-path product law, and the
locally uniform limit at the exit of a ball has a jointly measurable version. Adding the
half-disc clocks, the full exit-stopped and unstopped clocks converge for nonpositive insertions
with `γ ^ 2 < 2` and for positive insertions in the range of the inner occupation estimates.

## Main results

* `ae_tendstoUniformlyOn_stopped_exterior_clock`, `ae_exists_locally_uniform_limit_stopped_exterior_clock`
* `exists_measurable_locally_uniform_limit_stopped_exterior_clock_ball`
* `ae_tendstoUniformlyOn_stopped_domain_clock_nonpositive`, `ae_tendstoUniformlyOn_stopped_domain_clock`
* `ae_exists_locally_uniform_limit_stopped_domain_clock_nonpositive`,
  `ae_exists_locally_uniform_limit_stopped_domain_clock`
* `ae_exists_locally_uniform_limit_clock_nonpositive`, `ae_exists_locally_uniform_limit_clock`
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- For `0 < γ < 2` and any insertion, the exterior clocks stopped at the exit of a bounded open
domain converge uniformly on `[0, 1]` to a continuous, nondecreasing and nonnegative limit,
almost surely under the field-path product law. -/
theorem ae_tendstoUniformlyOn_stopped_exterior_clock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ)
    {D : Set ℂ} (hD : IsOpen D) {R : ℝ} (hR : 0 < R) (hDR : ∀ z ∈ D, ‖z‖ ≤ R) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), ∃ F : ℝ → ℝ,
      ContinuousOn F (Icc 0 1) ∧ MonotoneOn F (Icc 0 1) ∧ (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ F t) ∧
      TendstoUniformlyOn (fun n (t : ℝ) =>
        ∫ s in (0 : ℝ)..min t (ContinuousPath.exitTime D q.2).toReal,
          {z : ℂ | (1 : ℝ) / 2 < ‖z‖}.indicator (fun z =>
            dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z))
            (q.2 s.toNNReal)) F atTop (Icc 0 1) := by
  obtain ⟨p, a, C, hp, ha, hm⟩ := exists_exterior_dyadic_cell_moment hh (show γ ^ 2 < 4 by nlinarith) α R
  exact ae_tendstoUniformlyOn_stopped_exterior_clock_of_cell_moment hh hγ0 hγ2 α x hD hR hDR
    hp ha (hm x)

/-- For `0 < γ < 2` and any insertion, the exterior clocks stopped at the exit of a bounded
domain converge locally uniformly on `[0, ∞)` to a continuous, nonnegative and nondecreasing
limit, and the exit time is finite, almost surely under the field-path product law. -/
theorem ae_exists_locally_uniform_limit_stopped_exterior_clock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ)
    {D : Set ℂ} {R : ℝ} (hR : 0 < R) (hDR : ∀ z ∈ D, ‖z‖ ≤ R) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
      ContinuousPath.exitTime D q.2 < ⊤ ∧
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D q.2).toReal,
            {z : ℂ | (1 : ℝ) / 2 < ‖z‖}.indicator (fun z =>
            dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z))
              (q.2 s.toNNReal)) - F t| < η := by
  obtain ⟨p, a, C, hp, ha, hm⟩ := exists_exterior_dyadic_cell_moment hh (show γ ^ 2 < 4 by nlinarith) α R
  exact ae_exists_locally_uniform_limit_stopped_exterior_clock_of_cell_moment hh hγ0 hγ2 α x hR
    hDR hp ha hm

/-- For `0 < γ < 2` and any insertion, the exterior clocks stopped at the exit of the ball of
radius `N + 1` have a locally uniform limit on `[0, ∞)` which is jointly measurable in the
field, the path and the time, almost surely under the field-path product law. -/
theorem exists_measurable_locally_uniform_limit_stopped_exterior_clock_ball
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) (N : ℕ) :
    ∃ G : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable G ∧
      ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
        ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..min (t : ℝ)
            (ContinuousPath.exitTime (Metric.ball (0 : ℂ) ((N : ℝ) + 1)) q.2).toReal,
            {z : ℂ | (1 : ℝ) / 2 < ‖z‖}.indicator (fun z =>
            dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z))
              (q.2 s.toNNReal)) - G (q, t)| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let D : Set ℂ := Metric.ball (0 : ℂ) ((N : ℝ) + 1)
  let A : Set ℂ := {z : ℂ | (1 : ℝ) / 2 < ‖z‖ ∧ ‖z‖ ≤ (N : ℝ) + 1}
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  have hDR : ∀ z ∈ D, ‖z‖ ≤ (N : ℝ) + 1 := fun z hz => (mem_ball_zero_iff.mp hz).le
  choose M hMm _hMr hMae using fun n : ℕ =>
    exists_measurable_stopped_indicator_clock_prod_time hh (dyadicScale_pos (n + 1)) γ α hA
      (ContinuousPath.measurable_exitTime D Metric.isOpen_ball).ennreal_toReal
      (fun _ => ENNReal.toReal_nonneg)
  refine ⟨fun r => liminf (fun n => M n r) atTop, Measurable.liminf hMm, ?_⟩
  filter_upwards [ae_exists_locally_uniform_limit_stopped_exterior_clock hh hγ0 hγ2 α x
    (D := D) (by positivity) hDR, (Measure.quasiMeasurePreserving_fst (μ := P)
      (ν := planarBrownianMotion x)).ae (ae_all_iff.mpr hMae)] with q hq hM
  obtain ⟨-, F, -, -, -, hF⟩ := hq
  have hMeq (n : ℕ) (t : ℝ≥0) : M n (q, t) =
      ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D q.2).toReal,
        {z : ℂ | (1 : ℝ) / 2 < ‖z‖}.indicator (fun z =>
            dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z))
          (q.2 s.toNNReal) :=
    (hM n q.2 t).trans (stopped_exterior_clock_eq_bounded _ q.2 D _ hDR t).symm
  have hlim (t : ℝ≥0) : Tendsto (fun n => M n (q, t)) atTop (𝓝 (F t)) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    filter_upwards [hF t η hη] with n hn
    rw [Real.dist_eq, hMeq n t]
    exact hn t le_rfl
  intro T η hη
  filter_upwards [hF T η hη] with n hn t ht
  rw [(hlim t).liminf_eq]
  exact hn t ht

/-- For a nonpositive insertion and `0 < γ` with `γ ^ 2 < 2`, the full inserted clocks stopped
at the exit of a bounded open domain converge uniformly on `[0, 1]` to a continuous,
nondecreasing and nonnegative limit, almost surely under the field-path product law. -/
theorem ae_tendstoUniformlyOn_stopped_domain_clock_nonpositive
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ ^ 2 < 2) (hα : α ≤ 0) (x : ℂ)
    {D : Set ℂ} (hD : IsOpen D) {R : ℝ} (hR : 0 < R) (hDR : ∀ z ∈ D, ‖z‖ ≤ R) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), ∃ F : ℝ → ℝ,
      ContinuousOn F (Icc 0 1) ∧ MonotoneOn F (Icc 0 1) ∧ (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ F t) ∧
      TendstoUniformlyOn (fun n (t : ℝ) =>
        ∫ s in (0 : ℝ)..min t (ContinuousPath.exitTime D q.2).toReal,
          dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1))
              (q.2 s.toNNReal))) F atTop (Icc 0 1) := by
  obtain ⟨p, a, C, hp, ha, hm⟩ := exists_exterior_dyadic_cell_moment hh (show γ ^ 2 < 4 by nlinarith) α R
  exact ae_tendstoUniformlyOn_stopped_domain_clock_nonpositive_of_cell_moment hh hγ0 hγ2 hα x hD
    hR hDR hp ha (hm x)

/-- For a positive insertion in the range of the inner occupation estimates and `γ ^ 2 < 2`,
the full inserted clocks stopped at the exit of a bounded open domain converge uniformly on
`[0, 1]` to a continuous, nondecreasing and nonnegative limit, almost surely under the
field-path product law. -/
theorem ae_tendstoUniformlyOn_stopped_domain_clock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hq0 : 0 < γ * α) (hq2 : γ * α < 2) (hγ0 : 0 < γ) (hγ2 : γ ^ 2 < 2)
    (hsub : γ ^ 2 / 2 < 2 * (2 - γ * α) / (2 + γ * α)) (x : ℂ)
    {D : Set ℂ} (hD : IsOpen D) {R : ℝ} (hR : 0 < R) (hDR : ∀ z ∈ D, ‖z‖ ≤ R) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), ∃ F : ℝ → ℝ,
      ContinuousOn F (Icc 0 1) ∧ MonotoneOn F (Icc 0 1) ∧ (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ F t) ∧
      TendstoUniformlyOn (fun n (t : ℝ) =>
        ∫ s in (0 : ℝ)..min t (ContinuousPath.exitTime D q.2).toReal,
          dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1))
              (q.2 s.toNNReal))) F atTop (Icc 0 1) := by
  obtain ⟨p, a, C, hp, ha, hm⟩ := exists_exterior_dyadic_cell_moment hh (show γ ^ 2 < 4 by nlinarith) α R
  exact ae_tendstoUniformlyOn_stopped_domain_clock_of_cell_moment hh hq0 hq2 hγ0 hγ2 hsub x hD
    hR hDR hp ha (hm x)

/-- For a nonpositive insertion and `0 < γ` with `γ ^ 2 < 2`, the full inserted clocks stopped
at the exit of a bounded domain converge locally uniformly on `[0, ∞)` to a continuous,
nonnegative and nondecreasing limit, and the exit time is finite, almost surely under the
field-path product law. -/
theorem ae_exists_locally_uniform_limit_stopped_domain_clock_nonpositive
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ ^ 2 < 2) (hα : α ≤ 0) (x : ℂ)
    {D : Set ℂ} {R : ℝ} (hR : 0 < R) (hDR : ∀ z ∈ D, ‖z‖ ≤ R) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
      ContinuousPath.exitTime D q.2 < ⊤ ∧
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D q.2).toReal,
            dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1))
                (q.2 s.toNNReal))) - F t| < η := by
  obtain ⟨p, a, C, hp, ha, hm⟩ := exists_exterior_dyadic_cell_moment hh (show γ ^ 2 < 4 by nlinarith) α R
  exact ae_exists_locally_uniform_limit_stopped_domain_clock_nonpositive_of_cell_moment hh hγ0
    hγ2 hα x hR hDR hp ha hm

/-- For a positive insertion in the range of the inner occupation estimates and `γ ^ 2 < 2`,
the full inserted clocks stopped at the exit of a bounded domain converge locally uniformly on
`[0, ∞)` to a continuous, nonnegative and nondecreasing limit, and the exit time is finite,
almost surely under the field-path product law. -/
theorem ae_exists_locally_uniform_limit_stopped_domain_clock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hq0 : 0 < γ * α) (hq2 : γ * α < 2) (hγ0 : 0 < γ) (hγ2 : γ ^ 2 < 2)
    (hsub : γ ^ 2 / 2 < 2 * (2 - γ * α) / (2 + γ * α)) (x : ℂ)
    {D : Set ℂ} {R : ℝ} (hR : 0 < R) (hDR : ∀ z ∈ D, ‖z‖ ≤ R) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
      ContinuousPath.exitTime D q.2 < ⊤ ∧
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D q.2).toReal,
            dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1))
                (q.2 s.toNNReal))) - F t| < η := by
  obtain ⟨p, a, C, hp, ha, hm⟩ := exists_exterior_dyadic_cell_moment hh (show γ ^ 2 < 4 by nlinarith) α R
  exact ae_exists_locally_uniform_limit_stopped_domain_clock_of_cell_moment hh hq0 hq2 hγ0 hγ2
    hsub x hR hDR hp ha hm

/-- For a nonpositive insertion and `0 < γ` with `γ ^ 2 < 2`, the full inserted clocks converge
locally uniformly on `[0, ∞)` to a continuous, nonnegative and nondecreasing limit, almost
surely under the field-path product law. -/
theorem ae_exists_locally_uniform_limit_clock_nonpositive
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ ^ 2 < 2) (hα : α ≤ 0) (x : ℂ) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ), dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1))
              (q.2 s.toNNReal))) - F t| < η :=
  ae_exists_locally_uniform_limit_clock_nonpositive_of_cell_moment hh hγ0 hγ2 hα x
    fun R _ => exists_exterior_dyadic_cell_moment hh (show γ ^ 2 < 4 by nlinarith) α R

/-- For a positive insertion in the range of the inner occupation estimates and `γ ^ 2 < 2`,
the full inserted clocks converge locally uniformly on `[0, ∞)` to a continuous, nonnegative and
nondecreasing limit, almost surely under the field-path product law. -/
theorem ae_exists_locally_uniform_limit_clock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hq0 : 0 < γ * α) (hq2 : γ * α < 2) (hγ0 : 0 < γ) (hγ2 : γ ^ 2 < 2)
    (hsub : γ ^ 2 / 2 < 2 * (2 - γ * α) / (2 + γ * α)) (x : ℂ) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ), dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1))
              (q.2 s.toNNReal))) - F t| < η :=
  ae_exists_locally_uniform_limit_clock_of_cell_moment hh hq0 hq2 hγ0 hγ2 hsub x
    fun R _ => exists_exterior_dyadic_cell_moment hh (show γ ^ 2 < 4 by nlinarith) α R

end HarmonicBalls
