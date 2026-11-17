import HarmonicBalls.Proofs.Potential.LQGClockAnnularConvergence
import HarmonicBalls.Proofs.Potential.LQGClockAnnularGridBound

/-! # Regularity of the annular clock limit

For `0 < γ` with `γ ^ 2 < 2` and a fixed Brownian start, the fine-scale actual annular clocks
converge uniformly on the unit time interval, almost surely under the field-path product law.
This file shows that the limit time path is continuous, nonnegative and nondecreasing.

## Main results

* `stoppedAnnularClock_nonneg`: a nonnegative density gives a nonnegative annular clock.
* `continuous_nonneg_monotone_of_uniform_limit`: continuity, nonnegativity and monotonicity pass
  to uniform limits on the unit interval.
* `exists_ae_continuous_monotone_limit_stoppedAnnularClock`: the actual annular clocks have,
  almost surely, a uniform limit on the unit interval that is continuous, nonnegative and
  nondecreasing.
-/

open MeasureTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology

namespace HarmonicBalls

/-- An annular occupation clock with a nonnegative density is nonnegative. -/
theorem stoppedAnnularClock_nonneg (f : ℂ → ℝ) (hf0 : ∀ z, 0 ≤ f z) (δ : ℝ)
    (τ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ) :
    0 ≤ stoppedAnnularClock f δ τ b :=
  integral_nonneg fun z => Set.indicator_nonneg (fun z _ => hf0 z) z

/-- A uniform limit on the unit interval of continuous, nonnegative and nondecreasing time
paths is continuous, nonnegative and nondecreasing. -/
theorem continuous_nonneg_monotone_of_uniform_limit {A : ℕ → Icc (0 : ℝ) 1 → ℝ}
    {F : Icc (0 : ℝ) 1 → ℝ} (hc : ∀ j, Continuous (A j)) (h0 : ∀ j t, 0 ≤ A j t)
    (hm : ∀ j, Monotone (A j))
    (hF : ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t, |A j t - F t| < η) :
    Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F := by
  have hu : TendstoUniformly A F atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro η hη
    filter_upwards [hF η hη] with j hj t
    rw [dist_comm, Real.dist_eq]
    exact hj t
  have hlim (t : Icc (0 : ℝ) 1) : Tendsto (fun j => A j t) atTop (𝓝 (F t)) := hu.tendsto_at t
  refine ⟨hu.continuous (Eventually.of_forall hc).frequently,
    fun t => ge_of_tendsto' (hlim t) (fun j => h0 j t), ?_⟩
  intro s t hst
  exact le_of_tendsto_of_tendsto' (hlim s) (hlim t) (fun j => hm j hst)

/-- For each Brownian start and `γ ^ 2 < 2`, almost surely under the field-path product law,
the fine-scale actual annular clocks converge uniformly on the unit time interval to a time path
that is continuous, nonnegative and nondecreasing. -/
theorem exists_ae_continuous_monotone_limit_stoppedAnnularClock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∃ F : Icc (0 : ℝ) 1 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : Icc (0 : ℝ) 1,
          |stoppedAnnularClock (fun z => (dyadicScale (j+K))^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K)) z)) δ
              (fun _ => ((t : ℝ).toNNReal)) p.2 - F t| < η := by
  obtain ⟨K, hK⟩ := exists_ae_uniform_limit_stoppedAnnularClock hh x hγ hγ2 α hδ
  have hfst := Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)
  refine ⟨K, ?_⟩
  filter_upwards [hK, hfst.ae (ae_continuous_stoppedAnnularClock_time hh γ α δ),
    hfst.ae (ae_dyadic_stoppedAnnularClock_monotone_and_cell hh γ α δ)] with p hp hc hm
  obtain ⟨F, hF⟩ := hp
  obtain ⟨hFc, hF0, hFm⟩ := continuous_nonneg_monotone_of_uniform_limit
    (A := fun j (t : Icc (0 : ℝ) 1) => stoppedAnnularClock (fun z =>
      (dyadicScale (j+K))^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K)) z)) δ
          (fun _ => ((t : ℝ).toNNReal)) p.2) (F := F)
    (fun j => (hc (j+K) p.2).comp continuous_subtype_val)
    (fun j t => stoppedAnnularClock_nonneg _ (fun z => mul_nonneg
      (Real.rpow_nonneg (dyadicScale_pos (j+K)).le _) (Real.exp_pos _).le) _ _ _)
    (fun j s t hst => (hm (j+K) p.2).1 s.2 t.2 hst) hF
  exact ⟨F, hFc, hF0, hFm, hF⟩

end HarmonicBalls
