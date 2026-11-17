import HarmonicBalls.Proofs.Potential.LQGClockAnnularLimitRegularity
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! # A jointly measurable annular clock limit

For `0 < γ` with `γ ^ 2 < 2` and a fixed Brownian start, the fine-scale actual annular clocks
converge uniformly on the unit time interval, almost surely under the field-path product law.
This file represents the limit by a function that is jointly measurable in the field, the path
and the time, whose time paths are continuous, nonnegative and nondecreasing, and which is the
uniform and pointwise limit of the actual annular clocks on a measurable event of full measure.

## Main results

* `exists_measurable_stoppedAnnularClock_time`: the dyadic actual annular clocks have jointly
  measurable modifications in the field, the path and the time, with continuous time paths, that
  agree with them for all scales, paths and times off one field-null set.
* `exists_measurable_limit_stoppedAnnularClock`: the uniform limit of the actual annular clocks
  has a jointly measurable representative with continuous, nonnegative and nondecreasing time
  paths, approximated by the actual clocks on a measurable event of full measure.
-/

open MeasureTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology

namespace HarmonicBalls

/-- The dyadic actual annular clocks have modifications that are jointly measurable in the field,
the path and the unit time, have continuous time paths, and agree with the clocks for all scales,
paths and times off one field-null set. -/
theorem exists_measurable_stoppedAnnularClock_time
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α δ : ℝ) :
    ∃ M : ℕ → (Ω × ContinuousPath ℂ) × Icc (0 : ℝ) 1 → ℝ,
      (∀ k, Measurable (M k)) ∧
      (∀ k p, Continuous (fun t => M k (p, t))) ∧
      ∀ᵐ ω ∂P, ∀ (k : ℕ) (b : ContinuousPath ℂ) (t : Icc (0 : ℝ) 1),
        M k ((ω, b), t) = stoppedAnnularClock (fun z => (dyadicScale k)^(γ^2/2) *
          Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z)) δ
            (fun _ => ((t : ℝ).toNNReal)) b := by
  obtain ⟨H, hHc, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let f (k : ℕ) (ω : Ω) : ℂ → ℝ := fun z => (dyadicScale k)^(γ^2/2) *
    Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (H ω) (dyadicScale k) z)
  have hf (k : ℕ) (ω : Ω) : f k ω = fun z => (dyadicScale k)^(γ^2/2) *
      Real.exp (γ * (H ω (dyadicScale k) z - α * Real.log (max (dyadicScale k) ‖z‖))) := by
    funext z
    have hlog : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z (dyadicScale k) =
        Real.log (max (dyadicScale k) ‖z‖) := by
      simpa using LatticeProb.Gauss.circleAverage_log_norm_sub_eq z 0 (dyadicScale_pos k)
    simp only [f, LatticeProb.Gauss.fieldCircleAverage, hlog]
  have hl (k : ℕ) : Continuous fun z : ℂ => Real.log (max (dyadicScale k) ‖z‖) :=
    (continuous_const.max continuous_norm).log
      fun _ => (lt_max_of_lt_left (dyadicScale_pos k)).ne'
  have hfc (k : ℕ) (ω : Ω) : Continuous (f k ω) := by
    rw [hf k ω]
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      ((hHc ω _ (dyadicScale_pos k)).sub (continuous_const.mul (hl k)))))
  let G (k : ℕ) : Ω × ℂ → ℝ := fun q => A.indicator (f k q.1) q.2
  have hG (k : ℕ) : Measurable (G k) := by
    have hG' : G k = fun q => A.indicator (fun z => (dyadicScale k)^(γ^2/2) *
        Real.exp (γ * (H q.1 (dyadicScale k) z - α * Real.log (max (dyadicScale k) ‖z‖)))) q.2 := by
      funext q
      simp only [G, hf k q.1]
    rw [hG']
    have h1 : Measurable (fun q : Ω × ℂ => H q.1 (dyadicScale k) q.2) :=
      (hHm _ (dyadicScale_pos k)).comp measurable_swap
    apply Measurable.indicator _ (hA.preimage measurable_snd)
    exact measurable_const.mul (measurable_const.mul (h1.sub
      (measurable_const.mul ((hl k).measurable.comp measurable_snd)))).exp
  let M (k : ℕ) (q : (Ω × ContinuousPath ℂ) × Icc (0 : ℝ) 1) : ℝ :=
    stoppedAnnularClock (f k q.1.1) δ (fun _ => ((q.2 : ℝ).toNNReal)) q.1.2
  have hMt (k : ℕ) (p : Ω × ContinuousPath ℂ) : Continuous (fun t => M k (p, t)) :=
    (continuous_stoppedAnnularClock_time (f k p.1) (hfc k p.1) δ p.2).comp continuous_subtype_val
  have hMp (k : ℕ) (t : Icc (0 : ℝ) 1) : Measurable (fun p => M k (p, t)) :=
    (measurable_stopped_path_integral (G k) (hG k) (fun _ => ((t : ℝ).toNNReal))
      measurable_const).comp measurable_swap
  refine ⟨M, fun k => ?_, hMt, ?_⟩
  · exact (measurable_uncurry_of_continuous_of_measurable (u := fun t p => M k (p, t))
      (fun p => hMt k p) (hMp k)).comp measurable_swap
  · filter_upwards [hHae] with ω hω
    have hH : H ω = hcirc ω := funext fun r => funext fun z => hω r z
    intro k b t
    simp only [M, f, hH]

/-- A uniform limit is a pointwise limit. -/
private theorem tendsto_of_abs_sub_lt {ι : Type*} {A : ℕ → ι → ℝ} {F : ι → ℝ}
    (hF : ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t, |A j t - F t| < η) (t : ι) :
    Tendsto (fun j => A j t) atTop (𝓝 (F t)) :=
  Metric.tendsto_nhds.mpr fun η hη => (hF η hη).mono fun j hj => by
    rw [Real.dist_eq]
    exact hj t

/-- For each Brownian start and `γ ^ 2 < 2`, the uniform limit on the unit time interval of the
fine-scale actual annular clocks has a representative that is jointly measurable in the field, the
path and the time, whose time paths are all continuous, nonnegative and nondecreasing, and which is
the uniform and pointwise limit of the actual clocks on a measurable event of full measure under
the field-path product law. -/
theorem exists_measurable_limit_stoppedAnnularClock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (K : ℕ) (F : Ω × ContinuousPath ℂ → Icc (0 : ℝ) 1 → ℝ) (S : Set (Ω × ContinuousPath ℂ)),
      Measurable (Function.uncurry F) ∧ MeasurableSet S ∧
      (P.prod (planarBrownianMotion x)) Sᶜ = 0 ∧
      (∀ p, Continuous (F p) ∧ (∀ t, 0 ≤ F p t) ∧ Monotone (F p)) ∧
      ∀ p ∈ S,
        (∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : Icc (0 : ℝ) 1,
          |stoppedAnnularClock (fun z => (dyadicScale (j+K))^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K)) z)) δ
              (fun _ => ((t : ℝ).toNNReal)) p.2 - F p t| < η) ∧
        ∀ t : Icc (0 : ℝ) 1,
          Tendsto (fun j => stoppedAnnularClock (fun z => (dyadicScale (j+K))^(γ^2/2) *
            Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1)
              (dyadicScale (j+K)) z)) δ (fun _ => ((t : ℝ).toNNReal)) p.2)
            atTop (𝓝 (F p t)) := by
  classical
  obtain ⟨K, hK⟩ := exists_ae_continuous_monotone_limit_stoppedAnnularClock hh x hγ hγ2 α hδ
  obtain ⟨M, hMm, -, hMae⟩ := exists_measurable_stoppedAnnularClock_time hh γ α δ
  let μ := P.prod (planarBrownianMotion x)
  let C (p : Ω × ContinuousPath ℂ) (j : ℕ) (t : Icc (0 : ℝ) 1) : ℝ :=
    stoppedAnnularClock (fun z => (dyadicScale (j+K))^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K)) z)) δ
        (fun _ => ((t : ℝ).toNNReal)) p.2
  let L : (Ω × ContinuousPath ℂ) × Icc (0 : ℝ) 1 → ℝ := fun q => limUnder atTop (fun j => M (j+K) q)
  have hLm : Measurable L :=
    (StronglyMeasurable.limUnder (fun j => (hMm (j+K)).stronglyMeasurable)).measurable
  let Q (p : Ω × ContinuousPath ℂ) : Prop :=
    Continuous (fun t => L (p, t)) ∧ (∀ t, 0 ≤ L (p, t)) ∧ Monotone (fun t => L (p, t)) ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t, |C p j t - L (p, t)| < η
  have hQ : ∀ᵐ p ∂μ, Q p := by
    filter_upwards [hK, (Measure.quasiMeasurePreserving_fst (μ := P)
      (ν := planarBrownianMotion x)).ae hMae] with p hp hM
    obtain ⟨G, hGc, hG0, hGm, hG⟩ := hp
    have hLG : (fun t => L (p, t)) = G := by
      funext t
      apply Tendsto.limUnder_eq
      have hMC : (fun j => M (j+K) (p, t)) = fun j => C p j t :=
        funext fun j => hM (j+K) p.2 t
      rw [hMC]
      exact tendsto_of_abs_sub_lt hG t
    have hLG' (t : Icc (0 : ℝ) 1) : L (p, t) = G t := congrFun hLG t
    refine ⟨hLG ▸ hGc, fun t => (hLG' t) ▸ hG0 t, hLG ▸ hGm, fun η hη => ?_⟩
    filter_upwards [hG η hη] with j hj t
    rw [hLG' t]
    exact hj t
  let S : Set (Ω × ContinuousPath ℂ) := (toMeasurable μ {p | ¬ Q p})ᶜ
  have hS : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hSc : μ Sᶜ = 0 := by
    rw [compl_compl, measure_toMeasurable]
    exact ae_iff.mp hQ
  have hSQ (p : Ω × ContinuousPath ℂ) (hp : p ∈ S) : Q p :=
    by_contra fun h => hp (subset_toMeasurable _ _ h)
  let F (p : Ω × ContinuousPath ℂ) (t : Icc (0 : ℝ) 1) : ℝ := if p ∈ S then L (p, t) else 0
  have hFm : Measurable (Function.uncurry F) :=
    Measurable.ite (hS.preimage measurable_fst) hLm measurable_const
  refine ⟨K, F, S, hFm, hS, hSc, fun p => ?_, fun p hp => ?_⟩
  · by_cases hp : p ∈ S
    · obtain ⟨hc, h0, hm, -⟩ := hSQ p hp
      simp only [F, hp, ↓reduceIte]
      exact ⟨hc, h0, hm⟩
    · simp only [F, hp, ↓reduceIte]
      exact ⟨continuous_const, fun _ => le_rfl, monotone_const⟩
  · obtain ⟨-, -, -, hu⟩ := hSQ p hp
    have hFL : F p = fun t => L (p, t) := funext fun t => by simp only [F, hp, ↓reduceIte]
    rw [hFL]
    exact ⟨hu, tendsto_of_abs_sub_lt hu⟩

end HarmonicBalls
