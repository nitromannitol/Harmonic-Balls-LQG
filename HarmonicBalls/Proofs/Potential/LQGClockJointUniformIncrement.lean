import HarmonicBalls.Proofs.Potential.LQGClockExactUniformIncrement
import HarmonicBalls.Proofs.GFF.JointLogInsertionCircleProfile

/-! # Jointly measurable uniform clock increments

The exact uniform increment is measurable jointly in the field parameter and path.
-/

namespace HarmonicBalls

open MeasureTheory Set MarkovProcess
open scoped NNReal ENNReal Interval

/-- Joint measurability and finiteness of the exact uniform clock increment. -/
theorem measurable_lqgClock_exact_uniform_increment_joint
    {Ω : Type*} [MeasurableSpace Ω] {γ : ℝ} {hε : Ω → ℝ → ℂ → ℝ} (N k : ℕ)
    (hm₁ : Measurable fun p : Ω × ℂ => hε p.1 (dyadicScale (k + 1)) p.2)
    (hm₀ : Measurable fun p : Ω × ℂ => hε p.1 (dyadicScale k) p.2)
    (hc₁ : ∀ ω, Continuous (hε ω (dyadicScale (k + 1))))
    (hc₀ : ∀ ω, Continuous (hε ω (dyadicScale k))) :
    Measurable (fun p : Ω × ContinuousPath ℂ =>
      ⨆ t : Iic (N : ℝ≥0), ENNReal.ofReal
        |lqgClockApprox γ (hε p.1) (dyadicScale (k + 1)) p.2 t -
          lqgClockApprox γ (hε p.1) (dyadicScale k) p.2 t|) ∧
    ∀ p : Ω × ContinuousPath ℂ,
      (⨆ t : Iic (N : ℝ≥0), ENNReal.ofReal
        |lqgClockApprox γ (hε p.1) (dyadicScale (k + 1)) p.2 t -
          lqgClockApprox γ (hε p.1) (dyadicScale k) p.2 t|) ≠ ∞ := by
  let f : (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun p s =>
    dyadicScale (k + 1) ^ (γ ^ 2 / 2) * Real.exp (γ * hε p.1 (dyadicScale (k + 1)) (p.2 s.toNNReal)) -
    dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε p.1 (dyadicScale k) (p.2 s.toNNReal))
  have hev : Measurable fun p : (Ω × ContinuousPath ℂ) × ℝ => p.1.2 p.2.toNNReal :=
    (continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable.comp
      (measurable_fst.snd.prodMk measurable_snd)
  have hf : Measurable (Function.uncurry f) := by
    dsimp [f, Function.uncurry]
    exact (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul
      (hm₁.comp (measurable_fst.fst.prodMk hev))))).sub
      (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul
      (hm₀.comp (measurable_fst.fst.prodMk hev)))))
  have hfc (p : Ω × ContinuousPath ℂ) : Continuous (f p) := by
    dsimp [f]
    exact (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      ((hc₁ p.1).comp (p.2.continuous.comp continuous_real_toNNReal))))).sub
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      ((hc₀ p.1).comp (p.2.continuous.comp continuous_real_toNNReal)))))
  have heq (p : Ω × ContinuousPath ℂ) (t : ℝ≥0) :
      lqgClockApprox γ (hε p.1) (dyadicScale (k + 1)) p.2 t -
        lqgClockApprox γ (hε p.1) (dyadicScale k) p.2 t = ∫ s in (0 : ℝ)..(t : ℝ), f p s := by
    have h1 : IntervalIntegrable (fun s => dyadicScale (k + 1) ^ (γ ^ 2 / 2) *
        Real.exp (γ * hε p.1 (dyadicScale (k + 1)) (p.2 s.toNNReal))) volume 0 t :=
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
        ((hc₁ p.1).comp (p.2.continuous.comp continuous_real_toNNReal))))).intervalIntegrable _ _
    have h0 : IntervalIntegrable (fun s => dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * hε p.1 (dyadicScale k) (p.2 s.toNNReal))) volume 0 t :=
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
        ((hc₀ p.1).comp (p.2.continuous.comp continuous_real_toNNReal))))).intervalIntegrable _ _
    exact (intervalIntegral.integral_sub h1 h0).symm
  let q : Iic (N : ℝ≥0) → (Ω × ContinuousPath ℂ) → ℝ := fun t p =>
    |lqgClockApprox γ (hε p.1) (dyadicScale (k + 1)) p.2 t -
      lqgClockApprox γ (hε p.1) (dyadicScale k) p.2 t|
  have hqm (t : Iic (N : ℝ≥0)) : Measurable (q t) := by
    have hi : Measurable (fun p => ∫ s in (0 : ℝ)..((t : ℝ≥0) : ℝ), f p s) := by
      rw [show (fun p => ∫ s in (0 : ℝ)..((t : ℝ≥0) : ℝ), f p s) =
          (fun p => ∫ s in Ioc (0 : ℝ) ((t : ℝ≥0) : ℝ), f p s) by
          funext p; rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t)] ]
      exact hf.stronglyMeasurable.integral_prod_right.measurable
    convert hi.abs using 1
    funext p
    exact congrArg abs (heq p t)
  have hqc (p : Ω × ContinuousPath ℂ) : Continuous (fun t => q t p) := by
    have hc : Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t, f p s) :=
      intervalIntegral.continuous_primitive (fun a c => (hfc p).intervalIntegrable a c) 0
    have ht : Continuous (fun t : Iic (N : ℝ≥0) => ((t : ℝ≥0) : ℝ)) :=
      continuous_subtype_val.comp continuous_subtype_val
    have h := (hc.comp ht).abs
    convert h using 1
    funext t
    exact congrArg abs (heq p t)
  constructor
  · convert measurable_iSup_of_lowerSemicontinuous
      (fun t => ENNReal.measurable_ofReal.comp (hqm t))
      (fun p => (ENNReal.continuous_ofReal.comp (hqc p)).lowerSemicontinuous) using 1
    ext p
    simp only [q, iSup_apply, Function.comp_apply]
  · intro p
    obtain ⟨A, _, _, hA⟩ := exists_measurable_lqgClock_uniform_increment_bound N k (hc₁ p.1) (hc₀ p.1)
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    apply iSup_le
    intro t
    exact ENNReal.ofReal_le_ofReal (hA p.2 t t.property)

private theorem measurable_inserted_profile_scale
    {Ω : Type*} [MeasurableSpace Ω] {F : Ω → C(CircleParameter, ℝ)}
    (hFm : Measurable F) (α : ℝ) (j : ℕ) :
    Measurable (fun p : Ω × ℂ =>
      circleProfile (logInsertedCircleProfile (F p.1) α 0) (dyadicScale j) p.2) := by
  have hG : Measurable (fun ω => logInsertedCircleProfile (F ω) α 0) :=
    measurable_logInsertedCircleProfile_random hFm measurable_const measurable_const
  have h := measurable_circle_version_joint hG
  have hp : Measurable (fun p : Ω × ℂ =>
      (p.1, ((⟨dyadicScale j, dyadicScale_pos j⟩ : Set.Ioi (0 : ℝ)), p.2))) :=
    measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
  convert h.comp hp using 1
  funext p
  simp only [Function.comp_apply, circleProfile, dite_eq_left (dyadicScale_pos j)]

private theorem continuous_inserted_profile_scale (F : C(CircleParameter, ℝ)) (α : ℝ) (j : ℕ) :
    Continuous (fun z => circleProfile (logInsertedCircleProfile F α 0) (dyadicScale j) z) := by
  convert (logInsertedCircleProfile F α 0).continuous.comp
      (continuous_const.prodMk continuous_id : Continuous (fun z : ℂ =>
        ((⟨dyadicScale j, dyadicScale_pos j⟩ : Set.Ioi (0 : ℝ)), z))) using 1
  funext z
  simp only [Function.comp_apply, circleProfile, dite_eq_left (dyadicScale_pos j)]

/-- A measurable continuous inserted GFF version gives a jointly measurable exact
uniform clock increment and agrees with the raw inserted field at every positive scale. -/
theorem IsWholePlaneGFF.exists_joint_measurable_inserted_clock_increment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (α γ : ℝ) (N k : ℕ) :
    ∃ F : Ω → C(CircleParameter, ℝ), Measurable F ∧
      (∀ᵐ ω ∂P, ∀ r z, 0 < r →
        circleProfile (logInsertedCircleProfile (F ω) α 0) r z =
          fieldCircleAverage α (hcirc ω) r z) ∧
      Measurable (fun p : Ω × ContinuousPath ℂ =>
        ⨆ t : Iic (N : ℝ≥0), ENNReal.ofReal
          |lqgClockApprox γ (circleProfile (logInsertedCircleProfile (F p.1) α 0))
              (dyadicScale (k + 1)) p.2 t -
            lqgClockApprox γ (circleProfile (logInsertedCircleProfile (F p.1) α 0))
              (dyadicScale k) p.2 t|) ∧
      ∀ p : Ω × ContinuousPath ℂ,
        (⨆ t : Iic (N : ℝ≥0), ENNReal.ofReal
          |lqgClockApprox γ (circleProfile (logInsertedCircleProfile (F p.1) α 0))
              (dyadicScale (k + 1)) p.2 t -
            lqgClockApprox γ (circleProfile (logInsertedCircleProfile (F p.1) α 0))
              (dyadicScale k) p.2 t|) ≠ ∞ := by
  obtain ⟨F, hFm, _, hF⟩ := hh.exists_measurable_continuous_circle_version
  have hb := measurable_lqgClock_exact_uniform_increment_joint
    (γ := γ) (hε := fun ω => circleProfile (logInsertedCircleProfile (F ω) α 0)) N k
    (measurable_inserted_profile_scale hFm α (k + 1))
    (measurable_inserted_profile_scale hFm α k)
    (fun ω => continuous_inserted_profile_scale (F ω) α (k + 1))
    (fun ω => continuous_inserted_profile_scale (F ω) α k)
  refine ⟨F, hFm, ?_, hb⟩
  filter_upwards [hh.ae_logInsertedCircleProfile_eq_raw hF] with ω hω r z hr
  rw [circleProfile, dite_eq_left hr, hω α 0, fieldCircleAverage_eq α (hcirc ω) hr]
  simp

end HarmonicBalls
