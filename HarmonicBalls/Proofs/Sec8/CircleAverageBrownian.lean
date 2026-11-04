import HarmonicBalls.Proofs.Sec8.GaussianGerm
import Mathlib.Probability.BrownianMotion.Basic

/-! # The radial circle-average process -/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace HarmonicBalls

/-- The circle average at radius `exp(-t)`, parametrized by logarithmic scale. -/
noncomputable def radialCircleAverage {Ω : Type*} (hcirc : Ω → ℝ → ℂ → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ := hcirc ω (Real.exp (-(t : ℝ))) 0

/-- The logarithmically parametrized circle averages of a normalized
whole-plane GFF have the finite-dimensional distributions of Brownian motion. -/
theorem IsWholePlaneGFF.radialCircleAverage_isPreBrownianReal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) :
    IsPreBrownianReal (radialCircleAverage hcirc) P := by
  have hg : IsGaussianProcess (radialCircleAverage hcirc) P := by
    let o : ℝ≥0 → GFFObservable.Admissible := fun t =>
      ⟨.circle (Real.exp (-(t : ℝ))) 0, Real.exp_pos _⟩
    exact h.isGaussianProcess.comp_right o
  apply hg.isPreBrownianReal_of_covariance
  · intro t
    exact h.integral_eq_zero (.circle (Real.exp (-(t : ℝ))) 0) (Real.exp_pos _)
  · intro s t hst
    have hr : 0 < Real.exp (-(t : ℝ)) := Real.exp_pos _
    have hs : 0 < Real.exp (-(s : ℝ)) := Real.exp_pos _
    have hrs : Real.exp (-(t : ℝ)) ≤ Real.exp (-(s : ℝ)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (show (s : ℝ) ≤ (t : ℝ) from hst)
    have hs1 : Real.exp (-(s : ℝ)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr s.coe_nonneg)
    rw [covariance_comm]
    change cov[fun ω => hcirc ω (Real.exp (-(t : ℝ))) 0,
      fun ω => hcirc ω (Real.exp (-(s : ℝ))) 0; P] = (s : ℝ)
    have hc := h.covariance_eq (.circle (Real.exp (-(t : ℝ))) 0)
      (.circle (Real.exp (-(s : ℝ))) 0) hr hs
    change cov[fun ω => hcirc ω (Real.exp (-(t : ℝ))) 0,
      fun ω => hcirc ω (Real.exp (-(s : ℝ))) 0; P] = _ at hc
    rw [hc, wholePlaneGFFCov_concentric_circles hr hs hrs hs1, Real.log_exp, neg_neg]

/-- Radial circle averages have independent increments on logarithmic scales. -/
theorem IsWholePlaneGFF.radialCircleAverage_hasIndepIncrements
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) :
    HasIndepIncrements (radialCircleAverage hcirc) P :=
  h.radialCircleAverage_isPreBrownianReal.hasIndepIncrements

/-- Consecutive unit-time increments of the radial circle-average process. -/
noncomputable def radialCircleIncrement {Ω : Type*} (hcirc : Ω → ℝ → ℂ → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  radialCircleAverage hcirc (n + 1 : ℕ) ω - radialCircleAverage hcirc (n : ℕ) ω

/-- Consecutive logarithmic-scale circle-average increments are independent. -/
theorem IsWholePlaneGFF.iIndepFun_radialCircleIncrement
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) : iIndepFun (radialCircleIncrement hcirc) P := by
  have hm : Monotone (fun n : ℕ => (n : ℝ≥0)) := by
    intro a b hab
    change (a : ℝ≥0) ≤ (b : ℝ≥0)
    exact_mod_cast hab
  change iIndepFun (fun n ω => radialCircleAverage hcirc (n + 1 : ℕ) ω -
    radialCircleAverage hcirc (n : ℕ) ω) P
  simpa only [Nat.cast_add, Nat.cast_one] using
    (h.radialCircleAverage_hasIndepIncrements.nat hm)

/-- Every event in the tail of the unit-time radial circle-average increments
has probability zero or one. This is only the radial part of the GFF germ. -/
theorem IsWholePlaneGFF.radialCircleIncrement_tail_trivial
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (A : Set Ω)
    (hA : ∀ n, MeasurableSet[⨆ k ≥ n,
      MeasurableSpace.comap (radialCircleIncrement hcirc k) inferInstance] A) :
    P A = 0 ∨ P A = 1 := by
  let layers : ℕ → MeasurableSpace Ω := fun k =>
    MeasurableSpace.comap (radialCircleIncrement hcirc k) inferInstance
  have hle : ∀ k, layers k ≤ mΩ := by
    intro k
    apply Measurable.comap_le
    apply Measurable.sub
    · exact h.measurable_circle _ _ (Real.exp_pos _)
    · exact h.measurable_circle _ _ (Real.exp_pos _)
  apply measure_zero_or_one_of_measurableSet_limsup_atTop hle
    h.iIndepFun_radialCircleIncrement.iIndep
  rw [Filter.limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
  exact hA

end HarmonicBalls
