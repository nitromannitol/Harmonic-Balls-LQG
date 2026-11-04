import HarmonicBalls.Defs.Brownian
import MarkovProcess.Examples.BrownianMotion
import MarkovProcess.Path.MeasureIdentification
import MarkovProcess.FiniteTime.MeasureFiniteRestrictionIdentification
import Mathlib.Probability.BrownianMotion.Basic

/-! # Real Brownian scaling

The centered canonical Brownian motion from MarkovProcess satisfies Mathlib's
finite-dimensional characterization, so Mathlib's scaling theorem applies.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory MarkovProcess

/-- Finite-dimensional distributions determine finite measures on real
continuous-path space. -/
theorem real_path_measure_eq_of_finite_dimensional_laws
    (μ ν : Measure (ContinuousPath ℝ)) [IsFiniteMeasure μ]
    (h : ∀ I : Finset NNReal,
      μ.map (fun ω : ContinuousPath ℝ => I.restrict (fun t => ω t)) =
        ν.map (fun ω : ContinuousPath ℝ => I.restrict (fun t => ω t))) : μ = ν := by
  let eval : ContinuousPath ℝ → NNReal → ℝ := fun ω t => ω t
  have heval : Measurable eval := Measurable.of_eval fun t =>
    ContinuousPath.measurable_coordinateProcess t
  have hfull : μ.map eval = ν.map eval := by
    apply MarkovProcess.Measure.eq_of_map_finiteRestriction_eq
    intro I
    have hI : Measurable (I.restrict : (NNReal → ℝ) → I → ℝ) :=
      Measurable.of_eval fun _ => measurable_pi_apply _
    rw [Measure.map_map hI heval, Measure.map_map hI heval]
    exact h I
  let restrict : (NNReal → ℝ) → DenseTime → ℝ := fun ω t => ω (DenseTime.castOrderEmbedding t)
  have hrestrict : Measurable restrict := Measurable.of_eval fun _ => measurable_pi_apply _
  have hdense := congrArg (fun ρ : Measure (NNReal → ℝ) => ρ.map restrict) hfull
  rw [Measure.map_map hrestrict heval, Measure.map_map hrestrict heval] at hdense
  apply MarkovProcess.Measure.map_denseRestriction_injective
  exact hdense

/-- The centered MarkovProcess Brownian motion has Mathlib's finite-dimensional
Brownian laws. -/
theorem isPreBrownianReal_brownianMotion (x : ℝ) :
    ProbabilityTheory.IsPreBrownianReal
      (fun (t : NNReal) (ω : ContinuousPath ℝ) => ω t - x) (brownianMotion x) := by
  apply ProbabilityTheory.HasIndepIncrements.isPreBrownianReal_of_hasLaw
  · exact (MarkovProcess.isBrownianReal_brownianMotion x).hasLaw_eval
  · exact (MarkovProcess.isBrownianReal_brownianMotion x).hasIndepIncrements

/-- Brownian scaling for the centered real canonical process. -/
theorem isPreBrownianReal_scaled_brownianMotion (x : ℝ) {c : NNReal} (hc : c ≠ 0) :
    ProbabilityTheory.IsPreBrownianReal
      (fun (t : NNReal) (ω : ContinuousPath ℝ) =>
        (Real.sqrt c)⁻¹ * (ω (c * t) - x)) (brownianMotion x) :=
  (isPreBrownianReal_brownianMotion x).smul hc

/-- All finite-dimensional laws of the scaled centered process coincide with
those of real Brownian motion started at zero. -/
theorem scaled_brownianMotion_finite_dimensional_law
    (x : ℝ) {c : NNReal} (hc : c ≠ 0) (I : Finset NNReal) :
    (brownianMotion x).map (fun ω => I.restrict (fun t =>
        (Real.sqrt c)⁻¹ * (ω (c * t) - x))) =
      (brownianMotion 0).map (fun ω => I.restrict (fun t => ω t)) := by
  calc
    _ = ProbabilityTheory.BrownianReal.projectiveFamily I :=
      ((isPreBrownianReal_scaled_brownianMotion x hc).hasLaw I).map_eq
    _ = _ := by
      simpa only [sub_zero] using (((isPreBrownianReal_brownianMotion 0).hasLaw I).map_eq).symm

/-- Recenter, rescale time, and normalize a real continuous path. -/
noncomputable def scaledCenteredRealPath (x : ℝ) (c : NNReal)
    (ω : ContinuousPath ℝ) : ContinuousPath ℝ :=
  ⟨fun t => (Real.sqrt c)⁻¹ * (ω (c * t) - x), by fun_prop⟩

theorem continuous_scaledCenteredRealPath (x : ℝ) (c : NNReal) :
    Continuous (scaledCenteredRealPath x c) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  show Continuous (fun q : ContinuousPath ℝ × NNReal =>
    (Real.sqrt c)⁻¹ * (q.1 (c * q.2) - x))
  fun_prop

/-- The scaled centered real Brownian path has the law of Brownian motion
started at zero. -/
theorem brownianMotion_map_scaledCenteredRealPath
    (x : ℝ) {c : NNReal} (hc : c ≠ 0) :
    (brownianMotion x).map (scaledCenteredRealPath x c) = brownianMotion 0 := by
  apply real_path_measure_eq_of_finite_dimensional_laws
  intro I
  have hI : Measurable (fun ω : ContinuousPath ℝ => I.restrict (fun t => ω t)) :=
    Measurable.of_eval fun _ => ContinuousPath.measurable_coordinateProcess _
  rw [Measure.map_map hI (continuous_scaledCenteredRealPath x c).measurable]
  exact scaled_brownianMotion_finite_dimensional_law x hc I

end HarmonicBalls.Section6
