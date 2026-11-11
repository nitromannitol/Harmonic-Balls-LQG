import HarmonicBalls.Proofs.Sec8.RootedReferenceLawDomination
import Mathlib.MeasureTheory.Integral.Prod

/-! # Measurability of root-dependent local shifts

The imported Section 6 development uses Leonardo Bonanno's whole-plane GFF
formalization.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric

/-- Pairing a jointly measurable function with a fixed continuous test is a
measurable function of the root. -/
theorem measurable_integral_test_mul_root_function
    {Z : Type*} [MeasurableSpace Z] (g : Z → ℂ → ℝ)
    (hg : Measurable (Function.uncurry g)) (φ : LQGMetric.TestC) :
    Measurable (fun z => ∫ x, φ x * g z x) := by
  have hint : Measurable (fun p : Z × ℂ => φ p.2 * g p.1 p.2) :=
    (φ.continuous.measurable.comp measurable_snd).mul hg
  exact (hint.stronglyMeasurable.integral_prod_right').measurable

/-- Measurable root-dependent functions give a jointly measurable local
mean-zero pairing process after adding their deterministic shifts. -/
theorem measurable_local_pairing_add_root_integral
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω] {U : Set ℂ}
    (X : Ω → LQGMetric.TestC0 → ℝ) (hX : Measurable X)
    (g : Z → ℂ → ℝ) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun p : Z × Ω => fun φ : Section6.LocalTest U =>
      X p.2 φ.1 + ∫ x, φ.1.1 x * g p.1 x) := by
  apply measurable_pi_iff.mpr
  intro φ
  exact ((measurable_pi_apply φ.1).comp hX |>.comp measurable_snd).add
    ((measurable_integral_test_mul_root_function g hg φ.1.1).comp measurable_fst)

/-- A translated logarithmic insertion and a fixed logarithmic insertion are
jointly measurable, including at their singular points. -/
theorem measurable_translated_log_insertions (a b : ℝ) :
    Measurable (fun p : ℂ × ℂ =>
      a * Real.log ‖p.1 + p.2‖ + b * Real.log ‖p.2‖) := by
  have hsum : Measurable (fun p : ℂ × ℂ => p.1 + p.2) :=
    measurable_fst.add measurable_snd
  exact ((Real.measurable_log.comp hsum.norm).const_mul a).add
    ((Real.measurable_log.comp measurable_snd.norm).const_mul b)

/-- Local mean-zero pairings with translated and fixed logarithmic insertions
are jointly measurable in the root and the field. -/
theorem measurable_local_pairing_add_log_insertions
    {Ω : Type*} [MeasurableSpace Ω] {U : Set ℂ}
    (X : Ω → LQGMetric.TestC0 → ℝ) (hX : Measurable X) (a b : ℝ) :
    Measurable (fun p : ℂ × Ω => fun φ : Section6.LocalTest U =>
      X p.2 φ.1 + ∫ x, φ.1.1 x *
        (a * Real.log ‖p.1 + x‖ + b * Real.log ‖x‖)) :=
  measurable_local_pairing_add_root_integral X hX
    (fun z x => a * Real.log ‖z + x‖ + b * Real.log ‖x‖)
    (measurable_translated_log_insertions a b)

/-- Global fixed-root domination implies domination of the joint local laws
after adding a common root-dependent insertion. Measurability follows from
the underlying insertion functions. -/
theorem shiftedRootReferenceLaw_local_shift_of_measurable_functions
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    (ρ : Measure Z) (P : Measure Ω) [SFinite P] {c : ℂ} {r : ℝ}
    (X : Ω → LQGMetric.TestC0 → ℝ) (hX : Measurable X)
    (f g k : Z → ℂ → ℝ)
    (hg : Measurable (Function.uncurry g)) (hk : Measurable (Function.uncurry k))
    (heq : ∀ᵐ z ∂ρ, EqOn (f z) (g z) (closedBall c r))
    (hdom : ∀ᵐ z ∂ρ,
      P.map (fun o φ => X o φ + ∫ x, φ.1 x * f z x) ≪ P.map X) :
    shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball c r) =>
        X p.2 φ.1 + (∫ x, φ.1.1 x * g p.1 x) +
          ∫ x, φ.1.1 x * k p.1 x) ≪
    shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball c r) =>
        X p.2 φ.1 + ∫ x, φ.1.1 x * k p.1 x) := by
  apply shiftedRootReferenceLaw_local_shift_domination ρ P X hX f g
    (fun z φ => ∫ x, φ.1.1 x * k z x) heq hdom
  · apply measurable_pi_iff.mpr
    intro φ
    have hfirst : Measurable (fun p : Z × Ω =>
        X p.2 φ.1 + ∫ x, φ.1.1 x * g p.1 x) :=
      (measurable_pi_apply φ).comp (measurable_local_pairing_add_root_integral X hX g hg)
    exact hfirst.add ((measurable_integral_test_mul_root_function k hk φ.1.1).comp measurable_fst)
  · exact measurable_local_pairing_add_root_integral X hX k hk

end HarmonicBalls
