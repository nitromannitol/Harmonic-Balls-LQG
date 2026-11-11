import HarmonicBalls.Proofs.Sec8.LocalSmoothShiftCutoff
import HarmonicBalls.Proofs.Sec6.AnnulusLawTransfer

/-! # Local restriction of shifted field laws

A global comparison of mean-zero pairing laws can be restricted to a smaller
ball and translated by a common deterministic insertion. The imported Section 6
development uses Leonardo Bonanno's whole-plane GFF formalization.
-/

open MeasureTheory Metric Set
open scoped ContDiff

namespace HarmonicBalls

/-- If two deterministic shifts agree on a closed ball, then a global
absolute-continuity comparison for one shift restricts to the other shift on
local mean-zero tests. A further common insertion can be added to both laws.
The global comparison is an explicit premise. -/
theorem local_shifted_pairing_laws_of_global_domination
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {c : ℂ} {r : ℝ}
    (X : Ω → LQGMetric.TestC0 → ℝ) (hX : Measurable X)
    (f g : ℂ → ℝ) (heq : EqOn f g (closedBall c r))
    (k : Section6.LocalTest (ball c r) → ℝ)
    (hdom : P.map (fun o φ => X o φ + ∫ x, φ.1 x * f x) ≪ P.map X) :
    P.map (fun o (φ : Section6.LocalTest (ball c r)) =>
      X o φ.1 + (∫ x, φ.1.1 x * g x) + k φ) ≪
    P.map (fun o (φ : Section6.LocalTest (ball c r)) => X o φ.1 + k φ) := by
  let R : (LQGMetric.TestC0 → ℝ) → (Section6.LocalTest (ball c r) → ℝ) :=
    fun a φ => a φ.1
  let T : (Section6.LocalTest (ball c r) → ℝ) →
      (Section6.LocalTest (ball c r) → ℝ) := fun a φ => a φ + k φ
  let Y : Ω → LQGMetric.TestC0 → ℝ :=
    fun o φ => X o φ + ∫ x, φ.1 x * f x
  have hR : Measurable R := measurable_pi_iff.mpr fun φ => measurable_pi_apply φ.1
  have hT : Measurable T := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable (fun a : Section6.LocalTest (ball c r) → ℝ => a φ + k φ)
    have hm : Measurable (fun a : Section6.LocalTest (ball c r) → ℝ => a φ) :=
      measurable_pi_apply φ
    exact hm.add_const (k φ)
  have hY : Measurable Y := measurable_pi_iff.mpr fun φ =>
    ((measurable_pi_apply φ).comp hX).add_const _
  have hshift : ∀ φ : Section6.LocalTest (ball c r),
      (∫ x, φ.1.1 x * f x) = ∫ x, φ.1.1 x * g x := fun φ =>
    integral_mul_eq_of_eqOn_tsupport (heq.mono (φ.property.trans ball_subset_closedBall))
  have hmap := (hdom.map hR).map hT
  rw [Measure.map_map hR hY, Measure.map_map hR hX,
    Measure.map_map hT (hR.comp hY), Measure.map_map hT (hR.comp hX)] at hmap
  simpa only [Function.comp_def, T, R, Y, hshift] using hmap

/-- A locally smooth shift admits one global test-function cutoff that can
be used in every local comparison and with any common deterministic insertion. -/
theorem exists_smooth_cutoff_for_local_pairing_law
    {c : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {g : ℂ → ℝ} (hg : ContDiffOn ℝ ∞ g (ball c R)) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (X : Ω → LQGMetric.TestC0 → ℝ), Measurable X →
        P.map (fun o φ => X o φ + ∫ x, φ.1 x * f x) ≪ P.map X →
        ∀ k : Section6.LocalTest (ball c r) → ℝ,
          P.map (fun o (φ : Section6.LocalTest (ball c r)) =>
            X o φ.1 + (∫ x, φ.1.1 x * g x) + k φ) ≪
          P.map (fun o (φ : Section6.LocalTest (ball c r)) => X o φ.1 + k φ) := by
  obtain ⟨f, hf, heq⟩ := exists_testFunction_eqOn_closedBall_of_contDiffOn_ball hr hrR hg
  refine ⟨f, ⟨hf.1, hf.2.1, subset_univ _⟩, ?_⟩
  intro Ω _ P X hX hdom k
  exact local_shifted_pairing_laws_of_global_domination P X hX f g heq k hdom

end HarmonicBalls
