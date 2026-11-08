import HarmonicBalls.Proofs.Sec9.ExistenceResultsAssembly
import HarmonicBalls.Proofs.Sec9.ObstacleComparison

/-! # Section 9 numbered results from the three staged LQG inputs

Worker z4, task `section9-three-input-numbered-export-assembly`.

The exports below use exactly three staged LQG inputs:

* `hDG`: `WholePlaneLQGBallMassBounds` (normalized whole-plane GFF; the statement fixes insertion `0`);
* `hCC`: `LQGMeasureCoordChange P γ 0` (insertion `0`, the only scope these producers consume);
* `hE`: `LQGMeasureExistence P γ α` (all insertions `α`).

Results (Draft/Section9.lean, frozen statements):

* Lemma 9.1, `ObstacleComparisonStmt` (lemma:obstacle-comp, line 2279): unconditional, `obstacleComparison`.
* Lemmas 9.3 and 9.4, `HarmonicBallBoundarySubsetStmt` (line 2336) and `RegularOpenEqOfAEEqStmt` (line 2394):
  need only `hDG hCC hE`.
* Weak Proposition 9.2, `SubharmonicBallUniquenessWeakStmt` ([C10], operator decision E33(a)): needs, in addition,
  the typical-point leaf `h82 : TypicalPointManyGoodScalesStmt` (Lemma 8.2), an explicit binder.

Discharged inside the producers, not binders: the all-scales volume growth I2 (`LQGVolumeGrowthAllScalesStmt`),
the affine invariance of the normalized whole-plane GFF (`wholePlaneGFFAffineInvariance_proved`), the Weyl scaling
and non-atomicity of the LQG measure, and Lemma 6.11 (`VeryGoodAnnulusHarnackTypeStmt`) on the dyadic route, which is
derived from I2. No boundary-nullity binder occurs: the dyadic route to weak Proposition 9.2 uses only I2 and Lemma 8.2.

Not exported: the ordinary Proposition 9.2 (`SubharmonicBallUniquenessStmt`, line 2315). Its first conclusion
`int(closure Λ) ⊆ A` is not what the printed proof shows (Draft/Section9.lean, [C10]); only the weak statement is exported.

The frozen conclusions are used unchanged, so the carriers (`Ω : Type u`), the AE order (`∀ᵐ ω ∂P`), the Green
orientation (`greenFunction (ball 0 R) x z`) and the physical-dimension range (`0 < γ < 2`, `α₀ < lqgQ γ`) are those
of the frozen statements.

Credit: this module imports infrastructure of Leonardo Bonanno through the Lattice-Probability lean-v4.35 dependency
(LatticeProb.Bonanno), reached through `HarmonicBalls.Proofs.Sec9.ExistenceResultsAssembly` and
`HarmonicBalls.Proofs.Sec6.LQGWeylScaling`.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

section

variable
  (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    WholePlaneLQGBallMassBounds P γ hC hcirc)
  (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureCoordChange P γ 0 hC hcirc)
  (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
    LQGMeasureExistence P γ α hC hcirc)

include hDG hCC hE

/-- Lemmas 9.1, 9.3 and 9.4 from the three staged LQG inputs. No further leaf: Lemma 9.1 is unconditional,
and Lemmas 9.3 and 9.4 are consumed from `section9_comparison_lemmas_of_existence`. -/
theorem section9_comparison_results_of_three_inputs :
    ObstacleComparisonStmt.{u} ∧ HarmonicBallBoundarySubsetStmt.{u} ∧ RegularOpenEqOfAEEqStmt.{u} := by
  obtain ⟨h93, h94⟩ := section9_comparison_lemmas_of_existence hDG hCC hE
  exact ⟨obstacleComparison, h93, h94⟩

/-- Lemmas 9.1, 9.3, 9.4 and weak Proposition 9.2 from the three staged LQG inputs and the typical-point
leaf `h82` (Lemma 8.2). The ordinary Proposition 9.2 is not part of this export. -/
theorem section9_numbered_results_of_three_inputs
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ObstacleComparisonStmt.{u} ∧ HarmonicBallBoundarySubsetStmt.{u} ∧
      RegularOpenEqOfAEEqStmt.{u} ∧ SubharmonicBallUniquenessWeakStmt.{u} := by
  obtain ⟨h91, h93, h94⟩ := section9_comparison_results_of_three_inputs hDG hCC hE
  exact ⟨h91, h93, h94, subharmonicBallUniquenessWeak_of_existence hDG hCC hE h82⟩

end

end HarmonicBalls
