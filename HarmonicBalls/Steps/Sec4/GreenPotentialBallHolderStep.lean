import HarmonicBalls.Defs.Obstacle

/-!
# Gap G4: the quantitative Green clause of Proposition 2.5 on a disc

Lemma 4.2 (odometer:cont, line 721) asks for one random constant `C` with `|v^z_t(x) - v^z_t(y)| ≤ C |x - y|^α`
for all `t > 0` and `z ∈ B_1`. The proof (lines 730-733) writes `v^z_t` as minus the `G_{B_1}`-potential of
`μ_h|_Λ + ν|_{∂Λ}`, a measure with density in `[0,1]` with respect to `μ_h` (Lemma 3.2), and applies
Proposition 2.5. As printed (and as `GreenPotentialLiouvilleHolderStmt`, Draft/Section2.lean), Proposition 2.5 gives
a Hölder constant for each `f` separately, which does not give a constant uniform in `t` and `z`
(docs/campaign/GRAPH.md G4). The proof of Proposition 2.5 gives more: a Hölder seminorm `≤ C ‖f‖_∞` with `C`
depending on `μ` only. This file states that quantitative form for `O = B_R` as the step `GreenPotentialBallHolderStep`.

The step is discharged in Lean: its body is verbatim `VolumeGrowth.greenPotential_ball_holder`
(Proofs/Potential/GreenPotentialHolder.lean; exponent `greenPotentialHolderExponent β⁺ = min (β⁺, 1) / 2`), see
`greenPotentialBallHolderStep` in Steps/Sec4/GreenPotentialBallHolder.lean. That proof file cannot be imported
together with Appendix A's steps (Steps/SecA/Basic.lean and Proofs/Potential/GreenBall.lean both declare
`HarmonicBalls.continuousOn_greenFunction_ball`), so the reduction of Lemma 4.2 takes the step as a hypothesis. This
file imports only `Defs/Obstacle.lean`, so that both sides can import it.
-/

namespace HarmonicBalls

open MeasureTheory Metric

/-- **Step G4 (Proposition 2.5, Green clause, quantitative form, for `O = B_R`).** Let `μ` be a Radon measure
satisfying the volume growth condition eq:volume-growth on `B_R`. There is `C ≥ 0` such that for every `f`
measurable with `|f| ≤ M` `μ`-a.e. on `B_R`, the Green potential `x ↦ ∫_{B_R} G_{B_R}(x,y) f(y) μ(dy)` converges
absolutely on `closedBall 0 R` and is Hölder there with exponent `min (β⁺, 1) / 2` and constant `C M`. The exponent
depends on `β⁺` only and `C` does not depend on `f`. Proved: `greenPotentialBallHolderStep`
(Steps/Sec4/GreenPotentialBallHolder.lean). -/
def GreenPotentialBallHolderStep : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℂ → ℝ) (M : ℝ), AEStronglyMeasurable f (μ.restrict (ball 0 R)) → 0 ≤ M →
      (∀ᵐ y ∂μ.restrict (ball 0 R), |f y| ≤ M) →
      (∀ x ∈ closedBall (0 : ℂ) R,
        IntegrableOn (fun y => greenFunction (ball 0 R) x y * f y) (ball 0 R) μ) ∧
      ∀ x ∈ closedBall (0 : ℂ) R, ∀ x' ∈ closedBall (0 : ℂ) R,
        |∫ y in ball 0 R, greenFunction (ball 0 R) x y * f y ∂μ -
            ∫ y in ball 0 R, greenFunction (ball 0 R) x' y * f y ∂μ| ≤
          C * M * ‖x - x'‖ ^ (min βplus 1 / 2)

end HarmonicBalls
