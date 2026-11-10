import HarmonicBalls.FirstPass.S2S3S4S9SA
import HarmonicBalls.Proofs.Sec8.GreenKernelContinuity

/-!
# Proposition 2.3 with the pole clause (fp-2-3-green-pole)

Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795), Proposition 2.3
(prop:green-properties, corrected draft line 484). The paper's Green function `G_{B_R}(x,·)` has the value `+∞` at its
pole `x` (the Newtonian kernel is `+∞` on the diagonal, Armitage–Gardiner §4.1), so `G_{B_R}(x,·) > 0` on all of `B_R`.
The Draft statement `GreenFunctionBallStmt` (Draft/Section2.lean:68) does not express this, because `greenFunction`
takes the junk value `0` on the diagonal. This file adds the pole clause without editing the frozen statement:

* `GreenFunctionBallWithPoleStmt`: `GreenFunctionBallStmt` together with the pole clause;
* `firstPass_2_3_withPole`: the proof of `GreenFunctionBallWithPoleStmt`.

The pole limit is the existing theorem `HarmonicBalls.tendsto_greenFunction_ball_pole`
(Proofs/Sec8/GreenKernelContinuity.lean:16): for `z ∈ B_R(0)`, `G_{B_R}(z,y) → +∞` as `y → z`, `y ≠ z`. It is reused,
not restated. The explicit formula `G_{B_R}(x,y) = (2π)⁻¹ log (|R² - x̄ y| / (R |x - y|))` of `greenFunction_ball`
(Proofs/Potential/GreenBall.lean) is the mechanism behind it.
-/

namespace HarmonicBalls

open Metric Filter Topology

/-- **Proposition 2.3 with the pole clause** (audit chat 204, §1). `GreenFunctionBallStmt` (Draft/Section2.lean:68)
together with `G_{B_R}(x,y) → +∞` as `y → x` for `x ∈ B_R(0)`, `y ≠ x`: the Green function takes the value `+∞` at
its pole, so `G_{B_R}(x,·) > 0` on the whole of `B_R`. -/
def GreenFunctionBallWithPoleStmt : Prop :=
  GreenFunctionBallStmt ∧
    ∀ R : ℝ, 0 < R → ∀ x ∈ ball (0 : ℂ) R, Tendsto (greenFunction (ball 0 R) x) (𝓝[≠] x) atTop

/-- Proposition 2.3 with the pole clause: the Draft statement `firstPass_2_3` (FirstPass/S2S3S4S9SA.lean:41) and the
pole limit `tendsto_greenFunction_ball_pole` (Proofs/Sec8/GreenKernelContinuity.lean:16). -/
theorem firstPass_2_3_withPole : GreenFunctionBallWithPoleStmt :=
  ⟨firstPass_2_3, fun _ _ _ hx => tendsto_greenFunction_ball_pole hx⟩

end HarmonicBalls
