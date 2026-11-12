import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import LatticeProb.LQG.LQGMeasureInputs

/-!
# LP bridge for the ball-mass bounds of the whole-plane LQG measure

`HarmonicBalls.wholePlaneLQGBallMassBounds_of_LP` transports the LP statement
`LatticeProb.LQG.WholePlaneLQGBallMassBoundsLP` (LatticeProb/LQG/LQGMeasureInputs.lean) to the HB statement
`WholePlaneLQGBallMassBounds` (Proposed/LQG.lean:172; Ding-Gwynne 2019, Lemma 3.8). It is the reverse of
`wholePlaneLQGBallMassBoundsLP_of_HB` (FirstPass/Phase2/DerivedInputs30.lean:35): `PolyHighProb` has identical bodies
in both copies, and `IsWholePlaneGFF`, `IsLQGMeasureOfField` are transported by the bridge equivalences
`isWholePlaneGFF_iff` (M1) and `isLQGMeasureOfField_iff` (M4).
-/

open MeasureTheory

universe u

namespace HarmonicBalls

/-- The ball-mass bounds of the whole-plane γ-LQG measure (Ding-Gwynne 2019, Lemma 3.8) in HB form, from the LP form. -/
theorem wholePlaneLQGBallMassBounds_of_LP {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (h : LatticeProb.LQG.WholePlaneLQGBallMassBoundsLP P γ hC hcirc) :
    WholePlaneLQGBallMassBounds P γ hC hcirc := by
  intro hG hγ hγ2 μ hμ βl βu h1 h2 h3
  exact h ((LPBridge.isWholePlaneGFF_iff P hC hcirc).1 hG) hγ hγ2 μ
    ((LPBridge.isLQGMeasureOfField_iff P γ 0 hcirc μ).1 hμ) βl βu h1 h2 h3

/-- The universe-`u` family of LP ball-mass bounds gives the family of HB ball-mass bounds, in the binder shape `hDG`
of the counted forms. -/
theorem wholePlaneLQGBallMassBounds_forall_of_LP
    (h : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LatticeProb.LQG.WholePlaneLQGBallMassBoundsLP P γ hC hcirc)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) : WholePlaneLQGBallMassBounds P γ hC hcirc :=
  wholePlaneLQGBallMassBounds_of_LP P γ hC hcirc (h Ω P γ hC hcirc)

end HarmonicBalls
