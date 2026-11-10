import HarmonicBalls.Defs.LQG

/-!
# First-pass frozen inputs of the S11i chain (Lemma 11.13)

Each `def` below is an EXTERNAL fact (general GFF / LQG background, not a statement about the clusters,
odometers or harmonic balls of this paper), stated in the weakest form the first-pass proofs use.
-/

namespace HarmonicBalls

open MeasureTheory

/-- RETIRED (derived), not an input. Formerly a first-pass frozen input: measurability of the dyadic circle
averages in the centre variable. It is now derived from `IsWholePlaneGFF.ae_continuousOn_circle`
(`HarmonicBalls.SingularWeyl.ae_measurable_dyadic_circleAverage`, S11i/SingularWeyl.lean); no proof uses this `def`. -/
def CircleAverageVersionMeasurableStmt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ k : ℕ, Measurable (fun z : ℂ => hcirc ω (dyadicScale k) z)

end HarmonicBalls
