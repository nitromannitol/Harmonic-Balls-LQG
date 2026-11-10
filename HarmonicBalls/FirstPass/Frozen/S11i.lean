import HarmonicBalls.Defs.LQG

/-!
# First-pass frozen inputs of the S11i chain (Lemma 11.13)

Each `def` below is an EXTERNAL fact (general GFF / LQG background, not a statement about the clusters,
odometers or harmonic balls of this paper), stated in the weakest form the first-pass proofs use.
-/

namespace HarmonicBalls

open MeasureTheory

/-- FIRST-PASS FROZEN. Measurability of the dyadic circle averages of the whole-plane GFF in the centre
variable. Almost surely, for every dyadic radius `2^{-k}`, the map `z ↦ hcirc ω (2^{-k}) z` is measurable.
Source: standard; locator pending (the whole-plane GFF circle averages `h_r(z)`, `r > 0`, admit a version
continuous in `z`; this is the version convention under which the LQG approximations are measurable densities).
Used by: `HarmonicBalls.SingularWeyl.singular_weyl_measure_ae` (S11i/SingularWeyl.lean). -/
def CircleAverageVersionMeasurableStmt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ k : ℕ, Measurable (fun z : ℂ => hcirc ω (dyadicScale k) z)

end HarmonicBalls
