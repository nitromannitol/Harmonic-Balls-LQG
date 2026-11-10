import HarmonicBalls.Defs.GFF

/-!
# Total mass of the whole-plane GFF (FIRST-PASS, Chat 224 Correction 2)

The probability-space interface of the rooted, Campbell and Birkhoff argument needs the carrier measure `P` of a
whole-plane Gaussian free field to be a probability measure (Duplantier-Sheffield 2011, Section 2.1; Harmonic balls
in LQG, arXiv:2208.11795, Section 2.1). Under the definition `IsWholePlaneGFF P hC hcirc`
(`HarmonicBalls/Defs/GFF.lean`) this is already proved there as `IsWholePlaneGFF.isProbabilityMeasure`, from the
Gaussian clause `isGaussianProcess` at the admissible observable `circle 1 0`. This file restates that theorem under
the name requested by the operator. It adds no mathematics.
-/

open MeasureTheory
open HarmonicBalls

namespace FirstPassS11i

/-- Total mass one: under `IsWholePlaneGFF P hC hcirc` the measure `P` is a probability measure. The only clause of
the definition used is the Gaussian clause `isGaussianProcess` (`IsWholePlaneGFF.isProbabilityMeasure`). -/
theorem isProbabilityMeasure_of_isWholePlaneGFF {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) :
    IsProbabilityMeasure P :=
  h.isProbabilityMeasure

end FirstPassS11i
