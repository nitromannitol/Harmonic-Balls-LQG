import HarmonicBalls.Defs.GFF

/-!
# A whole-plane GFF is a probability measure (task fp-S11af-gff-probability, n4; for n3, item 1(b))

`IsWholePlaneGFF P hC hcirc` (`HarmonicBalls/Defs/GFF.lean`, Duplantier-Sheffield 2011, Section 3.1) does not list
`IsProbabilityMeasure P` among its clauses. This file shows that the probability property is already implied by the clause
`isGaussianProcess`, so no hypothesis is added.

Argument. Mathlib's `ProbabilityTheory.IsGaussianProcess X P` (`Probability/Distributions/Gaussian/IsGaussianProcess/Def.lean`)
says that for every finite index set `I` the restriction `I.restrict (X · ω)` has a Gaussian law under `P`
(`ProbabilityTheory.HasGaussianLaw`: almost sure measurability, and `P.map` is an `IsGaussian` measure). An `IsGaussian`
measure is a probability measure (`IsGaussian.toIsProbabilityMeasure`), and `HasGaussianLaw.isProbabilityMeasure` transfers
this to `P`, since the map is AE measurable: `P univ = (P.map _) univ = 1`. We use the empty finite family `I = ∅`; its
law lives on the one-point type `↥∅ → ℝ`. Any finite family gives the same conclusion, and the empty one needs no observable.
-/

open HarmonicBalls MeasureTheory ProbabilityTheory

namespace FirstPassS11af

/-- Total mass one: under `IsWholePlaneGFF P hC hcirc` the measure `P` is a probability measure. The only input used is the
clause `isGaussianProcess`, at the empty finite family of observables. -/
theorem isProbabilityMeasure_of_isWholePlaneGFF {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) :
    IsProbabilityMeasure P :=
  (h.isGaussianProcess.hasGaussianLaw (∅ : Finset GFFObservable.Admissible)).isProbabilityMeasure

end FirstPassS11af
