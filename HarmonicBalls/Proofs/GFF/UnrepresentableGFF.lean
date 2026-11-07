import HarmonicBalls.Defs.StrongMetricSpaces
import HarmonicBalls.Proofs.GFF.CoordinateModification

/-!
# Distribution representation of GFF versions

A coordinatewise version of a whole-plane GFF need not admit a simultaneous
samplewise distribution representation. The construction is conditional on an
existing GFF and preserves every fixed-test pairing almost surely.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Distributions

/-- A product extension of any project GFF has a coordinatewise version that is
not represented by a distribution at almost every sample. -/
theorem IsWholePlaneGFF.product_has_ae_unrepresentable_modification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) :
    ∃ hC' : Ω × ℝ → (ℂ → ℝ) → ℝ,
      IsWholePlaneGFF (P.prod (gaussianReal 0 1)) hC' (fun p => hcirc p.1) ∧
      (∀ φ, (fun p : Ω × ℝ => hC p.1 φ) =ᵐ[P.prod (gaussianReal 0 1)] (fun p => hC' p φ)) ∧
      ∀ᵐ p ∂P.prod (gaussianReal 0 1), ¬ ∃ distribution : PlaneDistribution,
        RepresentsPlaneDistribution (hC' p) distribution := by
  obtain ⟨hC', hg, he, hn⟩ := hh.product_has_ae_non_linear_modification
  refine ⟨hC', hg, he, ?_⟩
  filter_upwards [hn] with p ⟨φ, hφ, hnot⟩
  rintro ⟨distribution, hrep⟩
  let test : TestFunction (⊤ : Opens ℂ) ℝ ⊤ := ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩
  apply hnot
  have htest := hrep test
  have hdouble := hrep ((2 : ℝ) • test)
  change hC' p φ = distribution test at htest
  change hC' p (fun z => 2 * φ z) = distribution ((2 : ℝ) • test) at hdouble
  rw [hdouble, htest, map_smul]
  rfl

#print axioms IsWholePlaneGFF.product_has_ae_unrepresentable_modification

end HarmonicBalls
