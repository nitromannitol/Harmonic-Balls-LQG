import HarmonicBalls.Proofs.GFF.CoordinateModification

/-! # The covariance potential of a pairing of the whole-plane GFF

For `ρ : ℂ → ℝ` the covariance potential `outerPotential ρ x = ∫ ρ(y) G(x, y) dy` of `ρ` against the whole-plane
covariance kernel `G = wholePlaneCov` is the function whose pairing with a test function `ψ` is the covariance of the
pairings `(h^ℂ, ψ)` and `(h^ℂ, ρ)`:

  `Cov((h^ℂ, ψ), (h^ℂ, ρ)) = ∫ ψ(x) outerPotential ρ(x) dx`.

For a test function `ρ` it is Bonanno's logarithmic potential `∫ -log|x - y| ρ(y) dy` plus the two unit-circle
normalization terms; for a mean-zero test function the term `(∫ ρ) · log max(|x|, 1)` vanishes, so the covariance
potential is the logarithmic potential plus a constant, hence smooth on all of `ℂ`.

This is the first step (the potential of an outer test function) of the proof of the domain Markov property of the
whole-plane GFF in the form of conditional positivity (Miller-Sheffield, Imaginary Geometry IV, Proposition 2.8):
the dual elements are built from the potentials of the outer mean-zero test functions.

## Main results

* `HarmonicBalls.outerPotential`: the covariance potential.
* `HarmonicBalls.IsWholePlaneGFF.covariance_pairing_eq_integral_outerPotential`: the covariance identity.
* `HarmonicBalls.outerPotential_eq_logPot`: the formula in terms of the logarithmic potential.
* `HarmonicBalls.contDiff_outerPotential_of_integral_eq_zero`: smoothness for mean-zero test functions.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ContDiff

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The covariance potential `x ↦ ∫ ρ(y) G(x, y) dy` of `ρ` against the whole-plane covariance kernel
`G = wholePlaneCov`. -/
def outerPotential (ρ : ℂ → ℝ) (x : ℂ) : ℝ :=
  ∫ y, ρ y * wholePlaneCov x y

/-- The covariance kernel of two pairings is the pairing of the first test function with the covariance potential
of the second. -/
theorem wholePlaneGFFCov_pairing_eq_integral_outerPotential (ψ ρ : ℂ → ℝ) :
    wholePlaneGFFCov (.pairing ψ) (.pairing ρ) = ∫ x, ψ x * outerPotential ρ x :=
  rfl

/-- **Covariance potential.** For test functions `ψ` and `ρ`, the covariance of the pairings `(h^ℂ, ψ)` and
`(h^ℂ, ρ)` of the whole-plane GFF is `∫ ψ · outerPotential ρ`. -/
theorem IsWholePlaneGFF.covariance_pairing_eq_integral_outerPotential (hh : IsWholePlaneGFF P hC hcirc)
    {ψ ρ : ℂ → ℝ} (hψ : IsTestFunction Set.univ ψ) (hρ : IsTestFunction Set.univ ρ) :
    cov[fun s => hC s ψ, fun s => hC s ρ; P] = ∫ x, ψ x * outerPotential ρ x :=
  hh.covariance_eq (.pairing ψ) (.pairing ρ) hψ hρ

/-- The covariance potential of a test function is its logarithmic potential plus the unit-circle normalization
terms `(∫ ρ) · log max(|x|, 1)` and `∫ ρ(y) log max(|y|, 1) dy`. -/
theorem outerPotential_eq_logPot {ρ : ℂ → ℝ} (hρ : IsTestFunction Set.univ ρ) (x : ℂ) :
    outerPotential ρ x = LQGMetric.CircleAvg.logPot ρ x + (∫ y, ρ y) *
      LQGMetric.CircleAvg.circLog 0 1 x + ∫ y, ρ y * LQGMetric.CircleAvg.circLog 0 1 y :=
  integral_test_mul_wholePlaneCov ⟨ρ, hρ.1, hρ.2.1, Set.subset_univ _⟩ x

/-- For a mean-zero test function the covariance potential is the logarithmic potential plus a constant. -/
theorem outerPotential_eq_logPot_add_of_integral_eq_zero {ρ : ℂ → ℝ} (hρ : IsTestFunction Set.univ ρ)
    (h0 : ∫ y, ρ y = 0) (x : ℂ) :
    outerPotential ρ x = LQGMetric.CircleAvg.logPot ρ x + ∫ y, ρ y * LQGMetric.CircleAvg.circLog 0 1 y := by
  rw [outerPotential_eq_logPot hρ, h0, zero_mul, add_zero]

/-- **Smoothness.** The covariance potential of a mean-zero test function is smooth on `ℂ`. -/
theorem contDiff_outerPotential_of_integral_eq_zero {ρ : ℂ → ℝ} (hρ : IsTestFunction Set.univ ρ)
    (h0 : ∫ y, ρ y = 0) : ContDiff ℝ ∞ (outerPotential ρ) := by
  rw [show outerPotential ρ = fun x => LQGMetric.CircleAvg.logPot ρ x +
      ∫ y, ρ y * LQGMetric.CircleAvg.circLog 0 1 y from
    funext (outerPotential_eq_logPot_add_of_integral_eq_zero hρ h0)]
  exact (LQGMetric.MarkovGermVer.contDiff_logPot ⟨ρ, hρ.1, hρ.2.1, Set.subset_univ _⟩).add contDiff_const

end HarmonicBalls
