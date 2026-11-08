import Mathlib

/-! # Literature input: Miller-Sheffield, Imaginary Geometry IV, Proposition 2.9 (proposed)

Source: J. Miller and S. Sheffield, *Imaginary Geometry IV: interior rays, whole-plane reversibility, and
space-filling trees*, arXiv:1302.4738v2, Section 2.1, Proposition 2.9, printed page 49 (the statement was read from
the text layer of arXiv:1302.4738v2 at page 49; operator source-check pending).

Source setting (lines 1891-1897 and 1915-1918 of the text layer): `H` is the Hilbert space closure of `H_s` modulo a
global additive constant, with the Dirichlet inner product `(f, g)_∇ = (2π)^{-1} ∫ ∇f · ∇g`. A whole-plane GFF `h`
is a Gaussian on `H`: random variables `(h, f)_∇`, `f ∈ H`, jointly Gaussian with covariance `(f, g)_∇`. The
statement quantifies over an arbitrary real inner product space `H` (the Dirichlet space is an instance), and
`(h, f)_∇` is the family `X f` of a Gaussian `X` on `H`. The shifted field `h + g` is the family
`f ↦ (h, f)_∇ + (g, f)_∇`.

Proposition 2.9 (source): "Suppose that h is a whole-plane GFF defined up to a global additive constant in ℝ and fix
g ∈ H. Then the laws of h + g and h are mutually absolutely continuous. The Radon-Nikodym derivative of the law of the
former with respect to that of the latter is given by `(1/Z) e^{(h,g)_∇}` (2.8) where Z is a normalization constant."

This file stages the first sentence, for `h` defined up to a constant in `ℝ`. The second sentence (the same statement
for a whole-plane GFF defined up to a global additive constant in `rℤ`, `r > 0`, with the normalization
`(h, φ₀) ∈ [0, r)`) is NOT staged here: its statement needs the concrete normalized field, not an abstract Gaussian
on `H`. The operator should decide whether to stage it separately. -/

universe u

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A Gaussian on the real inner product space `H` (source lines 1915-1918): a family `X f`, `f ∈ H`, of random
variables, measurable, centered, linear in `f` almost surely, jointly Gaussian, with covariance `(f, g)_∇ = ⟪f, g⟫`.
-/
structure IsGaussianOnInnerProductSpace {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (X : H → Ω → ℝ) : Prop where
  measurable : ∀ f : H, Measurable (X f)
  integral_eq_zero : ∀ f : H, ∫ ω, X f ω ∂P = 0
  linear : ∀ (f g : H) (a b : ℝ), ∀ᵐ ω ∂P, X (a • f + b • g) ω = a * X f ω + b * X g ω
  isGaussian : IsGaussianProcess (fun f : H => X f) P
  covariance_eq : ∀ f g : H, covariance (X f) (X g) P = inner ℝ f g

/-- **Miller-Sheffield, Imaginary Geometry IV, Proposition 2.9, first sentence** (arXiv:1302.4738v2, p. 49), for
the Gaussian `X` on the Hilbert space `H`: for every `g ∈ H` there is a normalization constant `Z > 0` such that the
law of `h + g` and the law of `h` are mutually absolutely continuous, the Radon-Nikodym derivative of the former with
respect to the latter being `(1/Z) e^{(h,g)_∇}`, where `(h, g)_∇ = X g`. Events are measurable sets of the
product σ-algebra on `H → ℝ`; `h` is the random family `ω ↦ (f ↦ X f ω)`. -/
def MillerSheffieldIG4Prop29 (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : H → Ω → ℝ),
    IsGaussianOnInnerProductSpace P H X → ∀ g : H, ∃ Z : ℝ, 0 < Z ∧
      ∀ A : Set (H → ℝ), MeasurableSet A →
        P ((fun ω f => X f ω + inner ℝ g f) ⁻¹' A)
            = ∫⁻ ω in (fun ω f => X f ω) ⁻¹' A, ENNReal.ofReal (Real.exp (X g ω) / Z) ∂P ∧
        (P ((fun ω f => X f ω + inner ℝ g f) ⁻¹' A) = 0 ↔ P ((fun ω f => X f ω) ⁻¹' A) = 0)

end HarmonicBalls
