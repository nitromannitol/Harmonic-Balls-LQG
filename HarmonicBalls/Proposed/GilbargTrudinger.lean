import Mathlib

/-!
# Literature input (proposed): Dirichlet problem with continuous data, Gilbarg-Trudinger Theorem 2.14

Source: D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
2nd edition, revised third printing, Springer (2001), Theorem 2.14, p. 26, together with the
exterior-sphere barrier (2.34), p. 27. Locator as given in the task brief; the operator source-checks
the wording before promotion to `HarmonicBalls/External`. This is a `Prop` taken as an explicit
hypothesis; it is used only in `HarmonicBalls/Proofs/Potential/GreenGeneralBoundary.lean`.

Scope of the staged statement: the Laplace equation in the plane (`ℂ ≅ ℝ²`) on a bounded domain
(open and connected), with continuous boundary data, the solution being harmonic in the sense of
Mathlib (`InnerProductSpace.HarmonicOnNhd`) and continuous on the closure.
-/

namespace HarmonicBalls

open Metric Set Topology

/-- The exterior sphere condition at `z ∈ ∂U`: some open ball of positive radius has `z` on its
boundary sphere and lies outside the closure of `U`. -/
def ExteriorSphereAt (U : Set ℂ) (z : ℂ) : Prop :=
  ∃ (w : ℂ) (r : ℝ), 0 < r ∧ dist z w = r ∧ ball w r ⊆ (closure U)ᶜ

/-- Gilbarg-Trudinger, Theorem 2.14 (p. 26), for the Laplacian on `ℂ ≅ ℝ²`: if a bounded domain `U`
satisfies the exterior sphere condition at every boundary point, then for every continuous boundary
datum `φ` on `∂U` there is a function `u`, continuous on `closure U` and harmonic in `U`, with
`u = φ` on `∂U`. Staged as a hypothesis; the operator source-checks it before promotion. -/
def GilbargTrudingerThm2_14 : Prop :=
  ∀ U : Set ℂ, IsOpen U → IsConnected U → Bornology.IsBounded U →
    (∀ z ∈ frontier U, ExteriorSphereAt U z) →
    ∀ φ : ℂ → ℝ, ContinuousOn φ (frontier U) →
      ∃ u : ℂ → ℝ, ContinuousOn u (closure U) ∧ InnerProductSpace.HarmonicOnNhd u U ∧
        ∀ z ∈ frontier U, u z = φ z

end HarmonicBalls
