import Mathlib
import HarmonicBalls.Proposed.GilbargTrudinger
import HarmonicBalls.Proofs.Potential.PerronBoundary
import HarmonicBalls.Proofs.Potential.GilbargTrudingerDirichletProved
import HarmonicBalls.Proofs.Potential.GreenGeneralBoundary

/-!
# The exterior-sphere barrier and the Hölder Dirichlet problem on smooth domains

Source: D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
2nd edition, revised third printing, Springer (2001): the barrier (2.34), p. 27, at a boundary point
with an exterior sphere, and Theorem 2.14, p. 26.

* `HarmonicBalls.exists_barrier_of_exteriorSphereAt`: if `U` satisfies the exterior sphere condition
  `ExteriorSphereAt U z` at `z`, there is a barrier at `z`: a function continuous on `closure U`,
  harmonic in `U`, zero at `z`, positive on `closure U \ {z}`, and bounded below by a positive
  constant away from `z`. It is the logarithmic barrier of the exterior disc (`exists_barrier`),
  the planar case of (2.34).
* `HarmonicBalls.GreenGeneral.exists_dirichlet_holderOnWith_of_smooth`: the Stage 1 global statement
  `GreenGeneral.exists_dirichlet_holderOnWith` for a smooth bounded open set, with Theorem 2.14
  supplied by `gilbargTrudingerThm2_14_holds` instead of a hypothesis.
-/

namespace HarmonicBalls

open Metric Set Topology

/-- **Barrier (2.34)** of Gilbarg-Trudinger (p. 27) in the plane. If `U` satisfies the exterior
sphere condition at `z`, there is a function `β`, continuous on `closure U` and harmonic in `U`, with
`β z = 0`, `β > 0` on `closure U \ {z}`, and `β ≥ b > 0` on `closure U` at distance at least `δ`
from `z`, for every `δ > 0`. -/
theorem exists_barrier_of_exteriorSphereAt {U : Set ℂ} {z : ℂ} (h : ExteriorSphereAt U z) :
    ∃ β : ℂ → ℝ, ContinuousOn β (closure U) ∧ InnerProductSpace.HarmonicOnNhd β U ∧
      β z = 0 ∧ (∀ x ∈ closure U, x ≠ z → 0 < β x) ∧
      ∀ δ : ℝ, 0 < δ → ∃ b : ℝ, 0 < b ∧ ∀ x ∈ closure U, δ ≤ dist x z → b ≤ β x := by
  obtain ⟨w, r, hr, hzw, hball⟩ := h
  obtain ⟨β, hβc, hβh, -, hβz, hβlow⟩ := exists_barrier (Ω := U) hr hzw hball
  refine ⟨β, hβc, hβh, hβz, fun x hx hxz => ?_, hβlow⟩
  obtain ⟨b, hb, hbx⟩ := hβlow (dist x z) (dist_pos.mpr hxz)
  exact hb.trans_le (hbx x hx le_rfl)

namespace GreenGeneral

/-- The Stage 1 global statement (steps4-final Section 1, lines 125-199) without a literature
hypothesis. For a smooth bounded open set `O` and an `a`-Hölder datum `g` on `∂O`, with constant `L`
and bound `B`, the Dirichlet problem on `O` has a solution `H`, harmonic on `O`, equal to `g` on `∂O`,
and Hölder continuous on `closure O`. Theorem 2.14 of Gilbarg-Trudinger is
`gilbargTrudingerThm2_14_holds`. -/
theorem exists_dirichlet_holderOnWith_of_smooth {O : Set ℂ} (hO : IsSmoothBoundedOpen O)
    {g : ℂ → ℝ} {a L B : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hgc : ContinuousOn g (frontier O))
    (hgL : ∀ x ∈ frontier O, ∀ y ∈ frontier O, |g x - g y| ≤ L * dist x y ^ a)
    (hgB : ∀ x ∈ frontier O, |g x| ≤ B) :
    ∃ H : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd H O ∧ (∀ z ∈ frontier O, H z = g z) ∧
      ∃ C r : NNReal, 0 < r ∧ HolderOnWith C r H (closure O) :=
  exists_dirichlet_holderOnWith hO gilbargTrudingerThm2_14_holds ha hL hB hgc hgL hgB

end GreenGeneral

end HarmonicBalls
