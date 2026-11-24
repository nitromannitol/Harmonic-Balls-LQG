import HarmonicBalls.Defs.Geometry
import Mathlib.Analysis.Complex.Isometry

/-!
# Lipschitz domains: reorienting the axes by rotations suffices

Definition 11.1 (def:lipschitz, corrected paper line 2881) describes `A ∩ B_r(x₀)` as the region
above a Lipschitz graph "upon relabeling and reorienting the coordinate axes if necessary".
`IsLipschitzDomain` (`Defs/Geometry.lean`) allows every real linear isometry `e` of `ℂ` as the change
of coordinates. `IsLipschitzDomainRotation` allows only rotations `x ↦ u x` with `|u| = 1`.

The two classes are equal (`isLipschitzDomain_iff_rotation`): every linear isometry of `ℂ` is a
rotation or a rotation composed with complex conjugation (`linear_isometry_complex`), and for
`y = u x̄` the region `{f(Re y) < Im y}` is `{g(Re z) < Im z}` for the rotation `z = -ū x` and the
Lipschitz function `g(s) = f(-s)`. So the reading of "relabeling and reorienting" (with or without
reflections) does not change the notion.
-/

namespace HarmonicBalls

open Metric Set

/-- Definition 11.1 with the coordinates reoriented by rotations only. -/
def IsLipschitzDomainRotation (A : Set ℂ) : Prop :=
  IsOpen A ∧ IsConnected A ∧
    ∀ x₀ ∈ frontier A, ∃ r > 0, ∃ u : ℂ, ‖u‖ = 1 ∧ ∃ K : NNReal, ∃ f : ℝ → ℝ, LipschitzWith K f ∧
      A ∩ ball x₀ r = {x ∈ ball x₀ r | f (u * x).re < (u * x).im}

/-- **The class of Lipschitz domains does not depend on whether reflections are allowed.** -/
theorem isLipschitzDomain_iff_rotation (A : Set ℂ) :
    IsLipschitzDomain A ↔ IsLipschitzDomainRotation A := by
  constructor
  · rintro ⟨hA, hAc, h⟩
    refine ⟨hA, hAc, fun x₀ hx₀ => ?_⟩
    obtain ⟨r, hr, e, K, f, hf, heq⟩ := h x₀ hx₀
    obtain ⟨a, ha | ha⟩ := linear_isometry_complex e
    · refine ⟨r, hr, (a : ℂ), by simp, K, f, hf, ?_⟩
      rw [heq, ha]
      rfl
    · refine ⟨r, hr, -(starRingEnd ℂ (a : ℂ)), by simp, K, fun s => f (-s), ?_, ?_⟩
      · have hg := hf.comp LipschitzWith.id.neg
        rw [mul_one] at hg
        exact hg
      · rw [heq, ha]
        ext x
        simp only [mem_ofPred_eq, LinearIsometryEquiv.trans_apply, rotation_apply,
          Complex.conjLIE_apply]
        constructor <;> rintro ⟨hx, hxf⟩ <;> refine ⟨hx, ?_⟩
        · have h1 : (-(starRingEnd ℂ (a : ℂ)) * x).re = -((a : ℂ) * (starRingEnd ℂ) x).re := by
            simp [Complex.mul_re]
          have h2 : (-(starRingEnd ℂ (a : ℂ)) * x).im = ((a : ℂ) * (starRingEnd ℂ) x).im := by
            simp [Complex.mul_im]
            ring
          rw [h1, h2, neg_neg]
          exact hxf
        · have h1 : (-(starRingEnd ℂ (a : ℂ)) * x).re = -((a : ℂ) * (starRingEnd ℂ) x).re := by
            simp [Complex.mul_re]
          have h2 : (-(starRingEnd ℂ (a : ℂ)) * x).im = ((a : ℂ) * (starRingEnd ℂ) x).im := by
            simp [Complex.mul_im]
            ring
          rw [h1, h2, neg_neg] at hxf
          exact hxf
  · rintro ⟨hA, hAc, h⟩
    refine ⟨hA, hAc, fun x₀ hx₀ => ?_⟩
    obtain ⟨r, hr, u, hu, K, f, hf, heq⟩ := h x₀ hx₀
    have hu' : u ∈ Submonoid.unitSphere ℂ := mem_sphere_zero_iff_norm.2 hu
    refine ⟨r, hr, rotation ⟨u, hu'⟩, K, f, hf, ?_⟩
    rw [heq]
    rfl

end HarmonicBalls
