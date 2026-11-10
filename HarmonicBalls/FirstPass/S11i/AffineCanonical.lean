import HarmonicBalls.FirstPass.S11i.CanonicalLawUniversal
import HarmonicBalls.Proposed.LQG

/-!
# Affine invariance of the canonical law (write-up sec. 6, B4, identities (26)-(30))

For a whole-plane GFF `h^ℂ` and a deterministic affine map `z ↦ a z + b` (`a ≠ 0`), the transformed pairings
`h^{(a,b)}_C(ω, φ) = |a|^{-2} h_C(ω, φ((· - b)/a)) - h_circ(ω, |a|, b) ∫φ` and circle averages
`h^{(a,b)}_circ(ω, r, z) = h_circ(ω, |a| r, a z + b) - h_circ(ω, |a|, b)` again form a whole-plane GFF. This is the
input `WholePlaneGFFAffineInvariance` (Proposed; HB eq. (2.2)-(2.5), Berestycki-Powell Cor. 5.7). Given it, the
canonical (mean-zero) law of the transformed field equals the canonical law of the original, by the universal
canonical-law identity `canonicalLaw_eq_of_isWholePlaneGFF`. The dilation case `a = R`, `b = 0` is the form used in
write-up (30) (`g^{(R)}` and `h^{(R)}` of eq. (27), with the insertion constant `-α₀ log R` not affecting the
mean-zero code).

The affine-invariance input is an explicit hypothesis (`hAff`); it is not proved here.
-/

namespace HarmonicBalls

open MeasureTheory Set

/-- **Canonical law is invariant under deterministic affine maps (write-up (27), code-law part).** Given the
affine-invariance input `WholePlaneGFFAffineInvariance` (Proposed, pending source-check) and a whole-plane GFF, the
mean-zero code law of the transformed pairings `|a|^{-2} h_C(φ((·-b)/a)) - h_circ(|a|, b) ∫φ` equals the canonical
law of `h_C`. -/
theorem canonicalLaw_affine_invariant {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc) (hh : IsWholePlaneGFF P hC hcirc)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    P.map (fun ω (i : CanonIdx) =>
        (‖a‖ ^ 2)⁻¹ * hC ω (fun y => i.1 ((y - b) / a)) - hcirc ω ‖a‖ b * ∫ x, i.1 x)
      = P.map (fun ω (i : CanonIdx) => hC ω i.1) :=
  canonicalLaw_eq_of_isWholePlaneGFF (hAff hh a ha b) hh

/-- **Dilation form (write-up (30) with `b = 0`).** For a deterministic `R > 0`, the mean-zero code law of
`R^{-2} h_C(φ(·/R)) - h_circ(R, 0) ∫φ` equals the canonical law of `h_C`. This is the code-law half of
`g^{(R)} =d g` in eq. (27). -/
theorem canonicalLaw_dilate_invariant {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc) (hh : IsWholePlaneGFF P hC hcirc)
    {R : ℝ} (hR : 0 < R) :
    P.map (fun ω (i : CanonIdx) => (R ^ 2)⁻¹ * hC ω (fun y => i.1 (y / (R : ℂ))) - hcirc ω R 0 * ∫ x, i.1 x)
      = P.map (fun ω (i : CanonIdx) => hC ω i.1) := by
  have h := canonicalLaw_affine_invariant hAff hh (a := (R : ℂ)) (by exact_mod_cast hR.ne') 0
  have hn : ‖(R : ℂ)‖ = R := by simp [abs_of_pos hR]
  rw [hn] at h
  simp only [sub_zero] at h
  exact h

end HarmonicBalls
