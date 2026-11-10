import HarmonicBalls.FirstPass.S11i.CanonicalFailure
import HarmonicBalls.FirstPass.S11i.RootedFrequencyShift

/-!
# Step 8: the canonical failure set is measurable (fp-S11i-step8-canonical-failure, z11)

Steps 6-9 of the measurability chain of `notes/fp-gaps/CHATGPT-n3-hT.md` (sections 6-9, lines 174-317).

For a pairing `T : (ℂ → ℝ) → ℝ` and a root `z : ℂ`, the canonical field is `canonFieldOf α₀ T` (the pairings of
`h^α₀ = h^ℂ - α₀ log|·|` modulo constants; `alphaCanon α₀ hC ω = canonFieldOf α₀ (hC ω)`, `alphaCanon_eq_canonFieldOf`).
`canonicalWindowFreq` is the canonical window frequency: `N⁻¹` times the number of `n ∈ [N+1, 2N]` whose certificate
event holds at radius `2⁻ⁿ`, for the canonical measure `K L` and the canonical metric `d L`, `L` being the canonical
field. `canonicalFailure` is the set of pairs `(T, z)` at which that frequency does not converge to `q`.

The failure set is measurable for the product of the pairing σ-algebra `pairingSigmaAlgebra (fun T => T) univ` and the
Borel σ-algebra of `ℂ`. Measurability of the certificate events on `CanonSpace × ℂ` enters only through the hypothesis
`hcert` (to be supplied by `measurableSet_certificateEvent_canonical`). No new input.
-/

namespace HarmonicBalls.FirstPassS11iStep8Transfer

open MeasureTheory Set Filter Topology
open FirstPassS11i

/-- Canonical window frequency (chat 191 §6, §9): `N⁻¹` times the number of `n ∈ [N+1, 2N]` for which the certificate
event of the canonical measure `K L` and the canonical metric `d L` holds at radius `2⁻ⁿ` and root `z`. -/
noncomputable def canonicalWindowFreq (K : S11n.CanonSpace → Measure ℂ) (d : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (L : S11n.CanonSpace) (z : ℂ) (N : ℕ) : ℝ :=
  (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
      CertificateEvent (K L) (d L) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℕ) : ℝ) / (N : ℝ)

/-- Canonical failure set (chat 191 §6, §8): the pairs `(T, z)` of a pairing `T` and a root `z` at which the canonical
window frequency along the canonical field `Φ T` does not converge to `q`. -/
def canonicalFailure (K : S11n.CanonSpace → Measure ℂ) (d : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) (q : ℝ) (Φ : ((ℂ → ℝ) → ℝ) → S11n.CanonSpace) :
    Set (((ℂ → ℝ) → ℝ) × ℂ) :=
  {p | ¬ Tendsto (fun N : ℕ => canonicalWindowFreq K d Ostar U V W T Q' Q η M (Φ p.1) p.2 N) atTop (𝓝 q)}

end HarmonicBalls.FirstPassS11iStep8Transfer
