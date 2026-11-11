import HarmonicBalls.FirstPass.S11i.AlphaCanonical
import HarmonicBalls.FirstPass.S11i.Faithful

/-!
# The `alphaCanon` identities used in the truth check of `LQGCanonicalDecodersExistStmt`

The truth check needs the body of `alphaCanon` made
explicit: on mean-zero test functions, the canonical field of `h^α = h^ℂ - α log|·|` is the pairing
`φ ↦ (h^α, φ)` (`fieldPairing`, Defs/GFF). The declaration itself lives in the frozen file
`HarmonicBalls/FirstPass/Frozen/S11n.lean` and is not edited here.
-/

namespace HarmonicBalls

open Set

/-- Display of the canonical-field identity of the truth check (section 4): `alphaCanon α₀ hC ω` is the pairing
`φ ↦ fieldPairing α₀ (hC ω) φ` on the mean-zero test functions. Truth check TRUE. -/
theorem alphaCanon_eq_fieldPairing {Ω : Type*} (α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (ω : Ω) :
    alphaCanon α₀ hC ω = fun i => fieldPairing α₀ (hC ω) i.1 :=
  rfl

/-- The second identity of the truth check (section 4): `alphaCanon α₀ hC ω = localModConstField α₀ hC univ ω`,
the restriction to the whole plane modulo constants. Truth check TRUE. -/
theorem alphaCanon_eq_localModConstField {Ω : Type*} (α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (ω : Ω) :
    alphaCanon α₀ hC ω = localModConstField α₀ hC univ ω :=
  rfl

end HarmonicBalls
