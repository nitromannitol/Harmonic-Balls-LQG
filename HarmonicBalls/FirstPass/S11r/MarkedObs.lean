import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.Proposed.DuplantierMillerSheffield

/-!
# Marked local observation of the Duplantier-Miller-Sheffield shifted field (fp-S11r-marked-obs)

Source: ChatGPT chat 198 (PRO), `notes/fp-gaps/CHATGPT-hb-11-13-step8-Q1-Q2.md`, Ruling Q2 (lines 109-185).

Let `T` be the raw pairing functional of a whole-plane field `h = h^ℂ - α₀ log|·|` and let `z` be a root. The sampling
procedure of Duplantier-Miller-Sheffield (Lemma A.10, whole-plane clause) shifts the field by `dmsShift γ z`, whose raw
pairing functional is `dmsShiftedPairing γ z T h10`, where `h10 = h_1(0)`. The marked observation `(z, h|_D mod ℝ)` of the
shifted field is the reference observation `campbellReferenceObs γ α₀ D T z` of the Campbell-Palm law of `T` rooted at `z`.

The identity is exact on every domain `D` (no containment `D ⊆ B₁` is needed). Its content is algebraic: on mean-zero
test functions `φ` the additive constant `dmsConstant γ z h10` multiplies `∫ φ = 0` and drops out, while the
`w`-dependent term of `dmsShift` equals `-γ (log|w - z| - log max(1, |w|))`, the term carried by `campbellReferenceObs`.

This file does NOT assert the raw global identity `dmsShiftedPairing γ z T h10 = addFunPairing (translatedPairing hC hcirc z ω) u`:
that identity is false (Ruling Q2) and is not sought.
-/

namespace HarmonicBalls

open MeasureTheory

/-- **Marked local observation of the Duplantier-Miller-Sheffield shifted field.** For every domain `D ⊆ ℂ`, every raw
pairing functional `T`, every root `z`, and every `h10 : ℝ`, the marked observation of the shifted pairing
`dmsShiftedPairing γ z T h10` at `z` equals the Campbell-Palm reference observation `campbellReferenceObs γ α₀ D T z`.
Only mean-zero test functions supported in `D` enter the observation (`campbellMarkedObs`, `fieldSigmaAlgebraModConst`). -/
theorem campbellMarkedObs_dmsShiftedPairing
    (γ α₀ : ℝ) (D : Set ℂ) (T : (ℂ → ℝ) → ℝ) (z : ℂ) (h10 : ℝ) :
    campbellMarkedObs α₀ D (dmsShiftedPairing γ z T h10) z =
      campbellReferenceObs γ α₀ D T z := by
  -- against any test function, the DMS shift is `-γ` times the reference kernel `log|w - z| - log max(1, |w|)`
  have hshift : ∀ φ : ℂ → ℝ,
      (∫ w, dmsShift γ z w * φ w) =
        -γ * ∫ w, (Real.log ‖w - z‖ - Real.log (max 1 ‖w‖)) * φ w := by
    intro φ
    rw [← integral_const_mul (-γ)]
    congr 1
    funext w
    unfold dmsShift
    rw [max_comm ‖w‖ 1]
    ring
  simp only [campbellMarkedObs, campbellReferenceObs, fieldPairing, dmsShiftedPairing]
  congr 1
  funext φ
  -- mean-zero test function: the additive constant `dmsConstant γ z h10` drops out
  have hφ0 : ∫ w, φ.1 w = 0 := φ.2.2
  rw [hφ0, mul_zero, add_zero, hshift φ.1]
  ring

end HarmonicBalls
