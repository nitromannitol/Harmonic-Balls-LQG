import HarmonicBalls.FirstPass.S11i.AlphaCanonical
import HarmonicBalls.FirstPass.S11i.MixingCanonical
import HarmonicBalls.Proposed.LQG

/-!
# B1: covariance of the canonical decoders under the dilation `T = dilOp` (Step 13, section 3)

Notation of the LQG literature (Duplantier-Sheffield, Berestycki-Powell). For a whole-plane GFF `hC` with circle averages
`hcirc`, and the dilation by `r = 1/2`, the normalized dilated background is `g̃ = g(r ·) - g_r(0)`, here written in
pairing form exactly as in `WholePlaneGFFAffineInvariance` (Proposed/LQG.lean, `a = r`, `b = 0`).
The identity `dilOp (alphaCanon α hC ω) = alphaCanon α hC' ω` on mean-zero test functions (`normDilatePairing_half`
and `dilOp_alphaCanon_eq`) uses only the homogeneity of the pairing `hC ω` on test functions (`PairingHomogeneous`),
which is part of the meaning of a random generalized function; `IsWholePlaneGFF` does not state it (see the report).
-/

namespace HarmonicBalls

open MeasureTheory Set

/-- Homogeneity of a pairing functional on test functions: `(h, c k) = c (h, k)` for every real `c`. -/
def PairingHomogeneous (T : (ℂ → ℝ) → ℝ) : Prop :=
  ∀ c : ℝ, ∀ k : ℂ → ℝ, IsTestFunction (univ : Set ℂ) k → T (fun y => c * k y) = c * T k

/-- The normalized dilated pairing `φ ↦ (‖a‖²)⁻¹ T(φ((· - b)/a)) - s ∫ φ` of Proposed/LQG.lean with `a = r`, `b = 0`:
the pairing of `g(r ·) - g_r(0)` where `s = g_r(0)`. -/
noncomputable def normDilatePairing (T : (ℂ → ℝ) → ℝ) (s r : ℝ) : (ℂ → ℝ) → ℝ :=
  fun φ => (‖(r : ℂ)‖ ^ 2)⁻¹ * T (fun y => φ ((y - 0) / (r : ℂ))) - s * ∫ x, φ x

/-- For `r = 1/2` the normalized dilated pairing of a test function is the dilation operator `dilateTest 1`
applied to the pairing, minus the constant `s ∫ φ`. -/
theorem normDilatePairing_half {T : (ℂ → ℝ) → ℝ} (hT : PairingHomogeneous T) (s : ℝ) (φ : ℂ → ℝ)
    (hφ : IsTestFunction (univ : Set ℂ) φ) :
    normDilatePairing T s (1 / 2) φ = T (dilateTest 1 φ) - s * ∫ x, φ x := by
  have hn : (‖((1 / 2 : ℝ) : ℂ)‖ ^ 2)⁻¹ = 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    norm_num
  have hy : ∀ y : ℂ, (y - 0) / ((1 / 2 : ℝ) : ℂ) = ((2 : ℝ) : ℂ) * y := by
    intro y
    push_cast
    ring
  have h1 : T (fun y => φ (((2 : ℝ) : ℂ) * y)) = (1 / 4) * T (dilateTest 1 φ) := by
    have := hT (1 / 4) (dilateTest 1 φ) (isTestFunction_dilateTest hφ 1)
    rw [← this]
    congr 1
    funext y
    simp only [dilateTest, pow_one, Complex.real_smul]
    push_cast
    ring
  unfold normDilatePairing
  rw [hn]
  simp only [hy]
  rw [h1]
  ring

/-- The B1 identity at the canonical level: on mean-zero test functions the canonical field of the normalized dilated
background is the dilation of the canonical field, `dilOp (alphaCanon α hC ω) = alphaCanon α hC' ω`, where
`hC' ω = normDilatePairing (hC ω) (s ω) (1/2)` and the constant `s ω` (the circle average `g_{1/2}(0)`) is annihilated by
mean-zero tests. The drift `α ∫ φ log|·|` is invariant by `integral_dilateTest_one_mul_log`. -/
theorem dilOp_alphaCanon_eq {Ω : Type*} (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (s : Ω → ℝ) (ω : Ω)
    (hT : PairingHomogeneous (hC ω)) :
    dilOp (alphaCanon α hC ω) = alphaCanon α (fun ω' => normDilatePairing (hC ω') (s ω') (1 / 2)) ω := by
  funext i
  have hφ : IsTestFunction (univ : Set ℂ) i.1 := i.2.1
  have h2 := normDilatePairing_half hT (s ω) i.1 hφ
  have h3 := integral_dilateTest_one_mul_log hφ i.2.2
  simp only [dilOp, alphaCanon, fieldPairing]
  rw [h2, h3, i.2.2]
  ring

end HarmonicBalls
