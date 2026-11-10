import HarmonicBalls.FirstPass.S11s
import HarmonicBalls.FirstPass.S11v.Homog

/-!
# Coordinatewise B1 identity without pathwise homogeneity (fp-S11v, operator note 01:44 UTC, §3)

`dilOp_alphaCanon_eq` (S11s.lean) needs `PairingHomogeneous (hC ω)` at the given `ω`. Its proof uses homogeneity at one
scalar (`1/4`) and one test function (`dilateTest 1 φ`) only. Here the one instance is supplied almost surely by
`IsWholePlaneGFF.ae_pairing_smul`, for each fixed canonical coordinate `i`. The index `i` stays outside the a.s. quantifier
(`notes/fp-gaps/CHATGPT-n1-hAff-hhom.md`, §3, "Replacement for `dilOp_alphaCanon_eq`").
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set

/-- `normDilatePairing_half` for one test function: the only homogeneity used is at the scalar `1/4` and the test function
`dilateTest 1 φ` (hypothesis `hsm`). -/
theorem normDilatePairing_half_of_smul {T : (ℂ → ℝ) → ℝ} (s : ℝ) (φ : ℂ → ℝ)
    (hsm : T (fun y => (1 / 4 : ℝ) * dilateTest 1 φ y) = (1 / 4 : ℝ) * T (dilateTest 1 φ)) :
    normDilatePairing T s (1 / 2) φ = T (dilateTest 1 φ) - s * ∫ x, φ x := by
  have hn : (‖((1 / 2 : ℝ) : ℂ)‖ ^ 2)⁻¹ = 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    norm_num
  have hy : ∀ y : ℂ, (y - 0) / ((1 / 2 : ℝ) : ℂ) = ((2 : ℝ) : ℂ) * y := by
    intro y
    push_cast
    ring
  have h1 : T (fun y => φ (((2 : ℝ) : ℂ) * y)) = (1 / 4) * T (dilateTest 1 φ) := by
    rw [← hsm]
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

/-- **Coordinatewise B1 identity, almost surely (replacement for `dilOp_alphaCanon_eq`).** For each fixed canonical
coordinate `i`, almost surely `dilOp (alphaCanon α hC ω) i = alphaCanon α (normDilatePairing (hC ·) (s ·) (1/2)) ω i`.
No simultaneous homogeneity is used. -/
theorem ae_dilOp_alphaCanon_apply_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) (α : ℝ) (s : Ω → ℝ) (i : CanonIdx) :
    (fun ω => dilOp (alphaCanon α hC ω) i)
      =ᵐ[P] (fun ω => alphaCanon α (fun ω' => normDilatePairing (hC ω') (s ω') (1 / 2)) ω i) := by
  have hφ : IsTestFunction (univ : Set ℂ) i.1 := i.2.1
  filter_upwards [hG.ae_pairing_smul (1 / 4) (dilateTest 1 i.1) (isTestFunction_dilateTest hφ 1)] with ω hω
  have h2 := normDilatePairing_half_of_smul (T := hC ω) (s ω) i.1 hω
  have h3 := integral_dilateTest_one_mul_log hφ i.2.2
  simp only [dilOp, alphaCanon, fieldPairing]
  rw [h2, h3, i.2.2]
  ring

end HarmonicBalls
