import HarmonicBalls.FirstPass.S11ak.Scaling
import HarmonicBalls.FirstPass.S11v.Affine
import HarmonicBalls.FirstPass.Frozen.S11c

/-! # The dilated normalised field for the punctured-ball decoder (fp-S11ak, owner z6)

For `R > 0` the dilated, normalised whole-plane field `g(w) = h^ℂ(R w) - h^ℂ_R(0)` (CHATGPT-lh-R4-R5.md §R5a,
"Explicit dilation proof") is again a whole-plane GFF (`WholePlaneGFFAffineInvariance`, Proposed `LQG.lean:53`,
derived in `S11v/Affine.lean`). Its mean-zero observations on the disk `ball (c/R) (r/R)` are the rescaled
mean-zero observations of `h^ℂ` on `ball c r` (`fieldPairing_dilate`).

This file proves these deterministic and GFF-level parts. The metric identity relating `𝔇(g)` to `𝔇(h^ℂ)` needs the
random-constant Weyl shift (see the report, fp-S11ak); it is not proved here.
-/

namespace HarmonicBalls.S11ak

open MeasureTheory Set Filter Metric

universe u

/-- The pairing of the dilated normalised field: `φ ↦ R⁻² hC(φ(·/R)) - c₀ ∫ φ`, with `c₀` the circle average
`h^ℂ_R(0)` (`dilCirc` is its circle-average process). -/
noncomputable def dilPairing (R : ℝ) (hC : (ℂ → ℝ) → ℝ) (c₀ : ℝ) : (ℂ → ℝ) → ℝ :=
  fun φ => (R ^ 2)⁻¹ * hC (fun y => φ (y / (R : ℂ))) - c₀ * ∫ x, φ x

/-- The circle-average process of the dilated normalised field: `(r, z) ↦ h^ℂ_{Rr}(Rz) - h^ℂ_R(0)`. -/
noncomputable def dilCirc (R : ℝ) (hcirc : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun r z => hcirc (R * r) (R * z) - hcirc R 0

/-- The dilated normalised field is a whole-plane GFF (`WholePlaneGFFAffineInvariance` at `a = R`, `b = 0`). -/
theorem isWholePlaneGFF_dilate {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) {R : ℝ} (hR : 0 < R) :
    IsWholePlaneGFF P (fun ω => dilPairing R (hC ω) (hcirc ω R 0)) (fun ω => dilCirc R (hcirc ω)) := by
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hA := HarmonicBalls.wholePlaneGFFAffineInvariance_derived P hC hcirc hG (R : ℂ) hR0 0
  have hnorm : ‖(R : ℂ)‖ = R := by simp [abs_of_pos hR]
  simp only [hnorm, sub_zero, add_zero] at hA
  exact hA

/-- The pairing identity behind the coordinate change: the pulled-back field `h^ℂ(R·) + Q log R` is the dilated
normalised field plus the random constant `c₀ + Q log R`. -/
theorem addFunPairing_affine_eq_dilPairing (R : ℝ) (hC : (ℂ → ℝ) → ℝ) (c₀ Q : ℝ) :
    HarmonicBalls.addFunPairing (HarmonicBalls.affinePullbackPairing hC R 0) (fun _ => Q * Real.log R) =
      HarmonicBalls.addFunPairing (dilPairing R hC c₀) (fun _ => c₀ + Q * Real.log R) := by
  funext φ
  simp only [HarmonicBalls.addFunPairing, HarmonicBalls.affinePullbackPairing, dilPairing, sub_zero,
    integral_const_mul]
  ring

/-- Mean-zero observations of the dilated field on `ball (c/R) (r/R)` are rescaled observations of `h^ℂ` on
`ball c r`, with the factor `R⁻²`. -/
theorem localMeanZeroObs_dilate (hC : (ℂ → ℝ) → ℝ) {R : ℝ} (hR : 0 < R) (c : ℂ) (r α c₀ : ℝ)
    (φ : {φ : ℂ → ℝ // IsTestFunction (ball (c / (R : ℂ)) (r / R)) φ ∧ ∫ x, φ x = 0}) :
    localMeanZeroObs α (ball (c / (R : ℂ)) (r / R)) (dilPairing R hC c₀) φ =
      (R ^ 2)⁻¹ * localMeanZeroObs α (ball c r) hC
        ⟨fun y => φ.1 (y / (R : ℂ)), isTestFunction_div_ball hR φ.2.1,
          integral_div_ofReal_eq_zero hR φ.1 φ.2.2⟩ := by
  unfold localMeanZeroObs
  exact fieldPairing_dilate hC hR α c₀ φ.1 φ.2.1.1.continuous φ.2.1.2.1 φ.2.2

/-- The image of the disk `ball c r` under `z ↦ R z` is `ball (R c) (R r)`; equivalently `z ∈ ball (c/R) (r/R)` iff
`R z ∈ ball c r` (`R > 0`). -/
theorem mem_ball_div_iff_smul {c : ℂ} {r R : ℝ} (hR : 0 < R) (z : ℂ) :
    z ∈ ball (c / (R : ℂ)) (r / R) ↔ (R : ℂ) * z ∈ ball c r := by
  simp only [Metric.mem_ball, dist_eq_norm]
  have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hz : (R : ℂ) * z - c = (R : ℂ) * (z - c / (R : ℂ)) := by
    rw [mul_sub, mul_div_cancel₀ c hR0]
  rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, lt_div_iff₀ hR, mul_comm]

end HarmonicBalls.S11ak
