import HarmonicBalls.FirstPass.S11ai.RootedIdentification

/-!
# Step 3 of the rooted decoder identification: the local pairing identity

Notes: `notes/fp-gaps/CHATGPT-n1-n2-11-13-inputs.md` section 1.3, Step 3, equation (5).
For a root `z` and a test function `φ` supported in `ball z b`, the reference observation `campbellReferenceObs`
(the field `g - γ log|· - z| + b` of the Campbell marking, with insertion `α₀`) pairs with `φ` exactly as the
window pairing `canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u)` pairs with the translate
`x ↦ φ(x + z)`, provided `u = -α₀ log‖z + ·‖` on `ball 0 b` and `‖z + y‖ ≤ 1` on `ball 0 b`
(the Campbell shift `γ log max(1, |·|)` vanishes there). No further input is used.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls
open HarmonicBalls.S11c

namespace FirstPassS11ai

/-- Translation of a test function on `D` to a test function on `ℂ`: `φ ↦ (x ↦ φ(x + z))`, mean zero. -/
noncomputable def translateTestPairing {D : Set ℂ} (z : ℂ)
    (φ : {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0}) :
    {ψ : ℂ → ℝ // IsTestFunction univ ψ ∧ ∫ x, ψ x = 0} :=
  ⟨fun x => φ.1 (x + z),
    ⟨φ.2.1.1.comp (contDiff_id.add contDiff_const), φ.2.1.2.1.comp_homeomorph (Homeomorph.addRight z),
      subset_univ _⟩,
    (integral_add_right_eq_self φ.1 z).trans φ.2.2⟩

/-- **Step 3 (pairing identity).** If `u = -α₀ log‖z + ·‖` on `ball 0 b`, `‖z + y‖ ≤ 1` on `ball 0 b`, and `φ` vanishes
outside `ball z b`, then the reference observation at `z` and the translated window pairing agree on `φ`. -/
theorem campbellReferenceObs_eq_canonFieldOf_translate {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) (γ α₀ : ℝ) {D : Set ℂ} {z : ℂ} {b : ℝ} (u : ℂ → ℝ)
    (hu : ∀ w ∈ ball (0 : ℂ) b, u w = -α₀ * Real.log ‖z + w‖)
    (hbz : ∀ y ∈ ball (0 : ℂ) b, ‖z + y‖ ≤ 1)
    (φ : {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0})
    (hφs : ∀ x, x ∉ ball z b → φ.1 x = 0) :
    (campbellReferenceObs γ α₀ D (hC ω) z).2 φ =
      canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u) (translateTestPairing z φ) := by
  -- the translated test function is supported in `ball 0 b`
  have hsupp : ∀ x, φ.1 (x + z) ≠ 0 → x ∈ ball (0 : ℂ) b := by
    intro x hx
    by_contra h
    apply hx
    apply hφs
    intro hmem
    apply h
    rw [mem_ball, dist_eq_norm, add_sub_cancel_right] at hmem
    exact mem_ball_zero_iff.2 hmem
  -- pointwise identity for the shift term
  have hUpt : ∀ x, u x * φ.1 (x + z) = -α₀ * Real.log ‖x + z‖ * φ.1 (x + z) * 1 := by
    intro x
    by_cases hx : φ.1 (x + z) = 0
    · simp [hx]
    · rw [hu x (hsupp x hx), add_comm z x]
      ring
  -- pointwise identity for the Campbell term: `log max(1, ‖x + z‖) = 0` on the support
  have hCpt : ∀ x, (Real.log ‖x + z - z‖ - Real.log (max 1 ‖x + z‖)) * φ.1 (x + z) =
      φ.1 (x + z) * Real.log ‖x‖ := by
    intro x
    by_cases hx : φ.1 (x + z) = 0
    · simp [hx]
    · have h1 : ‖x + z‖ ≤ 1 := by
        rw [add_comm]
        exact hbz x (hsupp x hx)
      rw [add_sub_cancel_right, max_eq_left h1, Real.log_one, sub_zero, mul_comm]
  -- the three integral identities
  have hI1 : ∫ x, φ.1 x * Real.log ‖x‖ = ∫ x, φ.1 (x + z) * Real.log ‖x + z‖ :=
    (integral_add_right_eq_self (fun x => φ.1 x * Real.log ‖x‖) z).symm
  have hI2 : ∫ w, (Real.log ‖w - z‖ - Real.log (max 1 ‖w‖)) * φ.1 w =
      ∫ x, φ.1 (x + z) * Real.log ‖x‖ := by
    refine (integral_add_right_eq_self (fun w => (Real.log ‖w - z‖ - Real.log (max 1 ‖w‖)) * φ.1 w) z).symm.trans ?_
    congr 1
    funext x
    exact hCpt x
  have hI3 : ∫ x, u x * φ.1 (x + z) = -α₀ * ∫ x, φ.1 (x + z) * Real.log ‖x + z‖ := by
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [hUpt x]
    ring
  -- the field side
  have hfun : (fun y => φ.1 (y - z + z)) = φ.1 := funext fun y => by rw [sub_add_cancel]
  have hint0 : ∫ x, φ.1 (x + z) = 0 := (integral_add_right_eq_self φ.1 z).trans φ.2.2
  unfold campbellReferenceObs canonFieldOf fieldPairing addFunPairing translatedPairing translateTestPairing
  simp only [hint0, mul_zero, sub_zero]
  rw [hfun, hI1, hI2, hI3]
  ring

end FirstPassS11ai
