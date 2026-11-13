import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementObs
import HarmonicBalls.FirstPass.S11c.ShiftObs11_7
import HarmonicBalls.Steps.Sec11.PairingCovarianceLinearity

/-!
# The rooted constants of two normalizing test functions combine

For unit-mass test functions `ρ` on `D` and `ρ_V` on `V ⊆ D`, write
`κ(ρ) = fieldPairing α T ρ - γ ∫ log|w - z| ρ(w) dw` for the pairing of the rooted field `h - γ log|· - z|` with `ρ`.
If `D` lies in the closed unit disk (so that the term `log max(1, |w|)` of the reference observation vanishes on `D`)
and the pairing `T` is additive on `ρ - ρ_V`, the reference observation at the root `z` evaluated on the mean-zero
test function `ρ - ρ_V` is `κ(ρ) - κ(ρ_V)`. Consequently the scalars `exp(-ξ κ)` of the two normalizations multiply:
`exp(-ξ (κ(ρ) - κ(ρ_V))) · exp(-ξ κ(ρ_V)) = exp(-ξ κ(ρ))`.

* `campbellReferenceObs_meanZeroTestOfSub`: the deterministic identity;
* `ofReal_exp_campbellReferenceObs_meanZeroTestOfSub_mul`: the product of the scalars;
* `IsWholePlaneGFF.ae_campbellReferenceObs_meanZeroTestOfSub`: the identity almost surely for a whole-plane GFF,
  for which additivity of the pairing holds almost surely.
-/

open MeasureTheory Set

namespace HarmonicBalls

/-- **The reference observation on a difference of normalizing test functions.** For unit-mass test functions `ρ`
on `D` and `ρ_V` on `V ⊆ D`, with `D` in the closed unit disk and `T` additive on `ρ - ρ_V`, the reference
observation at `z` evaluated on the mean-zero test function `ρ - ρ_V` is the difference of the rooted pairings
`fieldPairing α T ρ - γ ∫ log|w - z| ρ(w) dw`. -/
theorem campbellReferenceObs_meanZeroTestOfSub {V D : Set ℂ} (hVD : V ⊆ D) (hD1 : ∀ w ∈ D, ‖w‖ ≤ 1)
    {ρ ρV : ℂ → ℝ} (hρ : IsTestFunction D ρ) (hρV : IsTestFunction V ρV) (h1 : ∫ x, ρ x = 1)
    (h1V : ∫ x, ρV x = 1) (γ α : ℝ) (T : (ℂ → ℝ) → ℝ) (z : ℂ)
    (hlin : T (fun x => ρ x - ρV x) = T ρ - T ρV) :
    (campbellReferenceObs γ α D T z).2 (meanZeroTestOfSub hVD hρ hρV h1 h1V) =
      (fieldPairing α T ρ - γ * ∫ w, Real.log ‖w - z‖ * ρ w) -
        (fieldPairing α T ρV - γ * ∫ w, Real.log ‖w - z‖ * ρV w) := by
  have hρV' : IsTestFunction D ρV := hρV.mono_set hVD
  have hzero : ∀ {φ : ℂ → ℝ}, IsTestFunction D φ → ∀ x, x ∉ D → φ x = 0 := fun hφ x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h))
  have hpt : ∀ w, (Real.log ‖w - z‖ - Real.log (max 1 ‖w‖)) * (ρ w - ρV w) =
      Real.log ‖w - z‖ * ρ w - Real.log ‖w - z‖ * ρV w := by
    intro w
    by_cases hw : w ∈ D
    · rw [max_eq_left (hD1 w hw), Real.log_one, sub_zero, mul_sub]
    · rw [hzero hρ w hw, hzero hρV' w hw]
      ring
  have iz : Integrable (fun w => Real.log ‖w - z‖ * ρ w) := by
    simpa only [mul_comm] using S11c.integrable_mul_logNorm_sub hρ z
  have izV : Integrable (fun w => Real.log ‖w - z‖ * ρV w) := by
    simpa only [mul_comm] using S11c.integrable_mul_logNorm_sub hρV' z
  have i0 : Integrable (fun w => ρ w * Real.log ‖w‖) := by
    simpa only [sub_zero] using S11c.integrable_mul_logNorm_sub hρ 0
  have i0V : Integrable (fun w => ρV w * Real.log ‖w‖) := by
    simpa only [sub_zero] using S11c.integrable_mul_logNorm_sub hρV' 0
  have hlog : ∫ x, (ρ x - ρV x) * Real.log ‖x‖ = (∫ x, ρ x * Real.log ‖x‖) - ∫ x, ρV x * Real.log ‖x‖ := by
    rw [← integral_sub i0 i0V]
    congr 1
    funext x
    ring
  simp only [campbellReferenceObs, meanZeroTestOfSub_val, fieldPairing, hlin, hpt]
  rw [integral_sub iz izV, hlog]
  ring

/-- **The scalars of the two normalizations multiply.** Under the hypotheses of
`campbellReferenceObs_meanZeroTestOfSub`, `exp(-ξ R(ρ - ρ_V)) · exp(-ξ κ(ρ_V)) = exp(-ξ κ(ρ))`, where `R` is the
reference observation at `z` and `κ(φ) = fieldPairing α T φ - γ ∫ log|w - z| φ(w) dw`. -/
theorem ofReal_exp_campbellReferenceObs_meanZeroTestOfSub_mul {V D : Set ℂ} (hVD : V ⊆ D)
    (hD1 : ∀ w ∈ D, ‖w‖ ≤ 1) {ρ ρV : ℂ → ℝ} (hρ : IsTestFunction D ρ) (hρV : IsTestFunction V ρV)
    (h1 : ∫ x, ρ x = 1) (h1V : ∫ x, ρV x = 1) (γ α ξ : ℝ) (T : (ℂ → ℝ) → ℝ) (z : ℂ)
    (hlin : T (fun x => ρ x - ρV x) = T ρ - T ρV) :
    ENNReal.ofReal (Real.exp (-ξ * (campbellReferenceObs γ α D T z).2 (meanZeroTestOfSub hVD hρ hρV h1 h1V))) *
        ENNReal.ofReal (Real.exp (-ξ * (fieldPairing α T ρV - γ * ∫ w, Real.log ‖w - z‖ * ρV w))) =
      ENNReal.ofReal (Real.exp (-ξ * (fieldPairing α T ρ - γ * ∫ w, Real.log ‖w - z‖ * ρ w))) := by
  rw [campbellReferenceObs_meanZeroTestOfSub hVD hD1 hρ hρV h1 h1V γ α T z hlin,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

/-- **The identity almost surely for a whole-plane GFF.** The pairing of a whole-plane GFF is almost surely additive on
`ρ - ρ_V`, so almost surely the reference observation at every root `z` evaluated on `ρ - ρ_V` is the difference of the
rooted pairings with `ρ` and `ρ_V`. -/
theorem IsWholePlaneGFF.ae_campbellReferenceObs_meanZeroTestOfSub {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {V D : Set ℂ} (hVD : V ⊆ D) (hD1 : ∀ w ∈ D, ‖w‖ ≤ 1) {ρ ρV : ℂ → ℝ} (hρ : IsTestFunction D ρ)
    (hρV : IsTestFunction V ρV) (h1 : ∫ x, ρ x = 1) (h1V : ∫ x, ρV x = 1) (γ α : ℝ) :
    ∀ᵐ ω ∂P, ∀ z : ℂ,
      (campbellReferenceObs γ α D (hC ω) z).2 (meanZeroTestOfSub hVD hρ hρV h1 h1V) =
        (fieldPairing α (hC ω) ρ - γ * ∫ w, Real.log ‖w - z‖ * ρ w) -
          (fieldPairing α (hC ω) ρV - γ * ∫ w, Real.log ‖w - z‖ * ρV w) := by
  filter_upwards [hh.ae_pairing_linear_combination (hρ.mono_set (subset_univ D))
    (hρV.mono_set (subset_univ V)) 1 (-1)] with ω hω z
  refine campbellReferenceObs_meanZeroTestOfSub hVD hD1 hρ hρV h1 h1V γ α (hC ω) z ?_
  have hfun : (fun x => ρ x - ρV x) = fun x => 1 * ρ x + -1 * ρV x := by
    funext x
    ring
  rw [hfun, hω]
  ring

end HarmonicBalls
