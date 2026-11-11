import HarmonicBalls.FirstPass.S11r.CMShift

/-!
# Rooted observation as an α = 0 observation of a shifted field

Step (d) of the rooted identity (20): on a disk `V` with `0 ∉ V` and `z ∉ V`, the rooted
reference observation `campbellReferenceObs γ α V (hC) z` (the Campbell-Palm observation of `f_z`, Lebesgue-a.e. root)
equals the observation at `α = 0` of `h^ℂ + f`, whenever `f = -α log|·| - γ log|· - z|` on `V`, `V ⊆ B₁` (so
`log max(1, |·|) = 0` on `V`). This is the Cameron-Martin shift input of `ae_mem_addFunPairing_of_ae_mem`.

* `integrable_test_mul_log_sub`: for a test function supported in `V` with `p ∉ V`, `φ · log|· - p|` is integrable
  (it is continuous with compact support: it vanishes near `p`).
* `campbellReferenceObs_eq_addFunPairing`: the identity of observations on test functions supported in `V`.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric

/-- A test function supported in `V`, with `p ∉ V`: `φ · log|· - p|` is continuous with compact support, hence
integrable (the logarithm is singular only at `p`, where `φ` vanishes in a neighbourhood). -/
theorem integrable_test_mul_log_sub {V : Set ℂ} {φ : ℂ → ℝ} (hφ : IsTestFunction V φ) {p : ℂ} (hp : p ∉ V) :
    Integrable (fun x => φ x * Real.log ‖x - p‖) := by
  have hpt : p ∉ tsupport φ := fun h => hp (hφ.2.2 h)
  have hcont : Continuous (fun x => φ x * Real.log ‖x - p‖) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x = p
    · have hzero : φ =ᶠ[nhds x] 0 := by
        rw [hx]
        exact notMem_tsupport_iff_eventuallyEq.1 hpt
      have h0 : ContinuousAt (fun _ : ℂ => (0 : ℝ)) x := continuousAt_const
      exact h0.congr (by
        filter_upwards [hzero] with y hy
        simp [hy])
    · have hne : x - p ≠ 0 := sub_ne_zero.2 hx
      have hn : ContinuousAt (fun y : ℂ => ‖y - p‖) x :=
        (continuous_norm.comp (continuous_id.sub continuous_const)).continuousAt
      have hlog : ContinuousAt (fun y : ℂ => Real.log ‖y - p‖) x :=
        hn.log (norm_ne_zero_iff.2 hne)
      exact (hφ.1.continuous.continuousAt).mul hlog
  exact hcont.integrable_of_hasCompactSupport (hφ.2.1.mul_right)

/-- The rooted reference observation of `V`-supported test functions is the α = 0 observation of `h^ℂ + f`, when
`f = -α log|·| - γ log|· - z|` on `V`, `V ⊆ B₁ ∖ {0}`, and `z ∉ V`. -/
theorem campbellReferenceObs_eq_addFunPairing {V : Set ℂ} {α γ : ℝ} {z : ℂ} (T : (ℂ → ℝ) → ℝ) {f : ℂ → ℝ}
    (hV1 : ∀ x ∈ V, ‖x‖ < 1) (hV0 : (0 : ℂ) ∉ V) (hzV : z ∉ V)
    (hf : ∀ x ∈ V, f x = -α * Real.log ‖x‖ - γ * Real.log ‖x - z‖)
    (φ : {φ : ℂ → ℝ // IsTestFunction V φ ∧ ∫ x, φ x = 0}) :
    (campbellReferenceObs γ α V T z).2 φ = fieldPairing 0 (addFunPairing T f) φ.1 := by
  obtain ⟨φ, hφ, -⟩ := φ
  have hzero : ∀ x, x ∉ V → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h))
  have hmax : ∀ x ∈ V, Real.log (max 1 ‖x‖) = 0 := fun x hx => by
    rw [max_eq_left (hV1 x hx).le, Real.log_one]
  have hI0 : Integrable (fun x => φ x * Real.log ‖x‖) := by
    simpa using integrable_test_mul_log_sub hφ hV0
  have hIz : Integrable (fun x => φ x * Real.log ‖x - z‖) := integrable_test_mul_log_sub hφ hzV
  have hpt : ∀ x, f x * φ x = -α * (φ x * Real.log ‖x‖) + (-γ) * (φ x * Real.log ‖x - z‖) := by
    intro x
    by_cases hx : x ∈ V
    · rw [hf x hx]; ring
    · rw [hzero x hx]; simp
  have hpt2 : ∀ w, (Real.log ‖w - z‖ - Real.log (max 1 ‖w‖)) * φ w = φ w * Real.log ‖w - z‖ := by
    intro w
    by_cases hw : w ∈ V
    · rw [hmax w hw]; ring
    · rw [hzero w hw]; simp
  have hint : ∫ x, f x * φ x = -α * (∫ x, φ x * Real.log ‖x‖) + (-γ) * (∫ x, φ x * Real.log ‖x - z‖) := by
    simp_rw [hpt]
    rw [integral_add (hI0.const_mul _) (hIz.const_mul _), integral_const_mul, integral_const_mul]
  unfold campbellReferenceObs fieldPairing addFunPairing
  simp_rw [hpt2]
  rw [zero_mul, sub_zero, hint]
  ring

end HarmonicBalls
