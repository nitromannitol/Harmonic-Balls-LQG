import HarmonicBalls.FirstPass.S11i.RootedLocality
import HarmonicBalls.FirstPass.S11i.TranslationCanonical

/-!
# Almost sure local window frequency at a fixed root (fp-S11i-11-13, write-up Step 11.5)

Fix a root `z` and a radius `b > 0` with `2b < ‖z‖` and `2b < 1` (write-up: `b = min{‖z‖, 1-‖z‖}/8`). Let `u` be smooth,
compactly supported, with zero unit-circle average and `u = -α₀ log‖· + z‖` on `B_b(0)` (`exists_log_shift_cutoff`,
`RootedBump.lean`). Let `G ω` be any distribution that agrees modulo constants with the shifted translated field
`addFunPairing (translatedPairing hC hcirc z ω) u` on the test functions supported in `B_b(0)`.

Then, almost surely, the window frequency along dilations of an event `E = ballRestrictPairing 7 ⁻¹' F` (`F` measurable,
on `B_7(0)` modulo constants) at `G ω` converges to `P{alphaCanon γ hC ∈ E}`, the same limit as at the translated
canonical field (translation invariance, `prob_alphaCanon_translatedPairing`).

Proof. `ae_windowFreqOf_shift` (Step 11.2) for the translated whole-plane GFF `translatedPairing hC hcirc z`
(`isWholePlaneGFF_translate`) gives the limit for `addFunPairing (translatedPairing hC hcirc z ω) u`; the locality
`windowFreqOf_ballRestrict_eq` (Step 11.4) shows that the two window frequencies agree for all `N` with `7 / 2^(N+1) < b`,
which holds eventually.
-/

namespace HarmonicBalls

universe u

open MeasureTheory ProbabilityTheory Metric Set Filter Topology
open HarmonicBalls.S11c

/-- The restriction map `ballRestrictPairing R` is measurable for the product σ-algebras. -/
theorem measurable_ballRestrictPairing (R : ℝ) :
    Measurable (ballRestrictPairing R) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

/-- Step 11.5 (a.s. local window frequency at a fixed root). See the module docstring. -/
theorem ae_rooted_window_frequency {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    (z : ℂ) {b : ℝ} (hb : 0 < b)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    (u : ℂ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcomp : HasCompactSupport u)
    (hu0 : Real.circleAverage u 0 1 = 0)
    (G : Ω → (ℂ → ℝ) → ℝ)
    (hG : ∀ ω, ∀ φ : ℂ → ℝ, IsTestFunction (ball (0 : ℂ) b) φ → ∫ x, φ x = 0 →
      G ω φ = addFunPairing (translatedPairing hC hcirc z ω) u φ) :
    ∀ᵐ ω ∂P, Tendsto (fun N => windowFreqOf γ (ballRestrictPairing 7 ⁻¹' F) (G ω) N) atTop
      (𝓝 (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal) := by
  set E : Set (ModConstTestPairings (Set.univ : Set ℂ)) := ballRestrictPairing 7 ⁻¹' F with hE_def
  have hEm : MeasurableSet E := (measurable_ballRestrictPairing 7) hF
  have hpt := ae_windowFreqOf_shift hCM hB (isWholePlaneGFF_translate hh z) γ hEm u hu hcomp hu0
  rw [prob_alphaCanon_translatedPairing hh γ z hEm] at hpt
  have hev : ∀ᶠ N : ℕ in atTop, (7 : ℝ) / 2 ^ (N + 1) < b := by
    obtain ⟨N0, hN0⟩ := pow_unbounded_of_one_lt (7 / b) (by norm_num : (1 : ℝ) < 2)
    filter_upwards [eventually_ge_atTop N0] with N hN
    have h1 : (2 : ℝ) ^ N0 ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
    have hb7 : 7 < b * 2 ^ N0 := by rw [div_lt_iff₀ hb, mul_comm] at hN0; exact hN0
    rw [div_lt_iff₀ (by positivity), pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left h1 hb.le]
  filter_upwards [hpt] with ω hω
  refine Tendsto.congr' ?_ hω
  filter_upwards [hev] with N hN
  exact (windowFreqOf_ballRestrict_eq γ (by norm_num) F (hG ω) N hN).symm

end HarmonicBalls
