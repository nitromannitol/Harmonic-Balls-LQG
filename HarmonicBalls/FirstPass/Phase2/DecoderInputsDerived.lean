import HarmonicBalls.FirstPass.Phase2.MassFunctionalDerived
import HarmonicBalls.FirstPass.S11n

/-!
# Partial derivation for the canonical decoders

Scope: the measurability of the closed-set and open-set masses of the canonical decoder. A canonical pairing
`L : S11n.CanonSpace` (mean-zero whole-plane pairings) is lifted to a raw distribution `rawOfCanon L`,
`φ ↦ L (φ - (∫ φ) · unitTest)` on test functions, where `unitTest` is a fixed test function of integral one.
The lift is measurable for the distribution σ-algebra `distributionMeasurableSpace`, so the masses of the decoder (`MassFunctionalDerived.massDecoder`, `openMass`) are measurable functions of `L`.

Not in this file: the Measure-valued kernel `K : CanonSpace → Measure ℂ` of `LQGCanonicalDecodersMeasurableExistStmt`
(its vague-limit assembly, and the identity with `e^{-γ c} μ` on the good event).
-/

namespace HarmonicBalls.DecoderInputsDerived

open MeasureTheory Set
open scoped ENNReal
open FirstPassS11atProducers HarmonicBalls.MassFunctionalDerived

attribute [local instance] distributionMeasurableSpace

/-- A fixed test function of integral one: the normalized circle approximant of radius `1` at the origin. -/
noncomputable def unitTest : ℂ → ℝ := circleApprox (by norm_num : (0 : ℝ) < 1) 0 0

theorem unitTest_isTestFunction : IsTestFunction univ unitTest :=
  isTestFunction_circleApprox _ _ _

theorem unitTest_integral : ∫ x, unitTest x = 1 :=
  integral_circleApprox _ _ _

theorem isTestFunction_sub_integral_mul {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    IsTestFunction univ (fun x => φ x - (∫ y, φ y) * unitTest x) :=
  ⟨hφ.1.sub (contDiff_const.mul unitTest_isTestFunction.1),
    hφ.2.1.sub unitTest_isTestFunction.2.1.mul_left, subset_univ _⟩

theorem integral_sub_integral_mul {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    ∫ x, (φ x - (∫ y, φ y) * unitTest x) = 0 := by
  have h1 : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have h2 : Integrable unitTest :=
    unitTest_isTestFunction.1.continuous.integrable_of_hasCompactSupport unitTest_isTestFunction.2.1
  rw [integral_sub h1 (h2.const_mul (∫ y, φ y)), integral_const_mul, unitTest_integral, mul_one, sub_self]

open Classical in
/-- The raw distribution of a canonical pairing: `φ ↦ L (φ - (∫ φ) unitTest)` on test functions, `0` otherwise. -/
noncomputable def rawOfCanon (L : S11n.CanonSpace) : (ℂ → ℝ) → ℝ :=
  fun φ => if h : IsTestFunction univ φ then
    L ⟨fun x => φ x - (∫ y, φ y) * unitTest x, isTestFunction_sub_integral_mul h, integral_sub_integral_mul h⟩
  else 0

theorem rawOfCanon_of_test {L : S11n.CanonSpace} {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    rawOfCanon L φ =
      L ⟨fun x => φ x - (∫ y, φ y) * unitTest x, isTestFunction_sub_integral_mul hφ, integral_sub_integral_mul hφ⟩ := by
  simp [rawOfCanon, hφ]

theorem measurable_rawOfCanon_apply {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    Measurable fun L : S11n.CanonSpace => rawOfCanon L φ := by
  simp only [rawOfCanon_of_test hφ]
  exact measurable_pi_apply _

/-- The lift `L ↦ rawOfCanon L` is measurable into the distribution σ-algebra. -/
theorem measurable_rawOfCanon : Measurable rawOfCanon := by
  refine measurable_iff_comap_le.2 ?_
  unfold distributionMeasurableSpace
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  refine iSup_le fun φ => iSup_le fun hφ => ?_
  exact measurable_iff_comap_le.1 (measurable_rawOfCanon_apply hφ)

/-- Measurability of the closed-set masses of the canonical lift (the decoder of `LQGMassFunctionalMeasurableFrozen`
composed with the lift). Holds for every dense family `q` with positive radii. -/
theorem measurable_canonClosedMass {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) (γ α₀ : ℝ) (S : Set ℂ) :
    Measurable fun L : S11n.CanonSpace => massDecoder hq γ α₀ S (rawOfCanon L) :=
  (measurable_massDecoder hq γ α₀ S).comp measurable_rawOfCanon

/-- Measurability of the open-set masses of the canonical lift. -/
theorem measurable_canonOpenMass {q : ℕ → ℝ × ℂ} (hq : ∀ m, 0 < (q m).1) (γ α₀ : ℝ) (U : Set ℂ) :
    Measurable fun L : S11n.CanonSpace => openMass hq γ α₀ U (rawOfCanon L) :=
  (measurable_openMass hq γ α₀ U).comp measurable_rawOfCanon

end HarmonicBalls.DecoderInputsDerived
