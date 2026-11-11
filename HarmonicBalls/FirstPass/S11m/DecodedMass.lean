import HarmonicBalls.FirstPass.S11m.DecodedRaw
import HarmonicBalls.Steps.Sec11.PinchGreenMeasurable

/-!
# Decoded masses of the local second event

Route: the mass clauses of `E₂(M)`
(`pinchSecondEventLocal`, `FirstPass/S11h/LocalEvents.lean:45`): the decoded mass of `U` and the decoded annulus Green
potential sup `S = SG_{3,6}` are read off a decoded measure `Φ ℓ : Measure ℂ`. If the decoder returns `c • (μ|B)` with
`c ∈ (0, ∞)` and the balls `U`, `annulus 0 3 6` lie in `B`, then both masses equal `c` times the true masses of `μ`.
Deterministic, measurability in the pairing for measurable `Φ`.
-/

namespace HarmonicBalls.S11m

open Set MeasureTheory
open scoped ENNReal

/-- Decoded mass of a set `U`: the decoded measure `Φ ℓ` evaluated on `U`. -/
def decMassU {X : Type*} (Φ : X → Measure ℂ) (U : Set ℂ) (ℓ : X) : ℝ≥0∞ :=
  Φ ℓ U

/-- Decoded annulus Green potential sup `S = SG_{3,6}(0)` of the decoded measure `Φ ℓ`. -/
noncomputable def decGreen {X : Type*} (Φ : X → Measure ℂ) (ℓ : X) : ℝ≥0∞ :=
  annulusGreenPotentialSup (Φ ℓ) 0 3 6

/-- The decoded mass of a measurable set is measurable in the pairing (`Measure.measurable_measure`). -/
theorem measurable_decMassU {X : Type*} [MeasurableSpace X] {Φ : X → Measure ℂ} (hΦ : Measurable Φ) {U : Set ℂ} (hU : MeasurableSet U) :
    Measurable (decMassU Φ U) :=
  (Measure.measurable_measure.mp hΦ) U hU

/-- The decoded annulus Green potential sup is measurable in the pairing (`measurable_annulusGreenPotentialSup`). -/
theorem measurable_decGreen {X : Type*} [MeasurableSpace X] {Φ : X → Measure ℂ} (hΦ : Measurable Φ) :
    Measurable (decGreen Φ) :=
  (HarmonicBalls.measurable_annulusGreenPotentialSup 0 3 6).comp hΦ

/-- Mass of a rescaled restriction: if `U ⊆ B` and `B` is measurable, then `(c • μ|B) U = c · μ U`. -/
theorem decMassU_smul_restrict {μ : Measure ℂ} {B U : Set ℂ} (hB : MeasurableSet B) (hU : U ⊆ B) (c : ℝ≥0∞) :
    (c • μ.restrict B) U = c * μ U := by
  rw [Measure.smul_apply, Measure.restrict_apply' hB, smul_eq_mul, Set.inter_eq_left.mpr hU]

/-- Deterministic decoded masses: if `Φ ℓ = c • (μ|B)` with `U ⊆ B` and `annulus 0 3 6 ⊆ B`, then the decoded mass of
`U` is `c · μ(U)` and the decoded annulus Green potential sup is `c · SG_{3,6}(μ)`. -/
theorem decodedMasses_of_restrict {μ : Measure ℂ} {B U : Set ℂ} (hB : MeasurableSet B) (hU : U ⊆ B)
    (hsub : annulus (0 : ℂ) 3 6 ⊆ B) {c : ℝ≥0∞} {ν : Measure ℂ} (h : ν = c • μ.restrict B) :
    ν U = c * μ U ∧ annulusGreenPotentialSup ν 0 3 6 = c * annulusGreenPotentialSup μ 0 3 6 := by
  subst h
  exact ⟨decMassU_smul_restrict hB hU c, annulusGreenPotentialSup_smul_restrict c hsub⟩

/-- Almost sure decoded masses. If a.s. the decoder returns `c • (μ ω|B)` for some `c ∈ (0, ∞)`, then a.s. the decoded
masses of `U` and `SG_{3,6}` are `c` times the masses of `μ ω` (for one and the same `c`). -/
theorem decodedMasses_ae {X Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} (Φ : X → Measure ℂ) (ℓ : Ω → X)
    (μ : Ω → Measure ℂ) {B U : Set ℂ} (hB : MeasurableSet B) (hU : U ⊆ B) (hsub : annulus (0 : ℂ) 3 6 ⊆ B)
    (h : ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ Φ (ℓ ω) = c • (μ ω).restrict B) :
    ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
      decMassU Φ U (ℓ ω) = c * μ ω U ∧ decGreen Φ (ℓ ω) = c * annulusGreenPotentialSup (μ ω) 0 3 6 := by
  filter_upwards [h] with ω hω
  obtain ⟨c, hc0, hctop, hΦω⟩ := hω
  exact ⟨c, hc0, hctop, (decodedMasses_of_restrict hB hU hsub hΦω).1,
    (decodedMasses_of_restrict hB hU hsub hΦω).2⟩

end HarmonicBalls.S11m
