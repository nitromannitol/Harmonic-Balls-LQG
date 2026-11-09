import Mathlib
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.Laplacian
import HarmonicBalls.Proofs.Sec11.ClosureScales.CutoffFourierSummability
import HarmonicBalls.Proofs.Sec11.ClosureScales.BorelCircleLimitDecoder

/-!
# Borel measurability of the Fourier finiteness test on the raw pairing carrier

The written Section 11 argument (`sec11-proof-r10.tex`, lines 1072-1089) makes a code valid only if its weighted
cos/sin Fourier square sums are finite for each cut-off, and states that this condition is Borel. The carrier is
the space `(ℂ → ℝ) → ℝ` of raw pairings `T`, with the pairing σ-algebra `pairingMeasSpace`: the σ-algebra generated
by the evaluations `T ↦ T φ` at test functions `φ` (`PalmPairingMeasurable`).

* `measurable_cutoffCoeff`: the literal cos/sin coefficient extraction is measurable into the countable product
  `ι × (ℤ × ℤ) × Bool → ℝ` (`true` for cosine, `false` for sine).
* `setOf_summable_eq_tsum_lt_top`: the literal finiteness set is the set where the `ENNReal.ofReal` tsum of its
  nonnegative terms is finite.
* `measurableSet_fourierFiniteness` and `measurableSet_fourierFiniteness_countable`: these sets are measurable for
  one cut-off, and for countably many cut-offs.
* `IsWholePlaneGFF.measurableSet_preimage_fourierFiniteness_countable`: pulled back along a whole-plane GFF, the
  event is measurable and has full probability, by the countable-cut-off conull theorem
  (`IsWholePlaneGFF.exists_measurable_conull_cutoffFourier_countable`).

No sample-wise linearity or continuity hypothesis is used, and no probability estimate is assumed.
-/

open MeasureTheory

noncomputable section

namespace HarmonicBalls

-- On raw pairings `(ℂ → ℝ) → ℝ` the measurable structure used in this file is the pairing σ-algebra.
attribute [local instance] pairingMeasSpace

/-- **Literal cos/sin coefficient extraction on the raw pairing.** For cut-offs `χ i` and a period `L`, the
coordinate `(i, k, true)` is `T (cutoffCosTest (χ i) L k)` and the coordinate `(i, k, false)` is
`T (cutoffSinTest (χ i) L k)`. -/
def cutoffCoeff {ι : Type*} (χ : ι → ℂ → ℝ) (L : ℝ) (T : (ℂ → ℝ) → ℝ) (p : ι × (ℤ × ℤ) × Bool) : ℝ :=
  if p.2.2 then T (cutoffCosTest (χ p.1) L p.2.1) else T (cutoffSinTest (χ p.1) L p.2.1)

/-- **Borel coefficient extraction.** The cos/sin coefficient extraction `T ↦ cutoffCoeff χ L T` is measurable from
the pairing σ-algebra into the countable product `ι × (ℤ × ℤ) × Bool → ℝ`, with the product σ-algebra. -/
theorem measurable_cutoffCoeff {ι : Type*} [Countable ι] (χ : ι → ℂ → ℝ)
    (hχ : ∀ i, IsTestFunction Set.univ (χ i)) (L : ℝ) :
    Measurable[pairingMeasSpace] (cutoffCoeff χ L) := by
  refine Measurable.of_eval fun p => ?_
  rcases p with ⟨i, k, b⟩
  cases b
  · exact measurable_pairing_eval (isTestFunction_cutoffSinTest (hχ i) L k)
  · exact measurable_pairing_eval (isTestFunction_cutoffCosTest (hχ i) L k)

/-- **Summability of nonnegative terms.** Nonnegative real terms are summable if and only if the tsum of their
`ENNReal.ofReal` is finite. -/
theorem summable_nonneg_iff_tsum_ofReal_lt_top {ι : Type*} {g : ι → ℝ} (hg : ∀ i, 0 ≤ g i) :
    Summable g ↔ ∑' i, ENNReal.ofReal (g i) < ⊤ := by
  refine ⟨fun hs => ?_, fun h => ?_⟩
  · rw [← ENNReal.ofReal_tsum_of_nonneg hg hs]
    exact ENNReal.ofReal_lt_top
  · exact (ENNReal.summable_toReal h.ne).congr fun i => ENNReal.toReal_ofReal (hg i)

/-- **Finiteness set as a tsum.** The literal set of raw pairings `T` whose weighted cos/sin Fourier square sums are
summable is the set where the `ENNReal.ofReal` tsum of the nonnegative terms is finite. -/
theorem setOf_summable_eq_tsum_lt_top {χ : ℂ → ℝ} (L : ℝ) :
    {T : (ℂ → ℝ) → ℝ | Summable (fun k : ℤ × ℤ =>
      (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) *
        ((T (cutoffCosTest χ L k)) ^ 2 + (T (cutoffSinTest χ L k)) ^ 2))} =
    {T : (ℂ → ℝ) → ℝ | ∑' k : ℤ × ℤ, ENNReal.ofReal ((1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) *
        ((T (cutoffCosTest χ L k)) ^ 2 + (T (cutoffSinTest χ L k)) ^ 2)) < ⊤} := by
  ext T
  exact summable_nonneg_iff_tsum_ofReal_lt_top fun k =>
    mul_nonneg (frequencyWeight_nonneg k) (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- **Borel part of the Fourier finiteness test (one cut-off).** For a test function `χ` and a period `L`, the set of
raw pairings whose weighted cos/sin Fourier square sums are summable is measurable for the pairing σ-algebra. -/
theorem measurableSet_fourierFiniteness {χ : ℂ → ℝ} (hχ : IsTestFunction Set.univ χ) (L : ℝ) :
    MeasurableSet[pairingMeasSpace] {T : (ℂ → ℝ) → ℝ | Summable (fun k : ℤ × ℤ =>
      (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) *
        ((T (cutoffCosTest χ L k)) ^ 2 + (T (cutoffSinTest χ L k)) ^ 2))} := by
  rw [setOf_summable_eq_tsum_lt_top L]
  refine measurableSet_lt (Measurable.tsum fun k => ?_) measurable_const
  exact (measurable_const.mul (((measurable_pairing_eval (isTestFunction_cutoffCosTest hχ L k)).pow_const 2).add
    ((measurable_pairing_eval (isTestFunction_cutoffSinTest hχ L k)).pow_const 2))).ennreal_ofReal

/-- **Borel part of the Fourier finiteness test (countably many cut-offs).** For countably many test functions `χ i`,
the set of raw pairings whose weighted cos/sin Fourier square sums are summable for every cut-off `χ i` is measurable
for the pairing σ-algebra. -/
theorem measurableSet_fourierFiniteness_countable {ι : Type*} [Countable ι] (χ : ι → ℂ → ℝ)
    (hχ : ∀ i, IsTestFunction Set.univ (χ i)) (L : ℝ) :
    MeasurableSet[pairingMeasSpace] {T : (ℂ → ℝ) → ℝ | ∀ i : ι, Summable (fun k : ℤ × ℤ =>
      (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) *
        ((T (cutoffCosTest (χ i) L k)) ^ 2 + (T (cutoffSinTest (χ i) L k)) ^ 2))} := by
  have hset : {T : (ℂ → ℝ) → ℝ | ∀ i : ι, Summable (fun k : ℤ × ℤ =>
      (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) *
        ((T (cutoffCosTest (χ i) L k)) ^ 2 + (T (cutoffSinTest (χ i) L k)) ^ 2))} =
      ⋂ i : ι, {T : (ℂ → ℝ) → ℝ | Summable (fun k : ℤ × ℤ =>
        (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) *
          ((T (cutoffCosTest (χ i) L k)) ^ 2 + (T (cutoffSinTest (χ i) L k)) ^ 2))} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  exact MeasurableSet.iInter fun i => measurableSet_fourierFiniteness (hχ i) L

/-- **Borel part of the Fourier finiteness test, pulled back along a whole-plane GFF (one cut-off).** The event that
the weighted cos/sin Fourier square sums of the field are summable is measurable on `Ω`, and has full probability. -/
theorem IsWholePlaneGFF.measurableSet_preimage_fourierFiniteness {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {χ : ℂ → ℝ} (hχ : IsTestFunction Set.univ χ) (L : ℝ) :
    MeasurableSet ((fun ω => hC ω) ⁻¹' {T : (ℂ → ℝ) → ℝ | Summable (fun k : ℤ × ℤ =>
      (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) *
        ((T (cutoffCosTest χ L k)) ^ 2 + (T (cutoffSinTest χ L k)) ^ 2))}) ∧
      P ((fun ω => hC ω) ⁻¹' {T : (ℂ → ℝ) → ℝ | Summable (fun k : ℤ × ℤ =>
        (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) *
          ((T (cutoffCosTest χ L k)) ^ 2 + (T (cutoffSinTest χ L k)) ^ 2))})ᶜ = 0 := by
  obtain ⟨S, -, hS0, hSs⟩ := hG.exists_measurable_conull_cutoffFourier hχ L
  exact ⟨measurable_pairing_field hG (measurableSet_fourierFiniteness hχ L),
    measure_mono_null (fun ω hω hS => hω (hSs ω hS)) hS0⟩

/-- **Borel part of the Fourier finiteness test, pulled back along a whole-plane GFF (countably many cut-offs).**
The event that the weighted cos/sin Fourier square sums of the field are summable for every cut-off `χ i` is
measurable on `Ω`, and has full probability: the countable-cut-off conull theorem supplies the full-measure event. -/
theorem IsWholePlaneGFF.measurableSet_preimage_fourierFiniteness_countable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {ι : Type*} [Countable ι] (χ : ι → ℂ → ℝ) (hχ : ∀ i, IsTestFunction Set.univ (χ i)) (L : ℝ) :
    MeasurableSet ((fun ω => hC ω) ⁻¹' {T : (ℂ → ℝ) → ℝ | ∀ i : ι, Summable (fun k : ℤ × ℤ =>
      (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) *
        ((T (cutoffCosTest (χ i) L k)) ^ 2 + (T (cutoffSinTest (χ i) L k)) ^ 2))}) ∧
      P ((fun ω => hC ω) ⁻¹' {T : (ℂ → ℝ) → ℝ | ∀ i : ι, Summable (fun k : ℤ × ℤ =>
        (1 + (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2) ^ (-2 : ℤ) *
          ((T (cutoffCosTest (χ i) L k)) ^ 2 + (T (cutoffSinTest (χ i) L k)) ^ 2))})ᶜ = 0 := by
  obtain ⟨S, -, hS0, hSs⟩ := hG.exists_measurable_conull_cutoffFourier_countable χ hχ L
  exact ⟨measurable_pairing_field hG (measurableSet_fourierFiniteness_countable χ hχ L),
    measure_mono_null (fun ω hω hS => hω (hSs ω hS)) hS0⟩

end HarmonicBalls

end
