import HarmonicBalls.FirstPass.S8c.PhaseTailConvert

/-! # FIRST-PASS helper (fp-S8d, owner n4): the phase tail with the dilation identity almost surely

S8c's `torusPhaseTail_of_dilation` (FirstPass/S8c/TorusFull.lean) and `localPhaseTail_ae_of_dilation`
(FirstPass/S8c/PhaseTailConvert.lean) take the dilation identity `hid` pointwise. The coordinate change of LQG
measures (Proposed/LQG.lean, `LQGMeasureCoordChange`) only holds almost surely, so for a dilation of a profile
space the identity holds for almost every point, for each level `n`.

This file proves the same two statements under the almost-sure identity `hid_ae`. The torus form applies the generic
`ae_frequency_of_torus_dilation` (FirstPass/S8c/TorusTail.lean) to the preimage sequence `T^[n]⁻¹' G`, for which the
identity holds pointwise, and transfers the block sums along the almost-sure equalities of the level sets. The planar
form is the proof of `localPhaseTail_ae_of_dilation` with the torus form replaced. No new mathematics. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- The torus-indexed phase tail under the dilation identity holding almost surely for each level. -/
theorem torusPhaseTail_of_dilation_ae (hB : BirkhoffPointwiseErgodic.{u}) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure ℂ) (hν : Measurable ν)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (ha : 0 < a) (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (hbound : ∀ q : ℂ, P {ω | ¬ (PhaseVeryGoodAnnulus (ν ω) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ q ∧
      AnnulusBallComparison (ν ω) 0 0 m)} ≤ ENNReal.ofReal (ζ / 2))
    (R : Ω → Ω) (hR : MeasurePreserving R P P)
    (hergT : Ergodic (fun p : PhaseTorus × Ω => (phaseTorusDouble p.1, R p.2))
      (phaseTorusFieldMeasure P))
    (hid_ae : ∀ n : ℕ, torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m n ν =ᵐ[phaseTorusFieldMeasure P]
      (fun p : PhaseTorus × Ω => (phaseTorusDouble p.1, R p.2))^[n] ⁻¹'
        torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m 0 ν) :
    ∀ᵐ p ∂(phaseTorusFieldMeasure P), ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤
        ∑ n ∈ Finset.Icc (N + 1) (2 * N),
          (torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m n ν).indicator (1 : PhaseTorus × Ω → ℝ) p := by
  classical
  have hF := ae_frequency_of_torus_dilation hB P R hR hergT
    (torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m 0 ν)
    (measurableSet_torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m ha ν hν 0) ζ hζ0 hζ1
    (fun θ => torusGoodLevel_section_failure_le P ν hloc β N₀ a b C₁m C₁p C₂m C₂p C₃ m
      (ENNReal.ofReal (ζ / 2)) hbound θ)
    (fun n => (fun p : PhaseTorus × Ω => (phaseTorusDouble p.1, R p.2))^[n] ⁻¹'
      torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m 0 ν)
    (fun n => rfl)
  have hEq : ∀ᵐ p ∂(phaseTorusFieldMeasure P), ∀ n : ℕ,
      (torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m n ν).indicator (1 : PhaseTorus × Ω → ℝ) p =
        ((fun p : PhaseTorus × Ω => (phaseTorusDouble p.1, R p.2))^[n] ⁻¹'
          torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m 0 ν).indicator (1 : PhaseTorus × Ω → ℝ) p := by
    rw [ae_all_iff]
    intro n
    filter_upwards [hid_ae n] with p hp
    simp only [Set.indicator_apply]
    exact if_congr hp.to_iff rfl rfl
  filter_upwards [hF, hEq] with p hp1 hp2
  refine hp1.mono fun N hN => le_trans hN (le_of_eq ?_)
  exact Finset.sum_congr rfl fun n _ => by rw [hp2 n]

/-- Planar form of the phase tail under the almost-sure dilation identity: the planar version of
`localPhaseTail_ae_of_dilation` (FirstPass/S8c/PhaseTailConvert.lean) with `hid` replaced by `hid_ae`. -/
theorem localPhaseTail_ae_of_dilation_ae (hB : BirkhoffPointwiseErgodic.{u}) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure ℂ) (hν : Measurable ν)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (ha : 0 < a) (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (hbound : ∀ q : ℂ, P {ω | ¬ (PhaseVeryGoodAnnulus (ν ω) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ q ∧
      AnnulusBallComparison (ν ω) 0 0 m)} ≤ ENNReal.ofReal (ζ / 2))
    (R : Ω → Ω) (hR : MeasurePreserving R P P)
    (hergT : Ergodic (fun p : PhaseTorus × Ω => (phaseTorusDouble p.1, R p.2))
      (phaseTorusFieldMeasure P))
    (hid_ae : ∀ n : ℕ, torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m n ν =ᵐ[phaseTorusFieldMeasure P]
      (fun p : PhaseTorus × Ω => (phaseTorusDouble p.1, R p.2))^[n] ⁻¹'
        torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m 0 ν) :
    ∀ᵐ x ∂((volume : Measure ℂ).prod P), ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Set.Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (ν x.2) β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ x.1 ∧
        AnnulusBallComparison (ν x.2) n 0 m}.ncard : ℝ) := by
  classical
  have hT := torusPhaseTail_of_dilation_ae hB P ν hν hloc β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ ha hζ0 hζ1
    hbound R hR hergT hid_ae
  have hQ : QuasiMeasurePreserving (Prod.map phaseTorusOfComplex id) ((volume : Measure ℂ).prod P)
      (((volume : Measure PhaseCircle).prod (volume : Measure PhaseCircle)).prod P) :=
    QuasiMeasurePreserving.prodMap quasiMeasurePreserving_phaseTorusOfComplex
      (QuasiMeasurePreserving.id P)
  have hloc' : ∀ᵐ x ∂((volume : Measure ℂ).prod P), IsLocallyFiniteMeasure (ν x.2) :=
    (Measure.quasiMeasurePreserving_snd).ae hloc
  filter_upwards [hQ.ae hT, hloc'] with x hx hxl
  have hfp : finitePart (ν x.2) = ν x.2 := by
    have := hxl
    exact finitePart_eq_of_locallyFinite (ν x.2)
  have hind : ∀ n : ℕ, (torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m n ν).indicator
      (1 : PhaseTorus × Ω → ℝ) (phaseTorusOfComplex x.1, x.2) =
      if PhaseVeryGoodAnnulus (ν x.2) β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ x.1 ∧
          AnnulusBallComparison (ν x.2) n 0 m then (1 : ℝ) else 0 := by
    intro n
    simp only [torusGoodLevel, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply, hfp,
      phaseVeryGoodAnnulus_torusPhase_ofComplex]
  refine hx.mono fun N hN => ?_
  refine le_trans hN (le_of_eq ?_)
  refine Eq.trans ?_ (ncard_block_eq_sum _ N).symm
  exact Finset.sum_congr rfl fun n _ => hind n

#print axioms torusPhaseTail_of_dilation_ae
#print axioms localPhaseTail_ae_of_dilation_ae

end HarmonicBalls
