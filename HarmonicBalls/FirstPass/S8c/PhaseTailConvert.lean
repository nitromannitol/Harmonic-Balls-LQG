import HarmonicBalls.FirstPass.S8c.TorusFull
import HarmonicBalls.Proofs.Sec8.PhaseTorusLebesgue

/-! # The planar form of the torus phase tail (FIRST-PASS fp-S8c-8-2-local, G-8-2 section 3, eqs. (5)-(10))

`torusPhaseTail_of_dilation` (FirstPass/S8c/TorusFull.lean) gives the eventual block frequency of the torus-indexed
level-`n` good events, almost surely on `phaseTorusFieldMeasure P`, given a measure-preserving dilation `R` of the
field space, its ergodicity `hergT` for `T = (phaseTorusDouble, R)`, and the identity `hid`.

This file transports that statement to the planar form of `LocalPhaseTailStep` (FirstPass/S8c/PhaseTail.lean): almost
surely on `volume.prod P`, with the planar phase `x.1 : ℂ` and the field `x.2`, the good events are those of the
unnormalised measure `ν x.2`. The transport uses only: the quasi-measure-preserving map `phaseTorusOfComplex`
(Proofs/Sec8/PhaseTorusLebesgue.lean), the torus-to-plane identity `phaseVeryGoodAnnulus_torusPhase_ofComplex`
(Proofs/Sec8/PhaseTorus.lean), the almost-sure local finiteness of `ν`, `finitePart_eq_of_locallyFinite`, and the
identity between a block count and a block sum of indicators.

No new mathematics. The dilation `R`, `hergT` and `hid` stay hypotheses: they are the open steps (b) and (c) of
`LocalPhaseTailStep`, and their realisation on the field law is the operator's decision. -/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- A block count of a predicate on `[N+1, 2N]` is the block sum of its indicators. -/
theorem ncard_block_eq_sum (Q : ℕ → Prop) [DecidablePred Q] (N : ℕ) :
    ({n : ℕ | n ∈ Set.Icc (N + 1) (2 * N) ∧ Q n}.ncard : ℝ) =
      ∑ n ∈ Finset.Icc (N + 1) (2 * N), (if Q n then (1 : ℝ) else 0) := by
  have hset : {n : ℕ | n ∈ Set.Icc (N + 1) (2 * N) ∧ Q n} =
      ↑((Finset.Icc (N + 1) (2 * N)).filter Q) := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, Finset.coe_filter, Finset.mem_Icc]
  rw [hset, Set.ncard_coe_finset, Finset.sum_boole]

/-- Planar form of the phase tail: from the torus-indexed statement of `torusPhaseTail_of_dilation`, almost surely on
`volume.prod P` the planar block count of the good events (for the unnormalised `ν x.2`, at the planar phase `x.1`)
is eventually at least `(1 - ζ) N`. Hypotheses: as in `torusPhaseTail_of_dilation`, with `hν` measurability of `ν`. -/
theorem localPhaseTail_ae_of_dilation (hB : BirkhoffPointwiseErgodic.{u}) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure ℂ) (hν : Measurable ν)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (ha : 0 < a) (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (hbound : ∀ q : ℂ, P {ω | ¬ (PhaseVeryGoodAnnulus (ν ω) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ q ∧
      AnnulusBallComparison (ν ω) 0 0 m)} ≤ ENNReal.ofReal (ζ / 2))
    (R : Ω → Ω) (hR : MeasurePreserving R P P)
    (hergT : Ergodic (fun p : PhaseTorus × Ω => (phaseTorusDouble p.1, R p.2))
      (phaseTorusFieldMeasure P))
    (hid : ∀ n : ℕ, torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m n ν =
      (fun p : PhaseTorus × Ω => (phaseTorusDouble p.1, R p.2))^[n] ⁻¹'
        torusGoodLevel β N₀ a b C₁m C₁p C₂m C₂p C₃ m 0 ν) :
    ∀ᵐ x ∂((volume : Measure ℂ).prod P), ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Set.Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (ν x.2) β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ x.1 ∧
        AnnulusBallComparison (ν x.2) n 0 m}.ncard : ℝ) := by
  classical
  have hT := torusPhaseTail_of_dilation hB P ν hν hloc β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ ha hζ0 hζ1
    hbound R hR hergT hid
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

#print axioms localPhaseTail_ae_of_dilation

end HarmonicBalls
