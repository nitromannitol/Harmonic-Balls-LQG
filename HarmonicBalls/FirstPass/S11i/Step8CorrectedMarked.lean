import Mathlib
import HarmonicBalls.FirstPass.S11i.Step8TransferMarked
import HarmonicBalls.FirstPass.S11i.ReferenceNull
import HarmonicBalls.FirstPass.S11r.MarkedObs
import HarmonicBalls.FirstPass.S11i.AnnularWeylAbsCont

/-!
# Corrected marked transfer with a zero-insertion DMS measure (Step 8, fp-S11i-11-13f, n3)

Operator ruling (chat 198, `notes/fp-gaps/CHATGPT-hb-11-13-step8-Q1-Q2.md`):
* The marked DMS identity `DMSLemmaA10WholePlaneMarked` is applied to the zero-insertion measure `μ0`
  (`IsLQGMeasureOfField P γ 0`), not to the target measure `μα` (`IsLQGMeasureOfField P γ α₀`).
* The DMS test set is the pullback `dmsLocalGood α₀ D Bad` of a measurable LOCAL failure set `Bad` of marked
  observations (`campbellMarkedObs`), not the global `canonicalFailure` complement.
* The shifted raw pairing is identified with the reference observation by the exact mean-zero identity
  `campbellMarkedObs_dmsShiftedPairing` (n2, S11r/MarkedObs.lean; NOT YET LANDED). It enters here as the
  hypothesis `hDshift`.
* The transfer `μ0 → μα` on the unit ball uses the annular Weyl-scaling absolute continuity (lh's z-worker; NOT YET
  LANDED). It enters here as the hypothesis `hac`.

No new frozen input; the file is placeholder-free. The Tonelli step is `ae_ae_ball_of_marked_of_ae_volume'`
(`Step8TransferMarked.lean`, hypothesis-free form).
-/

universe u

namespace HarmonicBalls.FirstPassS11iStep8Corrected

open MeasureTheory Filter Topology Set Metric ProbabilityTheory
open scoped ENNReal
open HarmonicBalls HarmonicBalls.S11c
open HarmonicBalls.FirstPassS11iStep8Transfer

/-- The good set of raw pairings for the DMS step (ruling Q2): `(T, z)` is good when the local marked observation
`campbellMarkedObs α₀ D T z = (z, mod-constant pairings of h = T - α₀ log|·| with mean-zero tests in D)` is not in the local
failure set `Bad`. It is the pullback of the complement of `Bad` by the marked observation. -/
def dmsLocalGood (α₀ : ℝ) (D : Set ℂ)
    (Bad : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ))) :
    Set (((ℂ → ℝ) → ℝ) × ℂ) :=
  {p | campbellMarkedObs α₀ D p.1 p.2 ∉ Bad}

/-- Evaluation at a test function is measurable for the pairing σ-algebra of `(fun T => T)` over `univ`. -/
theorem measurable_eval_pairingSigmaAlgebra (φ : ℂ → ℝ) (hφ : IsTestFunction Set.univ φ) :
    Measurable[pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ] (fun T : (ℂ → ℝ) → ℝ => T φ) :=
  Measurable.of_comap_le
    (le_iSup₂ (f := fun φ (_ : IsTestFunction Set.univ φ) =>
      MeasurableSpace.comap (fun T : (ℂ → ℝ) → ℝ => T φ) inferInstance) φ hφ)

/-- The marked observation map `(T, z) ↦ campbellMarkedObs α₀ D T z` is measurable for the product of the pairing
σ-algebra and the Borel σ-algebra of `ℂ`. -/
theorem measurable_campbellMarkedObs (α₀ : ℝ) (D : Set ℂ) :
    Measurable[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance]
      (fun p : ((ℂ → ℝ) → ℝ) × ℂ => campbellMarkedObs α₀ D p.1 p.2) := by
  let _ : MeasurableSpace ((ℂ → ℝ) → ℝ) := pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ
  unfold campbellMarkedObs
  refine Measurable.prodMk measurable_snd ?_
  refine Measurable.of_eval (fun φ => ?_)
  unfold fieldPairing
  have hφU : IsTestFunction Set.univ φ.1 := ⟨φ.2.1.1, φ.2.1.2.1, Set.subset_univ _⟩
  exact ((measurable_eval_pairingSigmaAlgebra φ.1 hφU).comp measurable_fst).sub measurable_const

/-- The good set is measurable for the DMS pairing σ-algebra as soon as the local failure set `Bad` is measurable. -/
theorem measurableSet_dmsLocalGood (α₀ : ℝ) (D : Set ℂ)
    {Bad : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ))} (hBad : MeasurableSet Bad) :
    MeasurableSet[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance]
      (dmsLocalGood α₀ D Bad) :=
  hBad.compl.preimage (measurable_campbellMarkedObs α₀ D)

/-- **Corrected marked transfer to the target measure (Step 8, zero-insertion DMS).**
Input: the marked DMS identity for the zero-insertion measure `μ0`; the mean-zero identity `hDshift` (n2,
`campbellMarkedObs_dmsShiftedPairing`, for every domain); the reference-observation statement `href` (a.e. root `z` in the
unit ball, `P`-a.s., the reference observation avoids the local failure set `Bad`); and the absolute continuity `hac` of the
target unit-ball restriction of `μα` with respect to that of `μ0` (annular Weyl scaling, lh's z-worker).
Output: `P`-a.s., for `μα`-a.e. `z` in the unit ball, the target marked observation avoids `Bad`. -/
theorem ae_marked_local_transfer {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    (γ α₀ : ℝ) (D : Set ℂ) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (μ0 μα : Ω → Measure ℂ)
    (hA10 : DMSLemmaA10WholePlaneMarked P γ hC hcirc μ0)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ0 : IsLQGMeasureOfField P γ 0 hcirc μ0)
    (hDshift : ∀ (D' : Set ℂ) (T : (ℂ → ℝ) → ℝ) (z : ℂ) (h10 : ℝ),
      campbellMarkedObs α₀ D' (dmsShiftedPairing γ z T h10) z = campbellReferenceObs γ α₀ D' T z)
    (Bad : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ))) (hBad : MeasurableSet Bad)
    (href : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (0 : ℂ) 1 →
      ∀ᵐ ω ∂P, campbellReferenceObs γ α₀ D (hC ω) z ∉ Bad)
    (hac : ∀ᵐ ω ∂P, (μα ω).restrict (ball (0 : ℂ) 1) ≪ (μ0 ω).restrict (ball (0 : ℂ) 1)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μα ω), z ∈ ball (0 : ℂ) 1 → campbellMarkedObs α₀ D (hC ω) z ∉ Bad := by
  have hleb : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (0 : ℂ) 1 →
      ∀ᵐ ω ∂P, (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) ∈ dmsLocalGood α₀ D Bad := by
    filter_upwards [href] with z hz hzB1
    filter_upwards [hz hzB1] with ω hω
    show campbellMarkedObs α₀ D (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) z ∉ Bad
    rw [hDshift]
    exact hω
  have h0 := ae_ae_ball_of_marked_of_ae_volume' P γ hC hcirc μ0 hA10 hGFF hμ0 (dmsLocalGood α₀ D Bad)
    (measurableSet_dmsLocalGood α₀ D hBad) hleb
  filter_upwards [h0, hac] with ω hω hacω
  have h1 : ∀ᵐ z ∂((μ0 ω).restrict (ball (0 : ℂ) 1)), (hC ω, z) ∈ dmsLocalGood α₀ D Bad := by
    rw [ae_restrict_iff' measurableSet_ball]
    exact hω
  have h2 : ∀ᵐ z ∂((μα ω).restrict (ball (0 : ℂ) 1)), (hC ω, z) ∈ dmsLocalGood α₀ D Bad :=
    hacω.ae_le h1
  rw [ae_restrict_iff' measurableSet_ball] at h2
  exact h2

/-- **Corrected marked transfer with the landed inputs (Step 8, fp-S11i-11-13f round 63).** Same conclusion as
`ae_marked_local_transfer`; its two named inputs are discharged by landed lemmas:
* the mean-zero identity `hDshift` is `campbellMarkedObs_dmsShiftedPairing` (n2, `S11r/MarkedObs.lean`);
* the absolute continuity `hac` is `insertedMeasure_ac_zeroInsertion_on_unitBall` (`S11i/AnnularWeylAbsCont.lean`),
  which uses the frozen Weyl relation `hWeyl` (`Frozen/S8c.lean:73`).
Remaining inputs: the frozen DMS marked identity `hA10` for the zero-insertion measure `μ0`; `hμ0`, `hμα`; the atom-at-zero
hypotheses `hNon0` (forwarded to the binder `_hNon0` of the absolute continuity lemma, which does not use it) and `hNonα`;
the measurable local failure set `Bad` and the reference-observation statement `href`. -/
theorem ae_marked_local_transfer_landed {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (γ α₀ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (D : Set ℂ) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (μ0 μα : Ω → Measure ℂ)
    (hA10 : DMSLemmaA10WholePlaneMarked P γ hC hcirc μ0)
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ0 : IsLQGMeasureOfField P γ 0 hcirc μ0) (hμα : IsLQGMeasureOfField P γ α₀ hcirc μα)
    (hNon0 : ∀ᵐ ω ∂P, μ0 ω {0} = 0) (hNonα : ∀ᵐ ω ∂P, μα ω {0} = 0)
    (Bad : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ))) (hBad : MeasurableSet Bad)
    (href : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (0 : ℂ) 1 →
      ∀ᵐ ω ∂P, campbellReferenceObs γ α₀ D (hC ω) z ∉ Bad) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μα ω), z ∈ ball (0 : ℂ) 1 → campbellMarkedObs α₀ D (hC ω) z ∉ Bad := by
  have hac := HarmonicBalls.FirstPassS11iAnnularWeylAbsCont.insertedMeasure_ac_zeroInsertion_on_unitBall
    hWeyl P γ α₀ hC hcirc μ0 μα hGFF hγ0 hγ2 hα hμ0 hμα hNon0 hNonα
  exact ae_marked_local_transfer γ α₀ D μ0 μα hA10 hGFF hμ0
    (fun D' T z h10 => campbellMarkedObs_dmsShiftedPairing γ α₀ D' T z h10) Bad hBad href hac

end HarmonicBalls.FirstPassS11iStep8Corrected

#print axioms HarmonicBalls.FirstPassS11iStep8Corrected.ae_marked_local_transfer
#print axioms HarmonicBalls.FirstPassS11iStep8Corrected.ae_marked_local_transfer_landed
