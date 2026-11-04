import HarmonicBalls.Proofs.Sec8.PhasePeriodicity
import HarmonicBalls.Proofs.Sec8.JointVeryGoodMeasurable

/-! # Joint measurability of the common phase

A common phase is removed by translating both the measure and the centre.
This makes the phase-dependent lattice event measurable jointly in all three. -/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- With a common phase at every inner scale, criterion three is jointly
measurable in a locally finite measure, centre, and phase. -/
theorem measurableSet_phaseVeryGoodCriterionThree_joint
    {A : Type*} [MeasurableSpace A] {μ : A → Measure ℂ} {c phase : A → ℂ}
    (hμ : Measurable μ) (hfinite : ∀ x, IsLocallyFiniteMeasure (μ x))
    (hc : Measurable c) (hphase : Measurable phase)
    (ρ : ℝ) (hρ : 0 < ρ) (N : ℕ) (a b C₃ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) :
    MeasurableSet {x : A |
      PhaseVeryGoodCriterionThree (μ x) ρ (c x) N a b C₃ (fun _ => phase x)} := by
  let ν : A → Measure ℂ := fun x => (μ x).map (fun z => z - phase x)
  have hν : Measurable ν := Section6.measurable_map_of_locallyFinite hμ hfinite
    (measurable_snd.sub (hphase.comp measurable_fst))
  have hm := measurableSet_veryGoodAnnulus_goodScales_joint hν (hc.sub hphase)
    ρ hρ N a b C₃ hunit
  convert hm using 1
  ext x
  have h := phaseVeryGoodCriterionThree_map_add (μ x) ρ (c x) (-phase x)
    N a b C₃ (fun _ => phase x)
  simp only [add_neg_cancel, phaseVeryGoodCriterionThree_zero, ← sub_eq_add_neg] at h
  simp only [mem_ofPred_eq, Pi.sub_apply]
  constructor
  · intro hp
    have hp' := h.mpr hp
    intro n hn z hz hl
    exact hp' n hn z ⟨hl, hz⟩
  · intro hp
    apply h.mp
    intro n hn z hz
    exact hp n hn z hz.2 hz.1

/-- The two mass-ratio bounds and the phase-shifted third criterion are
jointly measurable. -/
theorem measurableSet_phaseVeryGoodAnnulus_joint
    {A : Type*} [MeasurableSpace A] {μ : A → Measure ℂ} {c phase : A → ℂ}
    (hμ : Measurable μ) (hfinite : ∀ x, IsLocallyFiniteMeasure (μ x))
    (hc : Measurable c) (hphase : Measurable phase)
    (β ρ : ℝ) (hρ : 0 < ρ) (N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) :
    MeasurableSet {x : A |
      annulusBallMassSize (μ x) β ρ (c x) / (μ x) (annulus (c x) (ρ / 4) (2 * ρ)) ∈
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p) ∧
      annulusGreenPotentialSup (μ x) (c x) (ρ / 4) (2 * ρ) /
          (μ x) (annulus (c x) (ρ / 4) (2 * ρ)) ∈
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p) ∧
      PhaseVeryGoodCriterionThree (μ x) ρ (c x) N a b C₃ (fun _ => phase x)} := by
  obtain ⟨hball, hgreen⟩ := measurable_veryGoodAnnulus_sizeRatios_joint hμ hfinite hc β ρ hρ
  exact (isClosed_Icc.measurableSet.preimage hball).inter
    ((isClosed_Icc.measurableSet.preimage hgreen).inter
      (measurableSet_phaseVeryGoodCriterionThree_joint hμ hfinite hc hphase ρ hρ N a b C₃ hunit))

/-- A uniform fixed-phase bound also controls an independently sampled phase.
The measure on phases may be any probability measure. -/
theorem measure_prod_not_phaseVeryGoodCriterionThree_le
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (P : Measure Ω) [SFinite P] (Q : Measure T) [IsProbabilityMeasure Q]
    {μ : Ω → Measure ℂ} (hμ : Measurable μ)
    (hfinite : ∀ ω, IsLocallyFiniteMeasure (μ ω))
    {phase : T → ℂ} (hphase : Measurable phase)
    (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (N : ℕ) (a b C₃ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {δ : ℝ≥0∞} (hbound : ∀ q : ℂ,
      P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) ρ x N a b C₃ (fun _ => q)} ≤ δ) :
    (Q.prod P) {p : T × Ω |
      ¬ PhaseVeryGoodCriterionThree (μ p.2) ρ x N a b C₃ (fun _ => phase p.1)} ≤ δ := by
  have hs : MeasurableSet {p : T × Ω |
      ¬ PhaseVeryGoodCriterionThree (μ p.2) ρ x N a b C₃ (fun _ => phase p.1)} :=
    (measurableSet_phaseVeryGoodCriterionThree_joint (hμ.comp measurable_snd)
      (fun p => hfinite p.2) measurable_const (hphase.comp measurable_fst)
      ρ hρ N a b C₃ hunit).compl
  rw [Measure.prod_apply hs]
  calc
    _ ≤ ∫⁻ _ : T, δ ∂Q := lintegral_mono (fun t => hbound (phase t))
    _ = δ := by simp

end HarmonicBalls
