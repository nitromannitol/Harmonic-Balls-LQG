import HarmonicBalls.Proofs.Sec8.PhaseFrequencyLocality
import HarmonicBalls.Proofs.Sec8.PhaseTorusLawTransfer

/-! # Transfer of phase frequency from local normalized laws

The imported ergodic theorem is due to Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. Local law domination is an
explicit hypothesis, not a field-law input.
-/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A normalized restriction is a measurable locally finite-measure-valued
function of a locally finite measure. -/
noncomputable def localNormalizedMeasure (ε : ℝ)
    (μ : {ν : Measure ℂ // IsLocallyFiniteMeasure ν}) :
    {ν : Measure ℂ // IsLocallyFiniteMeasure ν} :=
  ⟨normalizedRestriction μ.val (ball 0 ε), inferInstance⟩

theorem measurable_localNormalizedMeasure (ε : ℝ) : Measurable (localNormalizedMeasure ε) := by
  apply Measurable.subtype_mk
  exact (measurable_normalizedRestriction_measure _ isOpen_ball.measurableSet).comp
    measurable_subtype_coe

/-- A phase-frequency estimate transfers using only laws of normalized
restrictions to a fixed neighborhood. Local domination and the positivity of
both neighborhood masses are explicit. -/
theorem ae_ae_veryGoodComparableScaleFrequency_of_local_recentered_law
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → {ν : Measure ℂ // IsLocallyFiniteMeasure ν}) (hU : Measurable U)
    (ρ : Measure ℂ) (hρ : ρ ≪ volume) (S : ℂ → Measure Ξ)
    (F : ℂ → Ξ → {ν : Measure ℂ // IsLocallyFiniteMeasure ν})
    (hF : ∀ᵐ z ∂ρ, AEMeasurable (F z) (S z))
    (ε : ℝ) (hε : 0 < ε)
    (hUpos : ∀ᵐ ω ∂P, (U ω).val (ball 0 ε) ≠ 0 ∧ (U ω).val (ball 0 ε) ≠ ∞)
    (hFpos : ∀ᵐ z ∂ρ, ∀ᵐ ω ∂(S z),
      (F z ω).val (ball 0 ε) ≠ 0 ∧ (F z ω).val (ball 0 ε) ≠ ∞)
    (hdom : ∀ᵐ z ∂ρ, (S z).map (fun ω => localNormalizedMeasure ε (F z ω)) ≪
      P.map (fun ω => localNormalizedMeasure ε (U ω)))
    (M : ℂ → Ξ → Measure ℂ)
    (hcenter : ∀ᵐ z ∂ρ, ∀ᵐ ω ∂(S z),
      (M z ω).map (fun w : ℂ => w - z) = (F z ω).val)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    (hphase : ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
        ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
          AnnulusBallComparison (U p.2).val n 0 m}.ncard : ℝ)) :
    ∀ᵐ z ∂ρ, ∀ᵐ ω ∂(S z), ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ (veryGoodComparableScaleCount (M z ω) β z N₀
        a b C₁m C₁p C₂m C₂p C₃ m N : ℝ) := by
  let L := {ν : Measure ℂ // IsLocallyFiniteMeasure ν}
  let Q : Measure PhaseTorus := (volume : Measure PhaseCircle).prod volume
  let A : PhaseTorus → L → Prop := fun t ν => ∀ᶠ N : ℕ in atTop,
    (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
      PhaseVeryGoodAnnulus ν.val β (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ (torusPhase t) ∧
      AnnulusBallComparison ν.val n 0 m}.ncard : ℝ)
  have hAm : MeasurableSet {p : PhaseTorus × L | A p.1 p.2} :=
    measurableSet_phaseTorus_blockFrequency β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit
  let V : Ω → L := fun ω => localNormalizedMeasure ε (U ω)
  have hV : Measurable V := (measurable_localNormalizedMeasure ε).comp hU
  have hphaseV : ∀ᵐ p ∂(Q.prod P), A p.1 (V p.2) := by
    filter_upwards [hphase, Measure.quasiMeasurePreserving_snd.ae hUpos] with p hp hm
    exact (phaseVeryGoodComparable_blockFrequency_iff_normalizedRestriction (U p.2).val
      hε hm.1 hm.2 β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ (fun _ => torusPhase p.1)).1 hp
  have hmap : Q.prod (P.map V) = (Q.prod P).map (Prod.map id V) := by
    simpa only [Measure.map_id] using Measure.map_prod_map Q P measurable_id hV
  have hlaw : ∀ᵐ p ∂(Q.prod (P.map V)), A p.1 p.2 := by
    rw [hmap, ae_map_iff (measurable_id.prodMap hV).aemeasurable hAm]
    exact hphaseV
  have htrans := ae_ae_negative_centerPhase_of_ae_prod_of_dominated (P.map V) ρ hρ
    (fun z => (S z).map (fun ω => localNormalizedMeasure ε (F z ω))) hdom (A := A) hlaw
  filter_upwards [htrans, hF, hFpos, hcenter] with z hz hf hp hc
  have hz' : ∀ᵐ ω ∂(S z), A (phaseTorusOfComplex (-z)) (localNormalizedMeasure ε (F z ω)) :=
    ae_of_ae_map ((measurable_localNormalizedMeasure ε).comp_aemeasurable hf) hz
  filter_upwards [hz', hp, hc] with ω hω hmass hcenterω
  have hfreq := (phaseVeryGoodComparable_blockFrequency_iff_normalizedRestriction (F z ω).val
    hε hmass.1 hmass.2 β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ
      (fun _ => torusPhase (phaseTorusOfComplex (-z)))).2 hω
  filter_upwards [hfreq] with N hN
  rw [veryGoodComparableScaleCount_eq_centered_torus, hcenterω]
  exact hN

/-- Rooted frequency follows from the rooted-law comparison and domination
of the normalized local recentered measure laws. -/
theorem ae_ae_rooted_veryGoodComparableScaleFrequency_of_local_recentered_law
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) [SFinite P] {μ : Ω → Measure ℂ} (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (S : Measure Ω) (hPdom : P ≪ S)
    (hμS : AEMeasurable μ S) (hlocS : ∀ᵐ ω ∂S, IsLocallyFiniteMeasure (μ ω))
    (P₀ : Measure Ξ) [IsProbabilityMeasure P₀]
    (U : Ξ → {ν : Measure ℂ // IsLocallyFiniteMeasure ν}) (hU : Measurable U)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hpos : ∀ z, w z ≠ 0) (hfin : ∀ z, w z ≠ ∞)
    (ρ : ℕ → Measure ℂ) (hρ : ∀ n, ρ n ≪ volume)
    (shift : ℕ → ℂ × Ω → Ω) (hshift : ∀ n, Measurable (shift n))
    (R : ℕ → ℂ → Measure Ω)
    (hrooted : ∀ n, P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
      (weightedLocalization w n) (measurableSet_weightedLocalization hw n) w hw) ≪
        shiftedRootReferenceLaw (ρ n) P (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, P.map (fun ω => shift n (z, ω)) ≪ R n z)
    (hdom : ∀ n, ∀ᵐ z ∂ρ n, R n z ≪ S)
    (F : ℕ → ℂ → Ω → {ν : Measure ℂ // IsLocallyFiniteMeasure ν})
    (hF : ∀ n, ∀ᵐ z ∂ρ n, AEMeasurable (F n z) (R n z))
    (ε : ℝ) (hε : 0 < ε)
    (hUpos : ∀ᵐ ω ∂P₀, (U ω).val (ball 0 ε) ≠ 0 ∧ (U ω).val (ball 0 ε) ≠ ∞)
    (hFpos : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ ω ∂(R n z),
      (F n z ω).val (ball 0 ε) ≠ 0 ∧ (F n z ω).val (ball 0 ε) ≠ ∞)
    (hlaw : ∀ n, ∀ᵐ z ∂ρ n,
      (R n z).map (fun ω => localNormalizedMeasure ε (F n z ω)) ≪
        P₀.map (fun ω => localNormalizedMeasure ε (U ω)))
    (hcenter : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ ω ∂(R n z),
      (μ ω).map (fun v : ℂ => v - z) = (F n z ω).val)
    (hphase : ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P₀),
      ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
        ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
          AnnulusBallComparison (U p.2).val n 0 m}.ncard : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ (veryGoodComparableScaleCount (μ ω) β z N₀
        a b C₁m C₁p C₂m C₂p C₃ m N : ℝ) := by
  apply ae_ae_veryGoodComparableScaleFrequency_of_dominated_rooted_law P hμ hloc S hPdom
    hμS hlocS β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit w hw hpos hfin
    ρ shift hshift R hrooted hac hdom
  intro n
  exact ae_ae_veryGoodComparableScaleFrequency_of_local_recentered_law P₀ U hU
    (ρ n) (hρ n) (R n) (F n) (hF n) ε hε hUpos (hFpos n) (hlaw n)
    (fun _ ω => μ ω) (hcenter n) β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit hphase

#print axioms ae_ae_rooted_veryGoodComparableScaleFrequency_of_local_recentered_law

#print axioms ae_ae_veryGoodComparableScaleFrequency_of_local_recentered_law

end HarmonicBalls
