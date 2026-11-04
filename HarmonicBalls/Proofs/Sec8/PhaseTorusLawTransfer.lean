import HarmonicBalls.Proofs.Sec8.PhaseTorusFrequency
import HarmonicBalls.Proofs.Sec8.RootedVeryGoodTransfer

/-! # Transfer under absolute continuity of recentered measure laws

The independent phase and measure law can be compared directly with the law
of a recentered random measure; no pointwise coupling is required.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace HarmonicBalls

/-- The phase-shifted block-frequency event is measurable jointly in the
phase and a locally finite measure. -/
theorem measurableSet_phaseTorus_blockFrequency
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) :
    MeasurableSet {p : PhaseTorus × {ν : Measure ℂ // IsLocallyFiniteMeasure ν} |
      ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
        (({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          PhaseVeryGoodAnnulus p.2.val β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
          AnnulusBallComparison p.2.val n 0 m}.ncard : ℕ) : ℝ)} := by
  let L := {ν : Measure ℂ // IsLocallyFiniteMeasure ν}
  have hN (N : ℕ) : Measurable (fun p : PhaseTorus × L =>
      ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus p.2.val β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
        AnnulusBallComparison p.2.val n 0 m}.ncard)) := by
    let T : PhaseTorus × L → Set ℕ := fun p => {n | n ∈ Icc (N + 1) (2 * N) ∧
      PhaseVeryGoodAnnulus p.2.val β (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
      AnnulusBallComparison p.2.val n 0 m}
    have hT : Measurable T := by
      apply measurable_setOfPred.comp
      apply measurable_pi_iff.mpr
      intro n
      apply measurableSet_setOfPred.mp
      by_cases hn : n ∈ Icc (N + 1) (2 * N)
      · simp only [hn, true_and]
        exact (measurableSet_phaseVeryGoodAnnulus
          (measurable_subtype_coe.comp measurable_snd) (fun p => p.2.property)
          measurable_const (measurable_torusPhase.comp measurable_fst) β
          (dyadicScale n) (dyadicScale_pos n) N₀ a b C₁m C₁p C₂m C₂p C₃ hunit).inter
          (measurableSet_annulusBallComparison_joint (measurable_subtype_coe.comp measurable_snd)
            (fun p => p.2.property) measurable_const n m)
      · simp only [hn, false_and, ofPred_false, MeasurableSet.empty]
    exact measurable_ncard.comp hT
  have hle (N : ℕ) : MeasurableSet {p : PhaseTorus × L |
      (1 - ζ) * (N : ℝ) ≤ (({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus p.2.val β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
        AnnulusBallComparison p.2.val n 0 m}.ncard : ℕ) : ℝ)} :=
    measurableSet_le measurable_const (Measurable.of_discrete.comp (hN N))
  have heq : {p : PhaseTorus × L | ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      (({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus p.2.val β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
        AnnulusBallComparison p.2.val n 0 m}.ncard : ℕ) : ℝ)} =
      ⋃ K : ℕ, ⋂ N : ℕ, ⋂ (_ : K ≤ N), {p : PhaseTorus × L |
        (1 - ζ) * (N : ℝ) ≤ (({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          PhaseVeryGoodAnnulus p.2.val β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
          AnnulusBallComparison p.2.val n 0 m}.ncard : ℕ) : ℝ)} := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, eventually_atTop]
  rw [heq]
  exact MeasurableSet.iUnion fun K => MeasurableSet.iInter fun N =>
    MeasurableSet.iInter fun _ => hle N

/-- A Haar-phase frequency estimate passes to Lebesgue-dominated centres
when the law of each recentered measure is absolutely continuous with respect
to the reference measure law. -/
theorem ae_ae_veryGoodComparableScaleFrequency_of_recentered_law
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Ω → {ν : Measure ℂ // IsLocallyFiniteMeasure ν}) (hU : Measurable U)
    (ρ : Measure ℂ) (hρ : ρ ≪ volume) (S : ℂ → Measure Ξ)
    (F : ℂ → Ξ → {ν : Measure ℂ // IsLocallyFiniteMeasure ν})
    (hF : ∀ᵐ z ∂ρ, AEMeasurable (F z) (S z))
    (hdom : ∀ᵐ z ∂ρ, (S z).map (F z) ≪ P.map U)
    (M : ℂ → Ξ → Measure ℂ)
    (hcenter : ∀ᵐ z ∂ρ, ∀ᵐ ω ∂(S z),
      (M z ω).map (fun w : ℂ => w - z) = (F z ω).val)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    (hphase : ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
        (({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
          AnnulusBallComparison (U p.2).val n 0 m}.ncard : ℕ) : ℝ)) :
    ∀ᵐ z ∂ρ, ∀ᵐ ω ∂(S z), ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ (veryGoodComparableScaleCount (M z ω) β z N₀
        a b C₁m C₁p C₂m C₂p C₃ m N : ℝ) := by
  let L := {ν : Measure ℂ // IsLocallyFiniteMeasure ν}
  let Q : Measure PhaseTorus := (volume : Measure PhaseCircle).prod volume
  let A : PhaseTorus → L → Prop := fun t ν => ∀ᶠ N : ℕ in atTop,
    (1 - ζ) * (N : ℝ) ≤ (({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
      PhaseVeryGoodAnnulus ν.val β (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ (torusPhase t) ∧
      AnnulusBallComparison ν.val n 0 m}.ncard : ℕ) : ℝ)
  have hAm : MeasurableSet {p : PhaseTorus × L | A p.1 p.2} :=
    measurableSet_phaseTorus_blockFrequency β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit
  have hmap : Q.prod (P.map U) = (Q.prod P).map (Prod.map id U) := by
    simpa only [Measure.map_id] using Measure.map_prod_map Q P measurable_id hU
  have hlaw : ∀ᵐ p ∂(Q.prod (P.map U)), A p.1 p.2 := by
    rw [hmap, ae_map_iff (measurable_id.prodMap hU).aemeasurable hAm]
    exact hphase
  have htrans := ae_ae_negative_centerPhase_of_ae_prod_of_dominated (P.map U) ρ hρ
    (fun z => (S z).map (F z)) hdom (A := A) hlaw
  filter_upwards [htrans, hF, hcenter] with z hz hf hc
  have hz' : ∀ᵐ ω ∂(S z), A (phaseTorusOfComplex (-z)) (F z ω) :=
    ae_of_ae_map hf hz
  filter_upwards [hz', hc] with ω hω hcω
  filter_upwards [hω] with N hN
  rw [veryGoodComparableScaleCount_eq_centered_torus, hcω]
  exact hN

/-- A phase-frequency estimate transfers to random-measure-typical roots
under explicit rooted-law and recentered-measure-law comparisons. -/
theorem ae_ae_rooted_veryGoodComparableScaleFrequency_of_recentered_law
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
    (hlaw : ∀ n, ∀ᵐ z ∂ρ n, (R n z).map (F n z) ≪ P₀.map U)
    (hcenter : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ ω ∂(R n z),
      (μ ω).map (fun v : ℂ => v - z) = (F n z ω).val)
    (hphase : ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P₀),
      ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
        (({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
          AnnulusBallComparison (U p.2).val n 0 m}.ncard : ℕ) : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ (veryGoodComparableScaleCount (μ ω) β z N₀
        a b C₁m C₁p C₂m C₂p C₃ m N : ℝ) := by
  apply ae_ae_veryGoodComparableScaleFrequency_of_dominated_rooted_law P hμ hloc S hPdom
    hμS hlocS β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit w hw hpos hfin
    ρ shift hshift R hrooted hac hdom
  intro n
  exact ae_ae_veryGoodComparableScaleFrequency_of_recentered_law P₀ U hU
    (ρ n) (hρ n) (R n) (F n) (hF n) (hlaw n) (fun _ ω => μ ω) (hcenter n)
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit hphase

end HarmonicBalls
