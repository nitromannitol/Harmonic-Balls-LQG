import HarmonicBalls.Proofs.Sec8.ObservedLocalRootTransfer
import HarmonicBalls.Proofs.Sec5.MeasureLawRegularity
import HarmonicBalls.Proofs.Sec8.AEPiSystemRatioRepresentatives

/-! # Frequency events observed through local measure versions

The phase-frequency argument uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. A local measure version is an
explicit hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

/-- A local measure version measurable through an observation determines a
measurable frequency event on the observation space. The measure-valued
version need not itself factor as a measurable map on that space. -/
theorem exists_observed_frequency_event_of_local_version
    {A F : Type*} [MeasurableSpace A] [MeasurableSpace F]
    (P : Measure A) (obs : A → F × ℂ) (μ : A → Measure ℂ)
    (ε : ℝ) (hε : 0 < ε) (ν : A → Measure ℂ)
    (hν : @Measurable A (Measure ℂ) (MeasurableSpace.comap obs inferInstance) _ ν)
    (hνeq : ∀ᵐ x ∂P, ν x = normalizedRestriction
      ((μ x).map (fun v : ℂ => v - (obs x).2)) (ball 0 ε))
    (hmass : ∀ᵐ x ∂P,
      ((μ x).map (fun v : ℂ => v - (obs x).2)) (ball 0 ε) ≠ 0 ∧
      ((μ x).map (fun v : ℂ => v - (obs x).2)) (ball 0 ε) ≠ ∞)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {η : Measure ℂ | IsGoodAnnulus η 1 0 a b}) :
    ∃ E : Set (F × ℂ), MeasurableSet E ∧
      ∀ᵐ x ∂P, (obs x ∈ E ↔ ∀ᶠ N : ℕ in atTop,
        (1 - ζ) * (N : ℝ) ≤ (veryGoodComparableScaleCount (μ x) β (obs x).2 N₀
          a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)) := by
  classical
  let M : MeasurableSpace A := MeasurableSpace.comap obs inferInstance
  let ν' : A → Measure ℂ := fun x => if IsLocallyFiniteMeasure (ν x) then ν x else 0
  have hν'm : @Measurable A (Measure ℂ) M _ ν' := by
    let : MeasurableSpace A := M
    exact hν.ite (measurableSet_isLocallyFiniteMeasure_complex.preimage hν) measurable_const
  have hν'loc (x : A) : IsLocallyFiniteMeasure (ν' x) := by
    dsimp [ν']
    split_ifs with h
    · exact h
    · infer_instance
  let V : A → {η : Measure ℂ // IsLocallyFiniteMeasure η} := fun x => ⟨ν' x, hν'loc x⟩
  have hVm : @Measurable A _ M _ V := hν'm.subtype_mk
  let T : Set A := {x | ∀ᶠ N : ℕ in atTop,
    (1 - ζ) * (N : ℝ) ≤ ({k : ℕ | k ∈ Icc (N + 1) (2 * N) ∧
      PhaseVeryGoodAnnulus (V x).val β (dyadicScale k) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phaseTorusOfComplex (-(obs x).2))) ∧
      AnnulusBallComparison (V x).val k 0 m}.ncard : ℝ)}
  have hTm : MeasurableSet[M] T := by
    let : MeasurableSpace A := M
    have hobs : Measurable obs := comap_measurable obs
    have hf : Measurable (fun x : A => (phaseTorusOfComplex (-(obs x).2), V x)) :=
      (measurable_phaseTorusOfComplex.comp (measurable_snd.comp hobs).neg).prodMk hVm
    have hp := (measurableSet_phaseTorus_blockFrequency β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit).preimage hf
    simpa only [Set.preimage_ofPred_eq, T] using hp
  obtain ⟨E, hEm, hE⟩ := MeasurableSpace.measurableSet_comap.mp hTm
  refine ⟨E, hEm, ?_⟩
  filter_upwards [hνeq, hmass] with x he hm
  have hloc : IsLocallyFiniteMeasure (ν x) := by rw [he]; infer_instance
  have hV : (V x).val = normalizedRestriction
      ((μ x).map (fun v : ℂ => v - (obs x).2)) (ball 0 ε) := by
    simpa [V, ν', hloc] using he
  have hfreq := phaseVeryGoodComparable_blockFrequency_iff_normalizedRestriction
    ((μ x).map (fun v : ℂ => v - (obs x).2)) hε hm.1 hm.2
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ
    (fun _ => torusPhase (phaseTorusOfComplex (-(obs x).2)))
  have hmem : obs x ∈ E ↔ x ∈ T := Set.ext_iff.mp hE x
  rw [hmem]
  change (∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
    ({k : ℕ | k ∈ Icc (N + 1) (2 * N) ∧
      PhaseVeryGoodAnnulus (V x).val β (dyadicScale k) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phaseTorusOfComplex (-(obs x).2))) ∧
      AnnulusBallComparison (V x).val k 0 m}.ncard : ℝ)) ↔ _
  rw [hV]
  simpa only [veryGoodComparableScaleCount_eq_centered_torus] using hfreq.symm

/-- Countable local mass-ratio versions suffice to realize the frequency
event on the observation space under a probability law. -/
theorem exists_observed_frequency_event_of_countable_ratios
    {A F : Type*} [MeasurableSpace A] [MeasurableSpace F]
    (P : Measure A) [IsProbabilityMeasure P] (obs : A → F × ℂ) (hobs : Measurable obs)
    (μ : A → Measure ℂ) (ε : ℝ) (hε : 0 < ε)
    (hμ : AEMeasurable μ P) (hloc : ∀ᵐ x ∂P, IsLocallyFiniteMeasure (μ x))
    (hmass : ∀ᵐ x ∂P,
      ((μ x).map (fun v : ℂ => v - (obs x).2)) (ball 0 ε) ≠ 0 ∧
      ((μ x).map (fun v : ℂ => v - (obs x).2)) (ball 0 ε) ≠ ∞)
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ V ∈ S, MeasurableSet V)
    (hversion : ∀ V ∈ S, ∃ Y : A → ℝ≥0∞,
      @Measurable A ℝ≥0∞ (MeasurableSpace.comap obs inferInstance) _ Y ∧
      (fun x => ((μ x).map (fun v : ℂ => v - (obs x).2)) (V ∩ ball 0 ε) /
        ((μ x).map (fun v : ℂ => v - (obs x).2)) (ball 0 ε)) =ᵐ[P] Y)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {η : Measure ℂ | IsGoodAnnulus η 1 0 a b}) :
    ∃ E : Set (F × ℂ), MeasurableSet E ∧
      ∀ᵐ x ∂P, (obs x ∈ E ↔ ∀ᶠ N : ℕ in atTop,
        (1 - ζ) * (N : ℝ) ≤ (veryGoodComparableScaleCount (μ x) β (obs x).2 N₀
          a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)) := by
  have hcenter : AEMeasurable (fun x => (μ x).map (fun v : ℂ => v - (obs x).2)) P := by
    obtain ⟨μ', hμm, hμloc, hμeq⟩ := Section6.exists_measurable_locallyFinite_rep hμ hloc
    have hf : Measurable (fun q : A × ℂ => q.2 - (obs q.1).2) :=
      measurable_snd.sub (measurable_snd.comp (hobs.comp measurable_fst))
    have hm := Section6.measurable_map_of_locallyFinite hμm hμloc hf
    apply hm.aemeasurable.congr
    filter_upwards [hμeq] with x hx
    exact congrArg (fun η : Measure ℂ => η.map (fun v : ℂ => v - (obs x).2)) hx.symm
  obtain ⟨ν, hν, hνeq⟩ := exists_normalizedRestriction_version_of_ae_piSystem_ratios
    P (MeasurableSpace.comap obs inferInstance) hobs.comap_le
    (fun x => (μ x).map (fun v : ℂ => v - (obs x).2)) hcenter
    (ball 0 ε) measurableSet_ball hmass S hcount hgen hpi hsets hversion
  exact exists_observed_frequency_event_of_local_version P obs μ ε hε ν hν hνeq hmass
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit

#print axioms exists_observed_frequency_event_of_countable_ratios
#print axioms exists_observed_frequency_event_of_local_version

end HarmonicBalls
