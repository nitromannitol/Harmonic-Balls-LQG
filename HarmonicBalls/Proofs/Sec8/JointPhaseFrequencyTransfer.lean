import HarmonicBalls.Proofs.Sec8.JointNormalizedMassLaw
import HarmonicBalls.Proofs.Sec8.PhaseLocalLawTransfer
import HarmonicBalls.Proofs.Sec5.MeasureLawRegularity

/-! # Phase frequency from joint local laws

The phase-frequency development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. -/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A phase-frequency estimate transfers through the joint law of an
observation and its normalized local measure. The phase may depend on that
observation. -/
theorem ae_phaseFrequency_of_joint_normalizedRestriction_law
    {E Ω Ξ : Type*} [MeasurableSpace E] [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) (X : Ω → E) (Y : Ξ → E)
    (hX : Measurable X) (hY : Measurable Y)
    (μ : Ω → Measure ℂ) (ν : Ξ → Measure ℂ) (hμ : Measurable μ) (hν : Measurable ν)
    (ε : ℝ) (hε : 0 < ε)
    (hμpos : ∀ᵐ ω ∂P, μ ω (ball 0 ε) ≠ 0 ∧ μ ω (ball 0 ε) ≠ ∞)
    (hνpos : ∀ᵐ ω ∂Q, ν ω (ball 0 ε) ≠ 0 ∧ ν ω (ball 0 ε) ≠ ∞)
    (hdom : Q.map (fun ω => (Y ω, normalizedRestriction (ν ω) (ball 0 ε))) ≪
      P.map (fun ω => (X ω, normalizedRestriction (μ ω) (ball 0 ε))))
    (phase : E → PhaseTorus) (hphase : Measurable phase)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {η : Measure ℂ | IsGoodAnnulus η 1 0 a b})
    (hfreq : ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phase (X ω))) ∧
        AnnulusBallComparison (μ ω) n 0 m}.ncard : ℝ)) :
    ∀ᵐ ω ∂Q, ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (ν ω) β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phase (Y ω))) ∧
        AnnulusBallComparison (ν ω) n 0 m}.ncard : ℝ) := by
  classical
  let L := {η : Measure ℂ // IsLocallyFiniteMeasure η}
  let loc' : Measure ℂ → Measure ℂ := fun η => if IsLocallyFiniteMeasure η then η else 0
  have hloc'm : Measurable loc' :=
    measurable_id.ite measurableSet_isLocallyFiniteMeasure_complex measurable_const
  have hloc'finite (η : Measure ℂ) : IsLocallyFiniteMeasure (loc' η) := by
    dsimp [loc']
    split_ifs with h
    · exact h
    · infer_instance
  let loc : Measure ℂ → L := fun η => ⟨loc' η, hloc'finite η⟩
  have hloc : Measurable loc := hloc'm.subtype_mk
  let T : Set (E × Measure ℂ) := {p | ∀ᶠ N : ℕ in atTop,
    (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
      PhaseVeryGoodAnnulus (loc p.2).val β (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phase p.1)) ∧
      AnnulusBallComparison (loc p.2).val n 0 m}.ncard : ℝ)}
  have hT : MeasurableSet T := by
    have hm := measurableSet_phaseTorus_blockFrequency β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit
    have hf : Measurable (fun p : E × Measure ℂ => (phase p.1, loc p.2)) :=
      (hphase.comp measurable_fst).prodMk (hloc.comp measurable_snd)
    simpa only [T, Set.preimage_ofPred_eq] using hm.preimage hf
  have hnorm : Measurable (fun η : Measure ℂ => normalizedRestriction η (ball 0 ε)) :=
    measurable_normalizedRestriction_measure _ measurableSet_ball
  have hXP : Measurable (fun ω => (X ω, normalizedRestriction (μ ω) (ball 0 ε))) :=
    hX.prodMk (hnorm.comp hμ)
  have hYQ : Measurable (fun ω => (Y ω, normalizedRestriction (ν ω) (ball 0 ε))) :=
    hY.prodMk (hnorm.comp hν)
  have hP : ∀ᵐ ω ∂P, (X ω, normalizedRestriction (μ ω) (ball 0 ε)) ∈ T := by
    filter_upwards [hfreq, hμpos] with ω hf hp
    have h := (phaseVeryGoodComparable_blockFrequency_iff_normalizedRestriction
      (μ ω) hε hp.1 hp.2 β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ
      (fun _ => torusPhase (phase (X ω)))).1 hf
    simpa [T, loc, loc', show IsLocallyFiniteMeasure
      (normalizedRestriction (μ ω) (ball 0 ε)) from inferInstance] using h
  have hQ := ae_of_ae_map hYQ.aemeasurable (hdom.ae_le ((ae_map_iff hXP.aemeasurable hT).2 hP))
  filter_upwards [hQ, hνpos] with ω hω hp
  apply (phaseVeryGoodComparable_blockFrequency_iff_normalizedRestriction
    (ν ω) hε hp.1 hp.2 β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ
    (fun _ => torusPhase (phase (Y ω)))).2
  simpa [T, loc, loc', show IsLocallyFiniteMeasure
    (normalizedRestriction (ν ω) (ball 0 ε)) from inferInstance] using hω

/-- Common observed mass approximations transfer a phase-frequency estimate
while retaining dependence between the phase and the measure. -/
theorem ae_phaseFrequency_of_common_mass_approximations
    {E Ω Ξ : Type*} [MeasurableSpace E] [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) (X : Ω → E) (Y : Ξ → E)
    (hX : Measurable X) (hY : Measurable Y)
    (μ : Ω → Measure ℂ) (ν : Ξ → Measure ℂ) (hμ : Measurable μ) (hν : Measurable ν)
    (ε : ℝ) (hε : 0 < ε)
    (hμpos : ∀ᵐ ω ∂P, μ ω (ball 0 ε) ≠ 0 ∧ μ ω (ball 0 ε) ≠ ∞)
    (hνpos : ∀ᵐ ω ∂Q, ν ω (ball 0 ε) ≠ 0 ∧ ν ω (ball 0 ε) ≠ ∞)
    (hdom : Q.map Y ≪ P.map X)
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ A ∈ S, MeasurableSet A) (huniv : univ ∈ S)
    (f : S → ℕ → E → ℝ) (hf : ∀ A n, Measurable (f A n))
    (hu : ∀ A, TendstoInMeasure P (fun n ω => f A n (X ω)) atTop
      (fun ω => (normalizedRestriction (μ ω) (ball 0 ε) A.val).toReal))
    (hv : ∀ A, TendstoInMeasure Q (fun n ω => f A n (Y ω)) atTop
      (fun ω => (normalizedRestriction (ν ω) (ball 0 ε) A.val).toReal))
    (phase : E → PhaseTorus) (hphase : Measurable phase)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {η : Measure ℂ | IsGoodAnnulus η 1 0 a b})
    (hfreq : ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phase (X ω))) ∧
        AnnulusBallComparison (μ ω) n 0 m}.ncard : ℝ)) :
    ∀ᵐ ω ∂Q, ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (ν ω) β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phase (Y ω))) ∧
        AnnulusBallComparison (ν ω) n 0 m}.ncard : ℝ) := by
  apply ae_phaseFrequency_of_joint_normalizedRestriction_law
    P Q X Y hX hY μ ν hμ hν ε hε hμpos hνpos ?_ phase hphase
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit hfreq
  exact joint_normalizedRestriction_law_absolutelyContinuous_of_common_approximations
    P Q X Y hX hY hdom μ ν hμ hν (ball 0 ε) measurableSet_ball
    S hcount hgen hpi hsets huniv f hf hu hv

end HarmonicBalls
