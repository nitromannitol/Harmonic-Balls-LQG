import HarmonicBalls.Proofs.Sec8.JointPhaseFrequencyTransfer
import HarmonicBalls.Proofs.Sec8.InsertedPhaseFrequencyEvent

/-! # A shared local phase-frequency certificate

The imported frequency argument uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. The joint rooted comparison and
common approximations are explicit hypotheses.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A local certificate valid for every phase on one reference exceptional
set also represents the rooted frequency when the joint observation and
normalized-measure law is dominated by its reference counterpart. -/
theorem ae_phaseFrequency_certificate_iff_of_joint_normalizedRestriction_law
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
    (C : Set (PhaseTorus × E)) (hC : MeasurableSet C)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {η : Measure ℂ | IsGoodAnnulus η 1 0 a b})
    (hcert : ∀ᵐ ω ∂P, ∀ t : PhaseTorus,
      ((t, X ω) ∈ C ↔ ∀ᶠ N : ℕ in atTop,
        (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          PhaseVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ (torusPhase t) ∧
          AnnulusBallComparison (μ ω) n 0 m}.ncard : ℝ))) :
    ∀ᵐ ω ∂Q, ((phase (Y ω), Y ω) ∈ C ↔ ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (ν ω) β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phase (Y ω))) ∧
        AnnulusBallComparison (ν ω) n 0 m}.ncard : ℝ)) := by
  classical
  let L := {η : Measure ℂ // IsLocallyFiniteMeasure η}
  let loc' : Measure ℂ → Measure ℂ := fun η => if IsLocallyFiniteMeasure η then η else 0
  have hloc'm : Measurable loc' :=
    measurable_id.ite measurableSet_isLocallyFiniteMeasure_complex measurable_const
  have hloc'finite (η : Measure ℂ) : IsLocallyFiniteMeasure (loc' η) := by
    dsimp [loc']
    split_ifs <;> infer_instance
  let loc : Measure ℂ → L := fun η => ⟨loc' η, hloc'finite η⟩
  have hloc : Measurable loc := hloc'm.subtype_mk
  let A : Set (E × Measure ℂ) := {p | (phase p.1, p.1) ∈ C ↔
    ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (loc p.2).val β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phase p.1)) ∧
        AnnulusBallComparison (loc p.2).val n 0 m}.ncard : ℝ)}
  have hleft : MeasurableSet {p : E × Measure ℂ | (phase p.1, p.1) ∈ C} :=
    hC.preimage ((hphase.comp measurable_fst).prodMk measurable_fst)
  have hright : MeasurableSet {p : E × Measure ℂ |
      ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
        ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          PhaseVeryGoodAnnulus (loc p.2).val β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phase p.1)) ∧
          AnnulusBallComparison (loc p.2).val n 0 m}.ncard : ℝ)} := by
    have hm := measurableSet_phaseTorus_blockFrequency β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit
    have hf : Measurable (fun p : E × Measure ℂ => (phase p.1, loc p.2)) :=
      (hphase.comp measurable_fst).prodMk (hloc.comp measurable_snd)
    simpa only [Set.preimage_ofPred_eq] using hm.preimage hf
  have hA : MeasurableSet A := by
    convert (hleft.inter hright).union (hleft.compl.inter hright.compl) using 1
    ext p
    simp only [A, mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff]
    tauto
  have hnorm : Measurable (fun η : Measure ℂ => normalizedRestriction η (ball 0 ε)) :=
    measurable_normalizedRestriction_measure _ measurableSet_ball
  have hXP : Measurable (fun ω => (X ω, normalizedRestriction (μ ω) (ball 0 ε))) :=
    hX.prodMk (hnorm.comp hμ)
  have hYQ : Measurable (fun ω => (Y ω, normalizedRestriction (ν ω) (ball 0 ε))) :=
    hY.prodMk (hnorm.comp hν)
  have hP : ∀ᵐ ω ∂P, (X ω, normalizedRestriction (μ ω) (ball 0 ε)) ∈ A := by
    filter_upwards [hcert, hμpos] with ω hc hp
    have hf := phaseVeryGoodComparable_blockFrequency_iff_normalizedRestriction
      (μ ω) hε hp.1 hp.2 β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ (fun _ => torusPhase (phase (X ω)))
    have hc' := (hc (phase (X ω))).trans hf
    simpa [A, loc, loc', show IsLocallyFiniteMeasure
      (normalizedRestriction (μ ω) (ball 0 ε)) from inferInstance] using hc'
  have hQ := ae_of_ae_map hYQ.aemeasurable (hdom.ae_le ((ae_map_iff hXP.aemeasurable hA).2 hP))
  filter_upwards [hQ, hνpos] with ω hω hp
  have hf := phaseVeryGoodComparable_blockFrequency_iff_normalizedRestriction
    (ν ω) hε hp.1 hp.2 β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ (fun _ => torusPhase (phase (Y ω)))
  have hω' : (phase (Y ω), Y ω) ∈ C ↔ ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (normalizedRestriction (ν ω) (ball 0 ε)) β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phase (Y ω))) ∧
        AnnulusBallComparison (normalizedRestriction (ν ω) (ball 0 ε)) n 0 m}.ncard : ℝ) := by
    simpa [A, loc, loc', show IsLocallyFiniteMeasure
      (normalizedRestriction (ν ω) (ball 0 ε)) from inferInstance] using hω
  exact hω'.trans hf.symm

/-- Common observable approximations of normalized masses identify a
reference phase-frequency certificate under the second law, including when
the phase depends on the observation. -/
theorem ae_phaseFrequency_certificate_iff_of_common_mass_approximations
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
    (C : Set (PhaseTorus × E)) (hC : MeasurableSet C)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {η : Measure ℂ | IsGoodAnnulus η 1 0 a b})
    (hcert : ∀ᵐ ω ∂P, ∀ t : PhaseTorus,
      ((t, X ω) ∈ C ↔ ∀ᶠ N : ℕ in atTop,
        (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          PhaseVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ (torusPhase t) ∧
          AnnulusBallComparison (μ ω) n 0 m}.ncard : ℝ))) :
    ∀ᵐ ω ∂Q, ((phase (Y ω), Y ω) ∈ C ↔ ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (ν ω) β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phase (Y ω))) ∧
        AnnulusBallComparison (ν ω) n 0 m}.ncard : ℝ)) := by
  apply ae_phaseFrequency_certificate_iff_of_joint_normalizedRestriction_law
    P Q X Y hX hY μ ν hμ hν ε hε hμpos hνpos ?_ phase hphase C hC
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit hcert
  exact joint_normalizedRestriction_law_absolutelyContinuous_of_common_approximations
    P Q X Y hX hY hdom μ ν hμ hν (ball 0 ε) measurableSet_ball
    S hcount hgen hpi hsets huniv f hf hu hv

/-- A certificate depending only on part of an observation remains valid
when the observation also carries a root used to choose the phase. -/
theorem ae_projected_phaseFrequency_certificate_iff
    {E F Ω Ξ : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) (X : Ω → E) (Y : Ξ → E)
    (hX : Measurable X) (hY : Measurable Y)
    (μ : Ω → Measure ℂ) (ν : Ξ → Measure ℂ) (hμ : Measurable μ) (hν : Measurable ν)
    (ε : ℝ) (hε : 0 < ε)
    (hμpos : ∀ᵐ ω ∂P, μ ω (ball 0 ε) ≠ 0 ∧ μ ω (ball 0 ε) ≠ ∞)
    (hνpos : ∀ᵐ ω ∂Q, ν ω (ball 0 ε) ≠ 0 ∧ ν ω (ball 0 ε) ≠ ∞)
    (hdom : Q.map (fun ω => (Y ω, normalizedRestriction (ν ω) (ball 0 ε))) ≪
      P.map (fun ω => (X ω, normalizedRestriction (μ ω) (ball 0 ε))))
    (phase : E → PhaseTorus) (hphase : Measurable phase)
    (project : E → F) (hproject : Measurable project)
    (C : Set (PhaseTorus × F)) (hC : MeasurableSet C)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {η : Measure ℂ | IsGoodAnnulus η 1 0 a b})
    (hcert : ∀ᵐ ω ∂P, ∀ t : PhaseTorus,
      ((t, project (X ω)) ∈ C ↔ ∀ᶠ N : ℕ in atTop,
        (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          PhaseVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ (torusPhase t) ∧
          AnnulusBallComparison (μ ω) n 0 m}.ncard : ℝ))) :
    ∀ᵐ ω ∂Q, ((phase (Y ω), project (Y ω)) ∈ C ↔ ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (ν ω) β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phase (Y ω))) ∧
        AnnulusBallComparison (ν ω) n 0 m}.ncard : ℝ)) := by
  let C' : Set (PhaseTorus × E) := (Prod.map id project) ⁻¹' C
  have hC' : MeasurableSet C' := hC.preimage (measurable_id.prodMap hproject)
  exact ae_phaseFrequency_certificate_iff_of_joint_normalizedRestriction_law
    P Q X Y hX hY μ ν hμ hν ε hε hμpos hνpos hdom phase hphase C' hC'
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit hcert

/-- An origin-inserted GFF frequency certificate also represents frequency
of a second measure when its local observation, root, and normalized measure
have the displayed joint law domination. -/
theorem IsWholePlaneGFF.exists_inserted_phaseFrequency_common_certificate
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hh : IsWholePlaneGFF P hC hcirc)
    (hμfield : IsLQGMeasureOfField P γ α hcirc μ) (hμ : Measurable μ)
    (hpos : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r →
      μ ω (ball 0 r) ≠ 0 ∧ μ ω (ball 0 r) ≠ ∞)
    (ρ : Measure ℂ) [SFinite ρ] (Q : Measure Ξ)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (Y : Ξ → (Section6.LocalTest (ball 0 R) → ℝ) × ℂ) (hY : Measurable Y)
    (ν : Ξ → Measure ℂ) (hν : Measurable ν)
    (hνpos : ∀ᵐ ω ∂Q, ν ω (ball 0 ε) ≠ 0 ∧ ν ω (ball 0 ε) ≠ ∞)
    (hdom : Q.map (fun ω => (Y ω, normalizedRestriction (ν ω) (ball 0 ε))) ≪
      (ρ.prod P).map (fun p : ℂ × Ω =>
        ((fun φ : Section6.LocalTest (ball 0 R) => hC p.2 φ.1.1 +
          ∫ x, φ.1.1 x * (-α * Real.log ‖x‖), p.1),
          normalizedRestriction (μ p.2) (ball 0 ε))))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {η : Measure ℂ | IsGoodAnnulus η 1 0 a b}) :
    ∃ C : Set (PhaseTorus × (Section6.LocalTest (ball 0 R) → ℝ)),
      MeasurableSet C ∧
      (∀ᵐ ω ∂P, ∀ t : PhaseTorus,
        ((t, fun φ : Section6.LocalTest (ball 0 R) => hC ω φ.1.1 +
          ∫ x, φ.1.1 x * (-α * Real.log ‖x‖)) ∈ C ↔ ∀ᶠ N : ℕ in atTop,
          (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
            PhaseVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀
              a b C₁m C₁p C₂m C₂p C₃ (torusPhase t) ∧
            AnnulusBallComparison (μ ω) n 0 m}.ncard : ℝ))) ∧
      (∀ᵐ ω ∂Q, ((phaseTorusOfComplex (-(Y ω).2), (Y ω).1) ∈ C ↔
        ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
          ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
            PhaseVeryGoodAnnulus (ν ω) β (dyadicScale n) 0 N₀
              a b C₁m C₁p C₂m C₂p C₃
                (torusPhase (phaseTorusOfComplex (-(Y ω).2))) ∧
            AnnulusBallComparison (ν ω) n 0 m}.ncard : ℝ))) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let F := Section6.LocalTest (ball 0 R) → ℝ
  let X : ℂ × Ω → F × ℂ := fun p =>
    (fun φ => hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (-α * Real.log ‖x‖), p.1)
  have hX : Measurable X := by
    apply Measurable.prodMk ?_ measurable_fst
    apply measurable_pi_iff.mpr
    intro φ
    exact ((hh.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)).comp
      measurable_snd).add_const _
  have hμ' : Measurable (fun p : ℂ × Ω => μ p.2) := hμ.comp measurable_snd
  have hp : ∀ᵐ p ∂(ρ.prod P), μ p.2 (ball 0 ε) ≠ 0 ∧ μ p.2 (ball 0 ε) ≠ ∞ :=
    Measure.quasiMeasurePreserving_snd.ae (hpos.mono fun _ h => h ε hε)
  obtain ⟨C, hC', hcert⟩ := hh.exists_inserted_phaseFrequency_event hμfield hpos hR
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit
  have href : ∀ᵐ p ∂(ρ.prod P), ∀ t : PhaseTorus,
      ((t, (X p).1) ∈ C ↔ ∀ᶠ N : ℕ in atTop,
        (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          PhaseVeryGoodAnnulus (μ p.2) β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ (torusPhase t) ∧
          AnnulusBallComparison (μ p.2) n 0 m}.ncard : ℝ)) :=
    Measure.quasiMeasurePreserving_snd.ae hcert
  have hphase : Measurable (fun q : F × ℂ => phaseTorusOfComplex (-q.2)) :=
    measurable_phaseTorusOfComplex.comp measurable_snd.neg
  refine ⟨C, hC', hcert, ?_⟩
  exact ae_projected_phaseFrequency_certificate_iff (ρ.prod P) Q X Y hX hY
    (fun p => μ p.2) ν hμ' hν ε hε hp hνpos hdom
    (fun q => phaseTorusOfComplex (-q.2)) hphase Prod.fst measurable_fst C hC'
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit href

end HarmonicBalls
