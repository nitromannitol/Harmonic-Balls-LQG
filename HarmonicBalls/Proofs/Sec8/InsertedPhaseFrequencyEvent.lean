import HarmonicBalls.Proofs.Sec8.LocalCircleDecoder
import HarmonicBalls.Proofs.Sec8.RecenteredPhaseLocalEvents
import HarmonicBalls.Proofs.Sec8.BufferedNormalizedRestriction
import HarmonicBalls.Proofs.Sec8.PhaseLocalLawTransfer
import HarmonicBalls.Proofs.Sec5.MeasureLawRegularity

/-! # A local phase-frequency event for the origin insertion

The imported frequency argument uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. -/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A normalized local measure version determines a measurable phase-frequency
 event in the local field, simultaneously for every phase outside one field
 exceptional set. -/
theorem IsWholePlaneGFF.exists_inserted_phaseFrequency_event
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hh : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hpos : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r →
      μ ω (ball 0 r) ≠ 0 ∧ μ ω (ball 0 r) ≠ ∞)
    {R : ℝ} (hR : 0 < R)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {η : Measure ℂ | IsGoodAnnulus η 1 0 a b}) :
    ∃ E : Set (PhaseTorus × (Section6.LocalTest (ball 0 R) → ℝ)),
      MeasurableSet E ∧ ∀ᵐ ω ∂P, ∀ t : PhaseTorus,
        ((t, fun φ : Section6.LocalTest (ball 0 R) =>
          hC ω φ.1.1 + ∫ x, φ.1.1 x * (-α * Real.log ‖x‖)) ∈ E ↔
        ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
          ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
            PhaseVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀
              a b C₁m C₁p C₂m C₂p C₃ (torusPhase t) ∧
            AnnulusBallComparison (μ ω) n 0 m}.ncard : ℝ)) := by
  classical
  obtain ⟨r, hr, ν, hν, hνeq⟩ := hh.exists_buffered_normalizedRestriction hμ hpos R hR
  let X := Section6.localPairingProc (ball 0 R) hC
  let M : MeasurableSpace Ω := MeasurableSpace.comap X inferInstance
  have hνM : @Measurable Ω (Measure ℂ) M _ ν := by
    rw [Section6.fieldSigmaAlgebraModConst_eq, Section6.fieldSigmaAlgebraModConst_eq_comap] at hν
    exact hν
  let ν' : Ω → Measure ℂ := fun ω => if IsLocallyFiniteMeasure (ν ω) then ν ω else 0
  have hν'm : @Measurable Ω (Measure ℂ) M _ ν' := by
    let : MeasurableSpace Ω := M
    exact hνM.ite (measurableSet_isLocallyFiniteMeasure_complex.preimage hνM) measurable_const
  have hν'loc (ω : Ω) : IsLocallyFiniteMeasure (ν' ω) := by
    dsimp [ν']
    split_ifs <;> infer_instance
  let V : Ω → {η : Measure ℂ // IsLocallyFiniteMeasure η} := fun ω => ⟨ν' ω, hν'loc ω⟩
  have hVm : @Measurable Ω _ M _ V := hν'm.subtype_mk
  let T : Set (PhaseTorus × Ω) := {p | ∀ᶠ N : ℕ in atTop,
    (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
      PhaseVeryGoodAnnulus (V p.2).val β (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
      AnnulusBallComparison (V p.2).val n 0 m}.ncard : ℝ)}
  have hTm : MeasurableSet[((inferInstance : MeasurableSpace PhaseTorus).prod M)] T := by
    let : MeasurableSpace Ω := M
    have hf : Measurable (fun p : PhaseTorus × Ω => (p.1, V p.2)) :=
      measurable_fst.prodMk (hVm.comp measurable_snd)
    simpa only [T, Set.preimage_ofPred_eq] using
      (measurableSet_phaseTorus_blockFrequency β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit).preimage hf
  have hTm' : MeasurableSet[MeasurableSpace.comap (Prod.map id X) inferInstance] T := by
    have heq : (inferInstance : MeasurableSpace PhaseTorus).prod M =
        MeasurableSpace.comap (Prod.map id X) inferInstance := by
      change (inferInstance : MeasurableSpace PhaseTorus).prod
        (MeasurableSpace.comap X inferInstance) =
        ((inferInstance : MeasurableSpace PhaseTorus).prod
          (inferInstance : MeasurableSpace (Section6.LocalTest (ball 0 R) → ℝ))).comap
            (Prod.map id X)
      rw [MeasurableSpace.comap_prodMap, MeasurableSpace.comap_id]
    exact heq ▸ hTm
  obtain ⟨E₀, hE₀, hE₀eq⟩ := MeasurableSpace.measurableSet_comap.mp hTm'
  let undo : (Section6.LocalTest (ball 0 R) → ℝ) → (Section6.LocalTest (ball 0 R) → ℝ) :=
    fun f φ => f φ - ∫ x, φ.1.1 x * (-α * Real.log ‖x‖)
  have hundo : Measurable undo := by
    apply measurable_pi_iff.mpr
    intro φ
    exact (measurable_pi_apply φ).sub_const _
  let E := (Prod.map id undo) ⁻¹' E₀
  refine ⟨E, hE₀.preimage (measurable_id.prodMap hundo), ?_⟩
  filter_upwards [hνeq, hpos] with ω he hp t
  have hloc : IsLocallyFiniteMeasure (ν ω) := by rw [he]; infer_instance
  have hV : (V ω).val = normalizedRestriction (μ ω) (ball 0 r) := by
    simpa [V, ν', hloc] using he
  have hmem : (t, X ω) ∈ E₀ ↔ (t, ω) ∈ T := Set.ext_iff.mp hE₀eq (t, ω)
  have hf := phaseVeryGoodComparable_blockFrequency_iff_normalizedRestriction
    (μ ω) hr.1 (hp r hr.1).1 (hp r hr.1).2 β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ
    (fun _ => torusPhase t)
  have hu : undo (fun φ => hC ω φ.1.1 + ∫ x, φ.1.1 x * (-α * Real.log ‖x‖)) = X ω := by
    funext φ
    simp [undo, X, Section6.localPairingProc]
  change (t, undo _) ∈ E₀ ↔ _
  rw [hu, hmem]
  change (∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
    ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
      PhaseVeryGoodAnnulus (V ω).val β (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ (torusPhase t) ∧
      AnnulusBallComparison (V ω).val n 0 m}.ncard : ℝ)) ↔ _
  rw [hV]
  exact hf.symm

/-- A reference phase-frequency estimate gives a measurable local certificate
and transfers that certificate to sampled roots under the displayed rooted
law comparison. The identification of the certificate with the original
measure at a random root is a separate requirement. -/
theorem IsWholePlaneGFF.exists_rooted_inserted_phaseFrequency_certificate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ₀ μ : Ω → Measure ℂ} (hh : IsWholePlaneGFF P hC hcirc)
    (hμ₀ : IsLQGMeasureOfField P γ γ hcirc μ₀)
    (hpos : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r →
      μ₀ ω (ball 0 r) ≠ 0 ∧ μ₀ ω (ball 0 r) ≠ ∞)
    (hμ : AEMeasurable μ P) (A B : Set ℂ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hfin : ∀ᵐ ω ∂P, μ ω A ≠ ∞)
    (ρ : Measure ℂ) [SFinite ρ] (hρ : ρ ≪ volume)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hside : ∀ᵐ z ∂(ρ.restrict B), ‖z‖ + R ≤ 1 ∨ 1 + R ≤ ‖z‖)
    (hrooted : (P.bind fun ω => ((μ ω).restrict A).map
      (fun z => (Section6.pairingProc hC ω, z))) ≪
      shiftedRootReferenceLaw ρ P (fun p => fun φ : LQGMetric.TestC0 =>
        hC p.2 φ.1 + ∫ x, φ.1 x *
          (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1))))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {η : Measure ℂ | IsGoodAnnulus η 1 0 a b})
    (hfreq : ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
        ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          PhaseVeryGoodAnnulus (μ₀ p.2) β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
          AnnulusBallComparison (μ₀ p.2) n 0 m}.ncard : ℝ)) :
    ∃ E : Set (PhaseTorus × (Section6.LocalTest (ball 0 r) → ℝ)),
      MeasurableSet E ∧
      (∀ᵐ ω ∂P, ∀ t : PhaseTorus,
        ((t, fun φ : Section6.LocalTest (ball 0 r) =>
          hC ω φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) ∈ E ↔
        ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
          ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
            PhaseVeryGoodAnnulus (μ₀ ω) β (dyadicScale n) 0 N₀
              a b C₁m C₁p C₂m C₂p C₃ (torusPhase t) ∧
            AnnulusBallComparison (μ₀ ω) n 0 m}.ncard : ℝ))) ∧
      (∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ A → z ∈ B →
        (phaseTorusOfComplex (-z), recenteredDistributionObservation (ball 0 r)
          (Section6.pairingProc hC ω, z)) ∈ E) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨E, hE, heq⟩ := hh.exists_inserted_phaseFrequency_event hμ₀ hpos hr
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit
  have hphase : ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      (p.1, fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) ∈ E := by
    filter_upwards [hfreq, Measure.quasiMeasurePreserving_snd.ae heq] with p hp he
    exact (he p.1).2 hp
  exact ⟨E, hE, heq, hh.ae_ae_localized_recentered_phase_event μ hμ A B hA hB
    hfin ρ hρ γ hr hrR hside hrooted E hE hphase⟩

#print axioms IsWholePlaneGFF.exists_rooted_inserted_phaseFrequency_certificate
#print axioms IsWholePlaneGFF.exists_inserted_phaseFrequency_event

end HarmonicBalls
