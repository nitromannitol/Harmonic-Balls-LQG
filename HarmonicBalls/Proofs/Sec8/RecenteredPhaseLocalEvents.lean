import HarmonicBalls.Proofs.Sec8.EventualBufferedLocalEvents
import HarmonicBalls.Proofs.Sec8.PhaseTorusLebesgue

/-! # Phase-dependent local events at sampled roots

A Haar-almost-every phase and origin-inserted field event transfers to the
canonical recentered observation with the phase determined by the sampled
root. The imported Section 8 development uses Leonardo Bonanno's
whole-plane GFF and ergodic-theorem formalizations.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

/-- A Haar/field almost-sure event also holds after adjoining a root whose
law is dominated by planar area and taking its negative torus phase. -/
theorem ae_shiftedRootReferenceLaw_of_phase_field_event
    {Ω F : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    (ρ : Measure ℂ) (hρ : ρ ≪ volume) (P : Measure Ω) [SFinite P]
    (X : Ω → F) (hX : Measurable X) (E : Set (PhaseTorus × F))
    (hE : MeasurableSet E)
    (hphase : ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      (p.1, X p.2) ∈ E) :
    ∀ᵐ q ∂shiftedRootReferenceLaw ρ P (fun p => X p.2),
      (phaseTorusOfComplex (-q.2), q.1) ∈ E := by
  have hp : Measurable (fun z : ℂ => phaseTorusOfComplex (-z)) :=
    measurable_phaseTorusOfComplex.comp (by fun_prop)
  have hmap : Measurable (fun p : ℂ × Ω => (X p.2, p.1)) :=
    (hX.comp measurable_snd).prodMk measurable_fst
  have hevent : MeasurableSet {q : F × ℂ | (phaseTorusOfComplex (-q.2), q.1) ∈ E} :=
    hE.preimage ((hp.comp measurable_snd).prodMk measurable_fst)
  apply (ae_map_iff hmap.aemeasurable hevent).2
  apply (Measure.ae_prod_iff_ae_ae (hmap hevent)).2
  exact ae_ae_negative_centerPhase_of_ae_prod P ρ hρ
    (A := fun t ω => (t, X ω) ∈ E) hphase

/-- A buffered rooted comparison transfers measurable phase-dependent local
field events to almost every sampled root. -/
theorem IsWholePlaneGFF.ae_ae_localized_recentered_phase_event
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (μ : Ω → Measure ℂ)
    (hμ : AEMeasurable μ P) (A B : Set ℂ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hfin : ∀ᵐ ω ∂P, μ ω A ≠ ∞)
    (ρ : Measure ℂ) [SFinite ρ] (hρ : ρ ≪ volume) (γ : ℝ)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hside : ∀ᵐ z ∂(ρ.restrict B), ‖z‖ + R ≤ 1 ∨ 1 + R ≤ ‖z‖)
    (hrooted : (P.bind fun ω => ((μ ω).restrict A).map
      (fun z => (Section6.pairingProc hC ω, z))) ≪
      shiftedRootReferenceLaw ρ P (fun p => fun φ : LQGMetric.TestC0 =>
        hC p.2 φ.1 + ∫ x, φ.1 x *
          (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1))))
    (E : Set (PhaseTorus × (Section6.LocalTest (ball 0 r) → ℝ)))
    (hE : MeasurableSet E)
    (hphase : ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      (p.1, fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) ∈ E) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ A → z ∈ B →
      (phaseTorusOfComplex (-z), recenteredDistributionObservation (ball 0 r)
        (Section6.pairingProc hC ω, z)) ∈ E := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let X : Ω → Section6.LocalTest (ball 0 r) → ℝ := fun ω φ =>
    hC ω φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro φ
    exact (hh.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)).add_const _
  let E' : Set ((Section6.LocalTest (ball 0 r) → ℝ) × ℂ) :=
    {q | (phaseTorusOfComplex (-q.2), q.1) ∈ E}
  have hE' : MeasurableSet E' := by
    exact hE.preimage (((measurable_phaseTorusOfComplex.comp (by fun_prop)).comp
      measurable_snd).prodMk measurable_fst)
  have href : ∀ᵐ q ∂(shiftedRootReferenceLaw (ρ.restrict B) P (fun p => X p.2)), q ∈ E' :=
    ae_shiftedRootReferenceLaw_of_phase_field_event (ρ.restrict B)
      ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hρ) P X hX E hE hphase
  exact hh.ae_ae_localized_recentered_observation μ hμ A B hA hB hfin ρ γ
    hr hrR hside hrooted E' hE' href

/-- Countably many Haar/field almost-sure local events hold at all sufficiently
small buffered scales at almost every sampled root. -/
theorem IsWholePlaneGFF.ae_ae_eventually_recentered_phase_events
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (μ : Ω → Measure ℂ)
    (hμ : AEMeasurable μ P) (A : Set ℂ) (hA : MeasurableSet A)
    (hfin : ∀ᵐ ω ∂P, μ ω A ≠ ∞) (ρ : Measure ℂ) [SFinite ρ]
    (hρ : ρ ≪ volume) (γ : ℝ)
    (hrooted : (P.bind fun ω => ((μ ω).restrict A).map
      (fun z => (Section6.pairingProc hC ω, z))) ≪
      shiftedRootReferenceLaw ρ P (fun p => fun φ : LQGMetric.TestC0 =>
        hC p.2 φ.1 + ∫ x, φ.1 x *
          (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1))))
    (E : ∀ n : ℕ, Set (PhaseTorus ×
      (Section6.LocalTest (ball 0 (1 / (2 * ((n : ℝ) + 1)))) → ℝ)))
    (hE : ∀ n, MeasurableSet (E n))
    (hphase : ∀ n, ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      (p.1, fun φ : Section6.LocalTest (ball 0 (1 / (2 * ((n : ℝ) + 1)))) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) ∈ E n) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ A → ∀ᶠ n in atTop,
      z ∈ bufferedRoots n ∧
      (phaseTorusOfComplex (-z),
        recenteredDistributionObservation (ball 0 (1 / (2 * ((n : ℝ) + 1))))
          (Section6.pairingProc hC ω, z)) ∈ E n := by
  have hevents : ∀ n, ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ A → z ∈ bufferedRoots n →
      (phaseTorusOfComplex (-z),
        recenteredDistributionObservation (ball 0 (1 / (2 * ((n : ℝ) + 1))))
          (Section6.pairingProc hC ω, z)) ∈ E n := by
    intro n
    have hr : 0 < 1 / (2 * ((n : ℝ) + 1)) := by positivity
    have hrR : 1 / (2 * ((n : ℝ) + 1)) < 1 / ((n : ℝ) + 1) := by
      have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [one_div_lt_one_div (by positivity) hp]
      nlinarith
    exact hh.ae_ae_localized_recentered_phase_event μ hμ A (bufferedRoots n) hA
      (measurableSet_bufferedRoots n) hfin ρ hρ γ hr hrR (ae_bufferedRoots_side ρ n)
      hrooted (E n) (hE n) (hphase n)
  have hall : ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ n, z ∈ A → z ∈ bufferedRoots n →
      (phaseTorusOfComplex (-z),
        recenteredDistributionObservation (ball 0 (1 / (2 * ((n : ℝ) + 1))))
          (Section6.pairingProc hC ω, z)) ∈ E n := by
    filter_upwards [ae_all_iff.mpr hevents] with ω hω
    exact ae_all_iff.mpr hω
  filter_upwards [hall, hh.ae_ae_buffered_root_cover μ hμ A hA hfin ρ hρ γ hrooted]
    with ω he hc
  filter_upwards [he, hc] with z hz hcov hzA
  have hsome : ∃ n, z ∈ bufferedRoots n := by
    rcases hcov hzA with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact ⟨n, Or.inl hn⟩
    · exact ⟨n, Or.inr hn⟩
  obtain ⟨N, hN⟩ := hsome
  filter_upwards [eventually_ge_atTop N] with n hn
  have hzn := bufferedRoots_mono hn hN
  exact ⟨hzn, hz n hzA hzn⟩

#print axioms IsWholePlaneGFF.ae_ae_eventually_recentered_phase_events
#print axioms ae_shiftedRootReferenceLaw_of_phase_field_event
#print axioms IsWholePlaneGFF.ae_ae_localized_recentered_phase_event

end HarmonicBalls
