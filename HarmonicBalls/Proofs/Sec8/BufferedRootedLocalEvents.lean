import HarmonicBalls.Proofs.Sec8.RootedReferenceNullSets

/-! # Local events at buffered sampled roots

An origin-inserted field estimate passes to the recentered observation at
sampled roots, using one global rooted-law comparison and the countable
interior and exterior buffer cover. The imported Section 6 development uses
Leonardo Bonanno's whole-plane GFF formalization.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

/-- An almost-sure field event persists after adjoining any independent root. -/
theorem ae_shiftedRootReferenceLaw_of_field_event
    {Z Ω F : Type*} [MeasurableSpace Z] [MeasurableSpace Ω] [MeasurableSpace F]
    (ρ : Measure Z) (P : Measure Ω) [SFinite P]
    (X : Ω → F) (hX : Measurable X) (E : Set F) (hE : MeasurableSet E)
    (hP : ∀ᵐ ω ∂P, X ω ∈ E) :
    ∀ᵐ q ∂shiftedRootReferenceLaw ρ P (fun p => X p.2), q.1 ∈ E := by
  have hmap : Measurable (fun p : Z × Ω => (X p.2, p.1)) :=
    (hX.comp measurable_snd).prodMk measurable_fst
  apply (ae_map_iff hmap.aemeasurable (measurable_fst hE)).2
  apply (Measure.ae_prod_iff_ae_ae (hmap (measurable_fst hE))).2
  exact Filter.Eventually.of_forall (fun _ => hP)

/-- Root positions with an interior or exterior buffer of the given size. -/
def bufferedRoots (n : ℕ) : Set ℂ := unitBallBufferedRoots n ∪ exteriorBufferedRoots n

/-- The buffered root sets are measurable. -/
theorem measurableSet_bufferedRoots (n : ℕ) : MeasurableSet (bufferedRoots n) :=
  (measurableSet_unitBallBufferedRoots n).union (measurableSet_exteriorBufferedRoots n)

/-- Each buffered root set stays on one side of the unit circle. -/
theorem ae_bufferedRoots_side (ρ : Measure ℂ) (n : ℕ) :
    ∀ᵐ z ∂(ρ.restrict (bufferedRoots n)),
      ‖z‖ + 1 / ((n : ℝ) + 1) ≤ 1 ∨
        1 + 1 / ((n : ℝ) + 1) ≤ ‖z‖ := by
  filter_upwards [ae_restrict_mem (measurableSet_bufferedRoots n)] with z hz
  rcases hz with hin | hout
  · exact Or.inl (le_of_lt hin)
  · exact Or.inr (le_of_lt hout)

/-- A countable family of origin-inserted field events holds at almost every
sampled root for every buffer containing that root. -/
theorem IsWholePlaneGFF.ae_ae_buffered_local_events
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (μ : Ω → Measure ℂ)
    (hμ : AEMeasurable μ P) (A : Set ℂ) (hA : MeasurableSet A)
    (hfin : ∀ᵐ ω ∂P, μ ω A ≠ ∞) (ρ : Measure ℂ) [SFinite ρ] (γ : ℝ)
    (hrooted : (P.bind fun ω => ((μ ω).restrict A).map
      (fun z => (Section6.pairingProc hC ω, z))) ≪
      shiftedRootReferenceLaw ρ P (fun p => fun φ : LQGMetric.TestC0 =>
        hC p.2 φ.1 + ∫ x, φ.1 x *
          (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1))))
    (E : ∀ n : ℕ, Set (Section6.LocalTest (ball 0 (1 / (2 * ((n : ℝ) + 1)))) → ℝ))
    (hE : ∀ n, MeasurableSet (E n))
    (hfixed : ∀ n, ∀ᵐ ω ∂P,
      (fun φ : Section6.LocalTest (ball 0 (1 / (2 * ((n : ℝ) + 1)))) =>
        hC ω φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) ∈ E n) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ A → ∀ n, z ∈ bufferedRoots n →
      recenteredDistributionObservation (ball 0 (1 / (2 * ((n : ℝ) + 1))))
        (Section6.pairingProc hC ω, z) ∈ E n := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let r : ℕ → ℝ := fun n => 1 / (2 * ((n : ℝ) + 1))
  let R : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr : ∀ n, 0 < r n := by intro n; dsimp [r]; positivity
  have hrR : ∀ n, r n < R n := by
    intro n
    dsimp [r, R]
    have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [one_div_lt_one_div (by positivity) hp]
    nlinarith
  let E' : ∀ n, Set ((Section6.LocalTest (ball 0 (r n)) → ℝ) × ℂ) :=
    fun n => E n ×ˢ univ
  have hE' : ∀ n, MeasurableSet (E' n) := fun n => (hE n).prod MeasurableSet.univ
  have href : ∀ n, ∀ᵐ q ∂(shiftedRootReferenceLaw (ρ.restrict (bufferedRoots n)) P
      (fun p => fun φ : Section6.LocalTest (ball 0 (r n)) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖))), q ∈ E' n := by
    intro n
    have hm : Measurable (fun ω => fun φ : Section6.LocalTest (ball 0 (r n)) =>
        hC ω φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) := by
      apply measurable_pi_iff.mpr
      intro φ
      exact (hh.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)).add_const _
    simpa only [E', Set.mem_prod, Set.mem_univ, and_true] using
      ae_shiftedRootReferenceLaw_of_field_event (ρ.restrict (bufferedRoots n)) P
      (fun ω φ => hC ω φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖))
      hm (E n) (hE n) (hfixed n)
  have h := hh.ae_ae_countable_localized_recentered_observations μ hμ A hA hfin ρ γ
    bufferedRoots measurableSet_bufferedRoots r R hr hrR (ae_bufferedRoots_side ρ)
    hrooted E' hE' href
  filter_upwards [h] with ω hω
  filter_upwards [hω] with z hz hzA n hzn
  exact (hz hzA n hzn).1


/-- When the reference root measure is dominated by area, every sampled root
outside a null set admits a buffer on which the corresponding origin-inserted
field event holds. -/
theorem IsWholePlaneGFF.ae_ae_exists_buffered_local_event
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
    (E : ∀ n : ℕ, Set (Section6.LocalTest (ball 0 (1 / (2 * ((n : ℝ) + 1)))) → ℝ))
    (hE : ∀ n, MeasurableSet (E n))
    (hfixed : ∀ n, ∀ᵐ ω ∂P,
      (fun φ : Section6.LocalTest (ball 0 (1 / (2 * ((n : ℝ) + 1)))) =>
        hC ω φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) ∈ E n) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ A → ∃ n, z ∈ bufferedRoots n ∧
      recenteredDistributionObservation (ball 0 (1 / (2 * ((n : ℝ) + 1))))
        (Section6.pairingProc hC ω, z) ∈ E n := by
  filter_upwards [hh.ae_ae_buffered_local_events μ hμ A hA hfin ρ γ hrooted E hE hfixed,
    hh.ae_ae_buffered_root_cover μ hμ A hA hfin ρ hρ γ hrooted] with ω hev hcov
  filter_upwards [hev, hcov] with z hz hc hzA
  rcases hc hzA with ⟨n, hn⟩ | ⟨n, hn⟩
  · exact ⟨n, Or.inl hn, hz hzA n (Or.inl hn)⟩
  · exact ⟨n, Or.inr hn, hz hzA n (Or.inr hn)⟩

#print axioms IsWholePlaneGFF.ae_ae_exists_buffered_local_event
#print axioms ae_shiftedRootReferenceLaw_of_field_event
#print axioms ae_bufferedRoots_side
#print axioms IsWholePlaneGFF.ae_ae_buffered_local_events

end HarmonicBalls
