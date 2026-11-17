import HarmonicBalls.Proofs.GFF.DMSInsertedLocalAbsoluteContinuity

/-!
# Root-dependent local event transfer

A measurable marked event with local sections transfers from the field with a
root insertion to almost every root of the singular Liouville measure.
-/

noncomputable section

open MeasureTheory Set Metric

namespace HarmonicBalls

/-- Restrict global mean-zero test pairings to a local region. -/
def restrictGlobalPairings (U : Set ℂ) (v : ModConstTestPairings univ) :
    ModConstTestPairings U := fun φ =>
  v ⟨φ.1, ⟨φ.2.1.1, φ.2.1.2.1, subset_univ _⟩, φ.2.2⟩

/-- A jointly measurable marked event whose sections are measurable local events
holds at almost every singular-measure root if its sections hold for the
whole-plane field with the corresponding root insertion. -/
theorem IsWholePlaneGFF.ae_singular_root_local_of_reference
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < lqgQ γ) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (S : Set (ModConstTestPairings univ × ℂ)) (hS : MeasurableSet S)
    (href : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (0 : ℂ) 1 →
      ∃ r : ℝ, 0 < r ∧ r < ‖z‖ ∧ ‖z‖ + r < 1 ∧
        ∃ E : Set (ModConstTestPairings (ball z r)), MeasurableSet E ∧
          (∀ v, (v, z) ∈ S ↔ restrictGlobalPairings (ball z r) v ∈ E) ∧
          ∀ᵐ ω ∂P, (fun φ => hC ω φ.1 +
            ∫ w, φ.1 w * (-γ * Real.log ‖w - z‖)) ∈ E) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) 1 →
      (localModConstField α hC univ ω, z) ∈ S := by
  apply hh.ae_singular_local_marked_of_ae_shifted hγ hγ2 hα hμ hν univ S hS
  filter_upwards [href] with z hz hzball
  obtain ⟨r, hr, hrz, hrunit, E, hE, hlocal, hgood⟩ := hz hzball
  let A : Ω → ModConstTestPairings (ball z r) := fun ω =>
    localModConstField α (fun _ : Unit => shiftedPairing γ z (hC ω)) (ball z r) ()
  let B : Ω → ModConstTestPairings (ball z r) := fun ω φ =>
    hC ω φ.1 + ∫ w, φ.1 w * (-γ * Real.log ‖w - z‖)
  have hAm : Measurable A := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable fun ω => (hC ω φ.1 + ∫ w, dmsShift γ z w * φ.1 w) -
      α * ∫ x, φ.1 x * Real.log ‖x‖
    exact ((hh.measurable_pairing φ.1 ⟨φ.2.1.1, φ.2.1.2.1, subset_univ _⟩).add_const _).sub_const _
  have hBm : Measurable B := by
    apply measurable_pi_iff.mpr
    intro φ
    exact (hh.measurable_pairing φ.1 ⟨φ.2.1.1, φ.2.1.2.1, subset_univ _⟩).add_const _
  have hab : P.map A ≪ P.map B :=
    (hh.inserted_marked_local_law_equivalence_of_radius α γ hr hrz hrunit).1
  have hB : ∀ᵐ v ∂(P.map B), v ∈ E := (ae_map_iff hBm.aemeasurable hE).2 hgood
  have hA : ∀ᵐ ω ∂P, A ω ∈ E := (ae_map_iff hAm.aemeasurable hE).1 (hab.ae_le hB)
  filter_upwards [hA] with ω hω
  apply (hlocal _).2
  exact hω

end HarmonicBalls
