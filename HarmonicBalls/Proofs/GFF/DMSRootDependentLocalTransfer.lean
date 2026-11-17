import HarmonicBalls.Proofs.GFF.DMSInsertedLocalAbsoluteContinuity
import HarmonicBalls.Proofs.Sec8.MeanZeroDistributionVersion

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

open MeasureTheory Set TopologicalSpace
open scoped Distributions
namespace HarmonicBalls

/-- Form a mean-zero local test by subtracting its integral times a unit-mass test. -/
def localGaugeTest (U : Opens ℂ) (ρ χ : LQGMetric.TestOn U)
    (hρ : ∫ x, ρ x = 1) : {φ : ℂ → ℝ // IsTestFunction U φ ∧ ∫ x, φ x = 0} := by
  let ψ : LQGMetric.TestOn U := χ - (∫ x, χ x) • ρ
  let ψ' : LQGMetric.TestC := LQGMetric.MarkovGerm.extC U ψ
  refine ⟨ψ', ⟨⟨ψ'.contDiff, ψ'.hasCompactSupport.isCompact, ?_⟩, ?_⟩⟩
  · simpa [ψ', LQGMetric.MarkovGerm.coe_extC] using ψ.tsupport_subset
  · simp only [ψ', LQGMetric.MarkovGerm.coe_extC]
    change ∫ x, (χ x - (∫ y, χ y) * ρ x) = 0
    rw [integral_sub (χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport)
      ((ρ.continuous.integrable_of_hasCompactSupport ρ.hasCompactSupport).const_mul _),
      integral_const_mul, hρ, mul_one, sub_self]

/-- Reconstruct a distribution on an open set from its local mean-zero pairings. -/
def localGaugeVersion (U : Opens ℂ) (ρ : LQGMetric.TestOn U)
    (hρ : ∫ x, ρ x = 1) (v : ModConstTestPairings U) : LQGMetric.DistOn U :=
  LQGMetric.pairJInv U (fun c => v (localGaugeTest U ρ (LQGMetric.comb U c) hρ))

/-- Local reconstruction is measurable for the cylinder sigma-algebra. -/
theorem measurable_localGaugeVersion (U : Opens ℂ) (ρ : LQGMetric.TestOn U)
    (hρ : ∫ x, ρ x = 1) : Measurable (localGaugeVersion U ρ hρ) := by
  apply (LQGMetric.measurable_pairJInv U).comp
  exact measurable_pi_iff.mpr fun c => measurable_pi_apply _

/-- Reconstructing the local pairings of a distribution fixes its gauge locally. -/
theorem localGaugeVersion_pairings (U : Opens ℂ) (ρ : LQGMetric.TestOn U)
    (hρ : ∫ x, ρ x = 1) (h : LQGMetric.DistC) :
    localGaugeVersion U ρ hρ (fun φ => h ⟨φ.1, φ.2.1.1, φ.2.1.2.1, subset_univ _⟩) =
      LQGMetric.restrictTo U (LQGMetric.addConst h (-(h (LQGMetric.MarkovGerm.extC U ρ)))) := by
  unfold localGaugeVersion
  rw [show (fun c => h ⟨(localGaugeTest U ρ (LQGMetric.comb U c) hρ).1,
      (localGaugeTest U ρ (LQGMetric.comb U c) hρ).2.1.1,
      (localGaugeTest U ρ (LQGMetric.comb U c) hρ).2.1.2.1, subset_univ _⟩) =
    LQGMetric.pairJ U (LQGMetric.restrictTo U
      (LQGMetric.addConst h (-(h (LQGMetric.MarkovGerm.extC U ρ))))) by
    funext c
    change h (LQGMetric.MarkovGerm.extC U (LQGMetric.comb U c -
      (∫ x, LQGMetric.comb U c x) • ρ)) = _
    change _ = LQGMetric.addConst h (-(h (LQGMetric.MarkovGerm.extC U ρ)))
      (LQGMetric.MarkovGerm.extC U (LQGMetric.comb U c))
    rw [map_sub, map_smul, map_sub, map_smul, LQGMetric.GFFInv.addConst_apply]
    simp only [smul_eq_mul, LQGMetric.MarkovGerm.coe_extC]
    ring]
  exact LQGMetric.pairJInv_pairJ U _

/-- Local reconstruction preserves every mean-zero pairing of a distribution. -/
theorem localGaugeVersion_apply (U : Opens ℂ) (ρ : LQGMetric.TestOn U)
    (hρ : ∫ x, ρ x = 1) (h : LQGMetric.DistC) (φ : LQGMetric.TestOn U)
    (hφ : ∫ x, φ x = 0) :
    localGaugeVersion U ρ hρ (fun ψ => h ⟨ψ.1, ψ.2.1.1, ψ.2.1.2.1, subset_univ _⟩) φ =
      h (LQGMetric.MarkovGerm.extC U φ) := by
  rw [localGaugeVersion_pairings]
  change LQGMetric.addConst h (-(h (LQGMetric.MarkovGerm.extC U ρ)))
    (LQGMetric.MarkovGerm.extC U φ) = _
  rw [LQGMetric.GFFInv.addConst_apply]
  simp only [LQGMetric.MarkovGerm.coe_extC, hφ, zero_mul, add_zero]

end HarmonicBalls
