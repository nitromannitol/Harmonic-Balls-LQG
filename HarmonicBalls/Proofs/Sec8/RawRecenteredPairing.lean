import HarmonicBalls.Proofs.Sec8.RecenteredVersionIndependence

/-! # Raw and reconstructed recentered pairings

The reconstruction uses Leonardo Bonanno's distribution-valued whole-plane
GFF development. The raw-pairing identification below requires an explicit
samplewise distribution representation; fixed-test equality alone does not
supply it. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- Exact reconstruction of all mean-zero pairings is equivalent to the
existence of a distribution representing them, modulo constants. -/
theorem meanZeroDistributionVersion_pairings_eq_iff (F : LQGMetric.TestC0 → ℝ) :
    (∀ φ : LQGMetric.TestC0, meanZeroDistributionVersion F φ.1 = F φ) ↔
      ∃ H : LQGMetric.DistC, ∀ φ : LQGMetric.TestC0, H φ.1 = F φ := by
  constructor
  · intro h
    exact ⟨meanZeroDistributionVersion F, h⟩
  · rintro ⟨H, hH⟩ φ
    have heq : F = fun ψ : LQGMetric.TestC0 => H ψ.1 := by
      funext ψ
      exact (hH ψ).symm
    rw [heq, meanZeroDistributionVersion_pairProc, LQGMetric.GFFInv.addConst_apply,
      φ.2, zero_mul, add_zero]

/-- Under samplewise distribution representation, recentering reconstructs
raw pairings simultaneously for every root and every local test. -/
theorem ae_recentered_observation_eq_raw_of_distribution_representation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ}
    (hrep : ∀ᵐ ω ∂P, ∃ H : LQGMetric.DistC,
      ∀ φ : LQGMetric.TestC0, H φ.1 = hC ω φ.1) (U : Set ℂ) :
    ∀ᵐ ω ∂P, ∀ (z : ℂ) (φ : Section6.LocalTest U),
      recenteredDistributionObservation U (Section6.pairingProc hC ω, z) φ =
        hC ω (LQGMetric.testAffinePull 1 z φ.1.1) := by
  filter_upwards [hrep] with ω hω
  intro z φ
  have ht := (meanZeroDistributionVersion_pairings_eq_iff
    (Section6.pairingProc hC ω)).2 hω (LQGMetric.GFFInv.pull0 1 z (by norm_num) φ.1)
  exact ht

/-- The joint recentered law of the raw pairings agrees with reconstruction
under any root-sampling kernel, provided samplewise representation holds. -/
theorem map_rooted_recentered_observation_eq_raw_of_distribution_representation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ}
    (hrep : ∀ᵐ ω ∂P, ∃ H : LQGMetric.DistC,
      ∀ φ : LQGMetric.TestC0, H φ.1 = hC ω φ.1)
    (U : Set ℂ) (κ : Kernel Ω ℂ) :
    (P ⊗ₘ κ).map (fun p =>
      (recenteredDistributionObservation U (Section6.pairingProc hC p.1, p.2), p.2)) =
    (P ⊗ₘ κ).map (fun p =>
      ((fun φ : Section6.LocalTest U => hC p.1 (LQGMetric.testAffinePull 1 p.2 φ.1.1)), p.2)) := by
  apply Measure.map_congr
  filter_upwards [ae_fst_of_ae_compProd P κ
    (ae_recentered_observation_eq_raw_of_distribution_representation hrep U)] with p hp
  exact Prod.ext (funext (hp p.2)) rfl

/-- Under samplewise representation, the normalized rooted comparison also
holds for the raw translated pairings. -/
theorem IsWholePlaneGFF.normalized_raw_translated_pairing_ac_origin_insertion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    (hrep : ∀ᵐ ω ∂P, ∃ H : LQGMetric.DistC,
      ∀ φ : LQGMetric.TestC0, H φ.1 = hC ω φ.1)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P) (B : Set ℂ)
    (hB : MeasurableSet B) (hfin : ∀ᵐ ω ∂P, μ ω B ≠ ∞)
    (ρ : Measure ℂ) (γ : ℝ) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hside : ∀ᵐ z ∂ρ, ‖z‖ + R ≤ 1 ∨ 1 + R ≤ ‖z‖)
    (hrooted : (P.bind fun ω => ((μ ω).restrict B).map
      (fun z => (Section6.pairingProc hC ω, z))) ≪
      shiftedRootReferenceLaw ρ P (fun p => fun φ : LQGMetric.TestC0 =>
        hC p.2 φ.1 + ∫ x, φ.1 x *
          (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1)))) :
    (P ⊗ₘ weightedRestrictionKernel P μ hμ B hB (fun _ => 1) measurable_const).map
      (fun p => ((fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.1 (LQGMetric.testAffinePull 1 p.2 φ.1.1)), p.2)) ≪
      shiftedRootReferenceLaw ρ P (fun p => fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) := by
  rw [← map_rooted_recentered_observation_eq_raw_of_distribution_representation hrep]
  exact hh.normalized_recentered_observation_ac_origin_insertion μ hμ B hB hfin ρ γ
    hr hrR hside hrooted

#print axioms IsWholePlaneGFF.normalized_raw_translated_pairing_ac_origin_insertion

/-- Fixed-coordinate almost-everywhere equality need not survive evaluation
at a random coordinate. -/
theorem exists_coordinatewise_ae_eq_but_diagonal_ne
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [NullSingletonClass P] :
    ∃ X : Ω → Ω → ℝ, (∀ t, ∀ᵐ ω ∂P, X ω t = 0) ∧ ∀ ω, X ω ω = 1 := by
  classical
  refine ⟨fun ω t => if ω = t then 1 else 0, ?_, ?_⟩
  · intro t
    have hnull : P {t} = 0 := measure_singleton t
    have ht : ∀ᵐ ω ∂P, ω ≠ t := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_eq_eq_singleton] using hnull
    filter_upwards [ht] with ω hω
    simp [hω]
  · intro ω
    simp

#print axioms meanZeroDistributionVersion_pairings_eq_iff
#print axioms map_rooted_recentered_observation_eq_raw_of_distribution_representation
#print axioms exists_coordinatewise_ae_eq_but_diagonal_ne

end HarmonicBalls
