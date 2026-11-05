import HarmonicBalls.Proofs.Sec8.TranslatedDistributionInsertion
import HarmonicBalls.Proofs.Sec8.RootedInsertionLocalization

/-! # Reconstruction with distribution insertions

The countable reconstruction is from Leonardo Bonanno's distribution-valued
whole-plane GFF development. -/

noncomputable section

open MeasureTheory Filter Metric Set

namespace HarmonicBalls

/-- Reconstructing the sum of the mean-zero pairings of two distributions
fixes the same circle-bump gauge as reconstructing their sum. -/
theorem meanZeroDistributionVersion_add_pairings (h k : LQGMetric.DistC) :
    meanZeroDistributionVersion (fun φ => h φ.1 + k φ.1) =
      LQGMetric.addConst (h + k) (-((h + k) (LQGMetric.CircleAvg.circBump 0 0 1))) := by
  simpa only [add_apply] using meanZeroDistributionVersion_pairProc (h + k)

/-- Countably many shared coordinates suffice to reconstruct all translated
mean-zero pairings after any distribution-valued insertion. -/
theorem meanZeroDistributionVersion_inserted_translated_pairing
    (F : LQGMetric.TestC0 → ℝ) (h k : LQGMetric.DistC)
    (hcoords : ∀ c : LQGMetric.CoordJ,
      F (LQGMetric.MarkovGerm.meanZeroApprox (LQGMetric.comb ⊤ c) 0) =
        h (LQGMetric.MarkovGerm.meanZeroApprox (LQGMetric.comb ⊤ c) 0).1)
    (z : ℂ) (φ : LQGMetric.TestC0) :
    meanZeroDistributionVersion (fun ψ => F ψ + k ψ.1)
        (LQGMetric.testAffinePull 1 z φ.1) =
      h (LQGMetric.testAffinePull 1 z φ.1) + k (LQGMetric.testAffinePull 1 z φ.1) := by
  have heq : meanZeroDistributionVersion (fun ψ => F ψ + k ψ.1) =
      meanZeroDistributionVersion (fun ψ => h ψ.1 + k ψ.1) := by
    unfold meanZeroDistributionVersion
    congr 1
    funext c
    dsimp only
    rw [hcoords c]
  rw [heq, meanZeroDistributionVersion_add_pairings, LQGMetric.GFFInv.addConst_apply]
  have hz := (LQGMetric.GFFInv.pull0 1 z (by norm_num) φ).2
  change ∫ x, LQGMetric.testAffinePull 1 z φ.1 x = 0 at hz
  rw [hz, zero_mul, add_zero, add_apply]

/-- On one probability-one event, reconstruction commutes with arbitrary
distribution insertions and translations of all mean-zero test functions. -/
theorem IsWholePlaneGFF.ae_canonical_inserted_translated_pairing
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ (z : ℂ) (φ : LQGMetric.TestC0) (k : LQGMetric.DistC),
      meanZeroDistributionVersion (fun ψ => hC ω ψ.1 + k ψ.1)
          (LQGMetric.testAffinePull 1 z φ.1) =
        meanZeroDistributionVersion (Section6.pairingProc hC ω)
          (LQGMetric.testAffinePull 1 z φ.1) + k (LQGMetric.testAffinePull 1 z φ.1) := by
  filter_upwards [ae_all_iff.mpr (fun c : LQGMetric.CoordJ =>
    hh.canonical_distribution_version_pairing
      (LQGMetric.MarkovGerm.meanZeroApprox (LQGMetric.comb ⊤ c) 0))] with ω hω
  intro z φ k
  apply meanZeroDistributionVersion_inserted_translated_pairing
  intro c
  exact (hω c).symm

/-- The whole-plane rooted logarithmic insertion as a distribution. -/
def wholePlaneRootInsertionDistribution (γ : ℝ) (z : ℂ) : LQGMetric.DistC :=
  Distribution.ofFun ⊤ (fun x : ℂ =>
    -γ * Real.log ‖x - z‖ + γ * Real.log (max ‖x‖ 1)) volume ⊤

/-- The rooted logarithmic insertion is locally integrable. -/
theorem locallyIntegrable_wholePlaneRootInsertion (γ : ℝ) (z : ℂ) :
    LocallyIntegrable (fun x : ℂ =>
      -γ * Real.log ‖x - z‖ + γ * Real.log (max ‖x‖ 1)) volume := by
  have hl := (locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm z).smul (-γ)
  have hn : LocallyIntegrable (fun x : ℂ => γ * Real.log (max ‖x‖ 1)) volume :=
    (continuous_const.mul continuous_wholePlaneNormalization).locallyIntegrable
  convert hl.add hn using 1

/-- Evaluation of the rooted logarithmic distribution is the integral used
in the whole-plane rooted-field formula. -/
theorem wholePlaneRootInsertionDistribution_apply (γ : ℝ) (z : ℂ)
    (φ : LQGMetric.TestC) :
    wholePlaneRootInsertionDistribution γ z φ = ∫ x, φ x *
      (-γ * Real.log ‖x - z‖ + γ * Real.log (max ‖x‖ 1)) := by
  rw [wholePlaneRootInsertionDistribution, Distribution.ofFun_apply
    ((locallyIntegrable_wholePlaneRootInsertion γ z).locallyIntegrableOn _)]
  rfl

/-- Recentring the whole-plane insertion turns its singularity into the
origin logarithm and translates the normalization term. -/
theorem integral_wholePlaneRootInsertion_translated (γ : ℝ) (z : ℂ)
    (φ : LQGMetric.TestC) :
    (∫ x, (LQGMetric.testAffinePull 1 z φ) x *
      (-γ * Real.log ‖x - z‖ + γ * Real.log (max ‖x‖ 1))) =
    ∫ y, φ y * (-γ * Real.log ‖y‖ + γ * Real.log (max ‖z + y‖ 1)) := by
  have ht := integral_add_right_eq_self (μ := volume)
    (fun x : ℂ => φ (x - z) *
      (-γ * Real.log ‖x - z‖ + γ * Real.log (max ‖x‖ 1))) z
  simpa [LQGMetric.testAffinePull_apply, add_comm] using ht.symm

/-- With one exceptional set, the reconstructed rooted-inserted field can
be translated at every root and tested against every mean-zero test. -/
theorem IsWholePlaneGFF.ae_canonical_root_insertion_translated_pairing
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ) :
    ∀ᵐ ω ∂P, ∀ (z : ℂ) (φ : LQGMetric.TestC0),
      meanZeroDistributionVersion (fun ψ => hC ω ψ.1 + ∫ x, ψ.1 x *
        (-γ * Real.log ‖x - z‖ + γ * Real.log (max ‖x‖ 1)))
          (LQGMetric.testAffinePull 1 z φ.1) =
        meanZeroDistributionVersion (Section6.pairingProc hC ω)
          (LQGMetric.testAffinePull 1 z φ.1) + ∫ x, φ.1 x *
            (-γ * Real.log ‖x‖ + γ * Real.log (max ‖z + x‖ 1)) := by
  filter_upwards [hh.ae_canonical_inserted_translated_pairing] with ω hω
  intro z φ
  have h := hω z φ (wholePlaneRootInsertionDistribution γ z)
  simp_rw [wholePlaneRootInsertionDistribution_apply] at h
  rw [integral_wholePlaneRootInsertion_translated] at h
  exact h

/-- The recentered reconstructed rooted-inserted reference law is
identical to the canonical translated-distribution insertion law. -/
theorem IsWholePlaneGFF.root_insertion_reconstruction_reference_law_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (ρ : Measure ℂ) (γ : ℝ) {U : Set ℂ} :
    shiftedRootReferenceLaw ρ P (fun p => fun φ : Section6.LocalTest U =>
      meanZeroDistributionVersion (fun ψ => hC p.2 ψ.1 + ∫ x, ψ.1 x *
        (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1)))
          (LQGMetric.testAffinePull 1 p.1 φ.1.1)) =
    shiftedRootReferenceLaw ρ P (fun p => fun φ : Section6.LocalTest U =>
      meanZeroDistributionVersion (Section6.pairingProc hC p.2)
          (LQGMetric.testAffinePull 1 p.1 φ.1.1) + ∫ x, φ.1.1 x *
            (-γ * Real.log ‖x‖ + γ * Real.log (max ‖p.1 + x‖ 1))) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  unfold shiftedRootReferenceLaw
  apply Measure.map_congr
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := ρ) (ν := P)).ae
    (hh.ae_canonical_root_insertion_translated_pairing γ)] with p hp
  congr 1
  funext φ
  exact hp p.1 φ.1

/-- After canonical reconstruction and recentering, the whole-plane
rooted-insertion reference law has the local null sets of the origin
logarithm field whenever the observation buffer avoids the unit circle. -/
theorem IsWholePlaneGFF.rooted_inserted_reconstruction_local_equivalence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (ρ : Measure ℂ) (γ : ℝ)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hside : ∀ᵐ z ∂ρ, ‖z‖ + R ≤ 1 ∨ 1 + R ≤ ‖z‖) :
    let A := shiftedRootReferenceLaw ρ P (fun p => fun φ : Section6.LocalTest (ball 0 r) =>
      meanZeroDistributionVersion (fun ψ => hC p.2 ψ.1 + ∫ x, ψ.1 x *
        (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1)))
          (LQGMetric.testAffinePull 1 p.1 φ.1.1))
    let B := shiftedRootReferenceLaw ρ P (fun p => fun φ : Section6.LocalTest (ball 0 r) =>
      hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖))
    A ≪ B ∧ B ≪ A := by
  have heq := hh.root_insertion_reconstruction_reference_law_eq ρ γ (U := ball 0 r)
  have h := hh.rooted_canonical_distribution_normalization_equivalence ρ hr hrR γ (-γ) hside
  rw [heq]
  have hcomm : (fun p : ℂ × Ω => fun φ : Section6.LocalTest (ball 0 r) =>
      meanZeroDistributionVersion (Section6.pairingProc hC p.2)
        (LQGMetric.testAffinePull 1 p.1 φ.1.1) + ∫ x, φ.1.1 x *
          (-γ * Real.log ‖x‖ + γ * Real.log (max ‖p.1 + x‖ 1))) =
      (fun p : ℂ × Ω => fun φ : Section6.LocalTest (ball 0 r) =>
        meanZeroDistributionVersion (Section6.pairingProc hC p.2)
          (LQGMetric.testAffinePull 1 p.1 φ.1.1) + ∫ x, φ.1.1 x *
            (γ * Real.log (max ‖p.1 + x‖ 1) + -γ * Real.log ‖x‖)) := by
    funext p φ
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hcomm]
  exact h

#print axioms IsWholePlaneGFF.rooted_inserted_reconstruction_local_equivalence
#print axioms IsWholePlaneGFF.ae_canonical_root_insertion_translated_pairing
#print axioms IsWholePlaneGFF.ae_canonical_inserted_translated_pairing

end HarmonicBalls
