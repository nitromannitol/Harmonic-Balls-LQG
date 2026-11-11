import HarmonicBalls.Proofs.Sec8.RecenteredRootedObservation
import HarmonicBalls.Proofs.Sec8.RootedSamplingProbability

/-! # Recentered distribution-valued versions

The countable reconstruction uses Leonardo Bonanno's distribution-valued
whole-plane GFF development. Agreement at fixed tests yields simultaneous
agreement after reconstruction, including at a field-dependent root. -/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- A distribution-valued version fixes the reconstructed distribution up to
its unit-circle mollifier gauge on one full-measure event. -/
theorem ae_meanZeroDistributionVersion_eq_of_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} (H : Ω → LQGMetric.DistC)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1)) :
    ∀ᵐ ω ∂P, meanZeroDistributionVersion (Section6.pairingProc hC ω) =
      LQGMetric.addConst (H ω) (-(H ω (LQGMetric.CircleAvg.circBump 0 0 1))) := by
  filter_upwards [ae_all_iff.mpr (fun c : LQGMetric.CoordJ =>
    hversion (LQGMetric.MarkovGerm.meanZeroApprox (LQGMetric.comb ⊤ c) 0))] with ω hω
  have heq : meanZeroDistributionVersion (Section6.pairingProc hC ω) =
      meanZeroDistributionVersion (fun φ => H ω φ.1) := by
    unfold meanZeroDistributionVersion
    congr 1
    funext c
    exact (hω c).symm
  rw [heq, meanZeroDistributionVersion_pairProc]

/-- A fixed-test distribution version and reconstruction agree simultaneously
at every translated mean-zero test and after every distribution insertion. -/
theorem ae_inserted_translated_pairing_of_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} (H : Ω → LQGMetric.DistC)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1)) :
    ∀ᵐ ω ∂P, ∀ (z : ℂ) (φ : LQGMetric.TestC0) (k : LQGMetric.DistC),
      meanZeroDistributionVersion (fun ψ => hC ω ψ.1 + k ψ.1)
          (LQGMetric.testAffinePull 1 z φ.1) =
        H ω (LQGMetric.testAffinePull 1 z φ.1) + k (LQGMetric.testAffinePull 1 z φ.1) := by
  filter_upwards [ae_all_iff.mpr (fun c : LQGMetric.CoordJ =>
    hversion (LQGMetric.MarkovGerm.meanZeroApprox (LQGMetric.comb ⊤ c) 0))] with ω hω
  intro z φ k
  apply meanZeroDistributionVersion_inserted_translated_pairing
  intro c
  exact (hω c).symm

/-- The recentered observation agrees with every distribution-valued version
at every root and every local mean-zero test on a common full-measure event. -/
theorem ae_recentered_observation_eq_of_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} (H : Ω → LQGMetric.DistC)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1)) (U : Set ℂ) :
    ∀ᵐ ω ∂P, ∀ (z : ℂ) (φ : Section6.LocalTest U),
      recenteredDistributionObservation U (Section6.pairingProc hC ω, z) φ =
        H ω (LQGMetric.testAffinePull 1 z φ.1.1) := by
  filter_upwards [ae_inserted_translated_pairing_of_version H hversion] with ω hω
  intro z φ
  change meanZeroDistributionVersion (fun ψ : LQGMetric.TestC0 => hC ω ψ.1)
      (LQGMetric.testAffinePull 1 z φ.1.1) = _
  simpa using hω z φ.1 (0 : LQGMetric.DistC)

/-- Root sampling by an arbitrary kernel preserves the joint recentered law
of the reconstruction and any fixed-test distribution-valued version. -/
theorem map_rooted_recentered_observation_eq_of_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} (H : Ω → LQGMetric.DistC)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1))
    (U : Set ℂ) (κ : Kernel Ω ℂ) :
    (P ⊗ₘ κ).map (fun p =>
      (recenteredDistributionObservation U (Section6.pairingProc hC p.1, p.2), p.2)) =
    (P ⊗ₘ κ).map (fun p =>
      ((fun φ : Section6.LocalTest U => H p.1 (LQGMetric.testAffinePull 1 p.2 φ.1.1)), p.2)) := by
  apply Measure.map_congr
  filter_upwards [ae_fst_of_ae_compProd P κ
    (ae_recentered_observation_eq_of_version H hversion U)] with p hp
  exact Prod.ext (funext (hp p.2)) rfl

/-- The normalized rooted comparison holds for the translated pairings of
any distribution-valued version, under the same rooted-law hypothesis. -/
theorem IsWholePlaneGFF.normalized_translated_version_ac_origin_insertion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (H : Ω → LQGMetric.DistC)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1))
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
        H p.1 (LQGMetric.testAffinePull 1 p.2 φ.1.1)), p.2)) ≪
      shiftedRootReferenceLaw ρ P (fun p => fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) := by
  rw [← map_rooted_recentered_observation_eq_of_version H hversion]
  exact hh.normalized_recentered_observation_ac_origin_insertion μ hμ B hB hfin ρ γ
    hr hrR hside hrooted

end HarmonicBalls
