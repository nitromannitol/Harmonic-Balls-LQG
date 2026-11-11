import HarmonicBalls.Proofs.Sec8.InsertedDistributionVersion
import HarmonicBalls.Proofs.Sec8.RootedBindTypicalPoint

/-! # Recentered rooted observations

The canonical reconstruction and whole-plane GFF comparison use Leonardo
Bonanno's distribution-valued GFF development. The weighted-root comparison
remains an explicit hypothesis. -/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- Reconstruct a distribution from the observed mean-zero field and recenter
its local pairings at the retained root. -/
def recenteredDistributionObservation (U : Set ℂ)
    (q : (LQGMetric.TestC0 → ℝ) × ℂ) : Section6.LocalTest U → ℝ :=
  fun φ => meanZeroDistributionVersion q.1 (LQGMetric.testAffinePull 1 q.2 φ.1.1)

/-- Recentered distribution observations are jointly measurable in the
observed pairing process and the root. -/
theorem measurable_recenteredDistributionObservation (U : Set ℂ) :
    Measurable (recenteredDistributionObservation U) := by
  apply measurable_pi_iff.mpr
  intro φ
  exact (measurable_translated_distribution_pairing φ.1.1).comp
    ((measurable_meanZeroDistributionVersion.comp measurable_fst).prodMk measurable_snd)

/-- Any observed-root law dominated by the whole-plane inserted reference
law remains dominated after canonical reconstruction and recentering. -/
theorem IsWholePlaneGFF.recentered_observation_ac_origin_insertion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (ρ : Measure ℂ) (γ : ℝ)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hside : ∀ᵐ z ∂ρ, ‖z‖ + R ≤ 1 ∨ 1 + R ≤ ‖z‖)
    (M : Measure ((LQGMetric.TestC0 → ℝ) × ℂ))
    (hrooted : M ≪ shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : LQGMetric.TestC0 => hC p.2 φ.1 + ∫ x, φ.1 x *
        (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1)))) :
    M.map (fun q => (recenteredDistributionObservation (ball 0 r) q, q.2)) ≪
      shiftedRootReferenceLaw ρ P (fun p => fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) := by
  have hT := measurable_recenteredDistributionObservation (ball 0 r)
  have hmap := hrooted.map (hT.prodMk measurable_snd)
  rw [shiftedRootReferenceLaw_map_root_operation ρ P _
    (hh.measurable_wholePlane_inserted_pairings γ) _ hT] at hmap
  exact hmap.trans (hh.rooted_inserted_reconstruction_local_equivalence ρ γ hr hrR hside).1

/-- A normalized root sample inherits the recentered local comparison from
an unnormalized observed-root comparison, including when the sampled mass
vanishes. -/
theorem IsWholePlaneGFF.normalized_recentered_observation_ac_origin_insertion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (μ : Ω → Measure ℂ)
    (hμ : AEMeasurable μ P) (B : Set ℂ) (hB : MeasurableSet B)
    (hfin : ∀ᵐ ω ∂P, μ ω B ≠ ∞) (ρ : Measure ℂ) (γ : ℝ)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hside : ∀ᵐ z ∂ρ, ‖z‖ + R ≤ 1 ∨ 1 + R ≤ ‖z‖)
    (hrooted : (P.bind fun ω => ((μ ω).restrict B).map
      (fun z => (Section6.pairingProc hC ω, z))) ≪
      shiftedRootReferenceLaw ρ P (fun p => fun φ : LQGMetric.TestC0 =>
        hC p.2 φ.1 + ∫ x, φ.1 x *
          (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1)))) :
    (P ⊗ₘ weightedRestrictionKernel P μ hμ B hB (fun _ => 1) measurable_const).map
      (fun p => (recenteredDistributionObservation (ball 0 r)
        (Section6.pairingProc hC p.1, p.2), p.2)) ≪
      shiftedRootReferenceLaw ρ P (fun p => fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hobs : Measurable (fun p : Ω × ℂ => (Section6.pairingProc hC p.1, p.2)) :=
    ((Section6.measurable_pairingProc hh).comp measurable_fst).prodMk measurable_snd
  have hT := (measurable_recenteredDistributionObservation (ball 0 r)).prodMk measurable_snd
  have hdom := observed_normalized_compProd_ac_restricted_bind P μ hμ
    (Section6.pairingProc hC) (Section6.measurable_pairingProc hh) B hB hfin
  have hmap := hdom.map hT
  rw [Measure.map_map hT hobs] at hmap
  exact hmap.trans (hh.recentered_observation_ac_origin_insertion ρ γ hr hrR hside _ hrooted)

/-- A measurable property of the origin-inserted local reference field holds
at almost every sampled root after canonical reconstruction and recentering,
provided the observed rooted-law comparison holds. -/
theorem IsWholePlaneGFF.ae_ae_recentered_observation_of_rooted_comparison
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (μ : Ω → Measure ℂ)
    (hμ : AEMeasurable μ P) (B : Set ℂ) (hB : MeasurableSet B)
    (hfin : ∀ᵐ ω ∂P, μ ω B ≠ ∞) (ρ : Measure ℂ) (γ : ℝ)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hside : ∀ᵐ z ∂ρ, ‖z‖ + R ≤ 1 ∨ 1 + R ≤ ‖z‖)
    (hrooted : (P.bind fun ω => ((μ ω).restrict B).map
      (fun z => (Section6.pairingProc hC ω, z))) ≪
      shiftedRootReferenceLaw ρ P (fun p => fun φ : LQGMetric.TestC0 =>
        hC p.2 φ.1 + ∫ x, φ.1 x *
          (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1))))
    (E : Set ((Section6.LocalTest (ball 0 r) → ℝ) × ℂ)) (hE : MeasurableSet E)
    (href : ∀ᵐ q ∂(shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖))), q ∈ E) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ B →
      (recenteredDistributionObservation (ball 0 r) (Section6.pairingProc hC ω, z), z) ∈ E := by
  let T := fun q => (recenteredDistributionObservation (ball 0 r) q, q.2)
  have hT : Measurable T :=
    (measurable_recenteredDistributionObservation (ball 0 r)).prodMk measurable_snd
  have hdom := hh.recentered_observation_ac_origin_insertion ρ γ hr hrR hside _ hrooted
  have hmap : ∀ᵐ q ∂(P.bind fun ω => ((μ ω).restrict B).map
      (fun z => (Section6.pairingProc hC ω, z))), T q ∈ E :=
    (ae_map_iff hT.aemeasurable hE).1 (hdom.ae_le href)
  exact ae_ae_mem_of_observed_restricted_bind P μ hμ (Section6.pairingProc hC)
    (Section6.measurable_pairingProc hh) B hB hfin hmap

end HarmonicBalls
