import HarmonicBalls.Proofs.Sec8.RawRecenteredPairing
import HarmonicBalls.Proofs.Sec8.RecenteredPhaseLocalEvents
import HarmonicBalls.Proofs.Sec8.CanonicalPhaseCertificate

/-! # Raw observations at sampled roots

The reconstruction uses Leonardo Bonanno's distribution-valued GFF work in
`LatticeProb.Bonanno.LQGMetric.Field.MarkovGerm`,
`LatticeProb.Bonanno.LQGMetric.Field.RandomDistVersion`,
`LatticeProb.Bonanno.LQGMetric.Field.GFFLaw`,
`LatticeProb.Bonanno.LQGMetric.Field.ExistGFF`, and
`LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance`.

These conditional bridges do not assert that raw pairings have a samplewise
distribution representation. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set

namespace HarmonicBalls

/-- A countable family of sampled-root coordinate agreements suffices for
any sequence of phase events determined by those coordinates. The exceptional
set for each coordinate may depend on the coordinate. -/
theorem ae_ae_eventually_raw_phase_events_of_countable_coordinates
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (μ : Ω → Measure ℂ) (A : Set ℂ)
    (hC : Ω → (ℂ → ℝ) → ℝ)
    (U : ℕ → Set ℂ)
    (T : ∀ n, ℕ → Section6.LocalTest (U n))
    (E : ∀ n, Set (PhaseTorus × (Section6.LocalTest (U n) → ℝ)))
    (hE : ∀ n t f g, (∀ k, f (T n k) = g (T n k)) →
      (t, f) ∈ E n → (t, g) ∈ E n)
    (hcoord : ∀ n k, ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ A →
      recenteredDistributionObservation (U n) (Section6.pairingProc hC ω, z) (T n k) =
        hC ω (LQGMetric.testAffinePull 1 z (T n k).1.1))
    (hsample : ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ A → ∀ᶠ n : ℕ in atTop,
      z ∈ bufferedRoots n ∧
        (phaseTorusOfComplex (-z), recenteredDistributionObservation (U n)
          (Section6.pairingProc hC ω, z)) ∈ E n) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ A → ∀ᶠ n : ℕ in atTop,
      z ∈ bufferedRoots n ∧
        (phaseTorusOfComplex (-z), fun φ : Section6.LocalTest (U n) =>
          hC ω (LQGMetric.testAffinePull 1 z φ.1.1)) ∈ E n := by
  have hc : ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ n k, z ∈ A →
      recenteredDistributionObservation (U n) (Section6.pairingProc hC ω, z) (T n k) =
        hC ω (LQGMetric.testAffinePull 1 z (T n k).1.1) := by
    filter_upwards [ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun k => hcoord n k))] with ω hω
    exact ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun k => hω n k))
  filter_upwards [hsample, hc] with ω hsampleω hcω
  filter_upwards [hsampleω, hcω] with z hz hcz
  intro hzA
  filter_upwards [hz hzA] with n hn
  exact ⟨hn.1, hE n _ _ _ (fun k => hcz n k hzA) hn.2⟩

/-- Agreement at the sampled root, simultaneously in the local test, is
sufficient to identify the entire joint raw and reconstructed laws. -/
theorem map_rooted_recentered_observation_eq_raw_of_ae_sampled
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} (U : Set ℂ) (κ : Kernel Ω ℂ)
    (hraw : ∀ᵐ p ∂(P ⊗ₘ κ), ∀ φ : Section6.LocalTest U,
      recenteredDistributionObservation U (Section6.pairingProc hC p.1, p.2) φ =
        hC p.1 (LQGMetric.testAffinePull 1 p.2 φ.1.1)) :
    (P ⊗ₘ κ).map (fun p =>
      (recenteredDistributionObservation U (Section6.pairingProc hC p.1, p.2), p.2)) =
    (P ⊗ₘ κ).map (fun p =>
      ((fun φ : Section6.LocalTest U => hC p.1 (LQGMetric.testAffinePull 1 p.2 φ.1.1)), p.2)) := by
  apply Measure.map_congr
  filter_upwards [hraw] with p hp
  exact Prod.ext (funext hp) rfl

/-- Coordinatewise agreement under the sampled-root law identifies the
joint cylinder laws when the raw translated process is measurable. No common
event of equality at every test is required. -/
theorem IsWholePlaneGFF.map_rooted_recentered_observation_eq_raw_of_coordinatewise
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (U : Set ℂ) (κ : Kernel Ω ℂ)
    (hraw_meas : Measurable (fun p : Ω × ℂ =>
      fun φ : Section6.LocalTest U => hC p.1 (LQGMetric.testAffinePull 1 p.2 φ.1.1)))
    (hcoord : ∀ φ : Section6.LocalTest U,
      (fun p => recenteredDistributionObservation U (Section6.pairingProc hC p.1, p.2) φ)
        =ᵐ[P ⊗ₘ κ] (fun p => hC p.1 (LQGMetric.testAffinePull 1 p.2 φ.1.1))) :
    (P ⊗ₘ κ).map (fun p =>
      (recenteredDistributionObservation U (Section6.pairingProc hC p.1, p.2), p.2)) =
    (P ⊗ₘ κ).map (fun p =>
      ((fun φ : Section6.LocalTest U => hC p.1 (LQGMetric.testAffinePull 1 p.2 φ.1.1)), p.2)) := by
  have hcan : Measurable (fun p : Ω × ℂ =>
      recenteredDistributionObservation U (Section6.pairingProc hC p.1, p.2)) :=
    (measurable_recenteredDistributionObservation U).comp
      (((Section6.measurable_pairingProc hh).comp measurable_fst).prodMk measurable_snd)
  exact map_prod_eq_of_coordinatewise_ae_eq Prod.snd hcan hraw_meas measurable_snd hcoord

#print axioms ae_ae_eventually_raw_phase_events_of_countable_coordinates
#print axioms map_rooted_recentered_observation_eq_raw_of_ae_sampled
#print axioms IsWholePlaneGFF.map_rooted_recentered_observation_eq_raw_of_coordinatewise

end HarmonicBalls
