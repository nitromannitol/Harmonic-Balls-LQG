import HarmonicBalls.Proofs.Sec8.UniformSingularPhaseCertificate
import HarmonicBalls.Proofs.Sec8.RecenteredPhaseLocalEvents
import HarmonicBalls.Proofs.Sec8.RecenteredVersionIndependence

/-! # Uniform phase-frequency certificates at sampled roots

The imported ergodic theorem and distribution-valued GFF development use
Leonardo Bonanno's LatticeProb and whole-plane GFF formalizations. -/

noncomputable section

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

universe u

/-- Under rooted-law domination, the singular reference certificates hold at
almost every sampled root at all sufficiently small buffered radii. Their
frequency interpretation is for the reference measure; identifying the
rooted measure with its local decoder is a separate step. -/
theorem IsWholePlaneGFF.exists_rooted_uniform_phaseFrequency_certificate
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ β : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ₀ ν : Ω → Measure ℂ} {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
    (hh : IsWholePlaneGFF P hC hcirc) (hμ₀ : IsLQGMeasureOfField P γ γ hcirc μ₀)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC₀ : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hCCγ : LQGMeasureCoordChange P γ γ hC hcirc)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (A : Set ℂ) (hA : MeasurableSet A) (hfin : ∀ᵐ ω ∂P, μ ω A ≠ ∞)
    (ρ : Measure ℂ) [SFinite ρ] (hρ : ρ ≪ volume)
    (hrooted : (P.bind fun ω => ((μ ω).restrict A).map
      (fun z => (Section6.pairingProc hC ω, z))) ≪
      shiftedRootReferenceLaw ρ P (fun p => fun φ : LQGMetric.TestC0 =>
        hC p.2 φ.1 + ∫ x, φ.1 x *
          (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1))))
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ c a : ℝ, 0 < c ∧ a ∈ Ioo (0 : ℝ) 1 ∧
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
    ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∃ m ∈ Ioo (0 : ℝ) 1,
    ∀ N : ℕ, N₀ ≤ N →
    ∃ E : ∀ n : ℕ, Set (PhaseTorus ×
      (Section6.LocalTest (ball 0 (1 / (2 * ((n : ℝ) + 1)))) → ℝ)),
      (∀ n, MeasurableSet (E n)) ∧
      (∀ n, ∀ᵐ ω ∂P, ∀ t : PhaseTorus,
        ((t, fun φ : Section6.LocalTest (ball 0 (1 / (2 * ((n : ℝ) + 1)))) =>
          hC ω φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) ∈ E n ↔
        ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
          ({k : ℕ | k ∈ Icc (K + 1) (2 * K) ∧
            PhaseVeryGoodAnnulus (μ₀ ω) β (dyadicScale k) 0 N
              (a / (((401 : ℝ) ^ |-(γ * γ)|) ^ 2)) b
              C₁m C₁p C₂m C₂p c (torusPhase t) ∧
            AnnulusBallComparison (μ₀ ω) k 0 m}.ncard : ℝ))) ∧
      (∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ A → ∀ᶠ n in atTop,
        z ∈ bufferedRoots n ∧
        (phaseTorusOfComplex (-z),
          recenteredDistributionObservation (ball 0 (1 / (2 * ((n : ℝ) + 1))))
            (Section6.pairingProc hC ω, z)) ∈ E n) ∧
      (∀ (H : Ω → LQGMetric.DistC),
        (∀ φ : LQGMetric.TestC0,
          (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1)) →
        ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ A → ∀ᶠ n in atTop,
          z ∈ bufferedRoots n ∧
          (phaseTorusOfComplex (-z),
            fun φ : Section6.LocalTest (ball 0 (1 / (2 * ((n : ℝ) + 1)))) =>
              H ω (LQGMetric.testAffinePull 1 z φ.1.1)) ∈ E n) := by
  have hαγ : γ < lqgQ γ := by
    have hsq : γ ^ 2 < 4 := by nlinarith
    have hdiv : γ / 2 < 2 / γ := by
      apply (lt_div_iff₀ hγ).2
      nlinarith
    unfold lqgQ
    linarith
  obtain ⟨c, a, hc, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p,
    N₀, hN₀, m, hm, hcert⟩ :=
    hh.exists_uniform_singular_inserted_phaseFrequency_certificate hgrowth hfull
      hγ hγ2 hαγ hβ hb hμ₀ hν hAff hCC₀ hCCγ hζ
  refine ⟨c, a, hc, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, ?_⟩
  intro N hN
  choose E hE heq hphase using fun n : ℕ =>
    hcert N hN (1 / (2 * ((n : ℝ) + 1))) (by positivity)
  have hsample := hh.ae_ae_eventually_recentered_phase_events μ hμ A hA hfin ρ hρ γ
    hrooted E hE hphase
  refine ⟨E, hE, heq, hsample, ?_⟩
  intro H hversion
  have hver : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ (z : ℂ)
      (φ : Section6.LocalTest (ball 0 (1 / (2 * ((n : ℝ) + 1))))),
      recenteredDistributionObservation (ball 0 (1 / (2 * ((n : ℝ) + 1))))
        (Section6.pairingProc hC ω, z) φ =
          H ω (LQGMetric.testAffinePull 1 z φ.1.1) :=
    ae_all_iff.mpr (fun n => ae_recentered_observation_eq_of_version H hversion _)
  filter_upwards [hsample, hver] with ω hsampleω hverω
  filter_upwards [hsampleω] with z hz hzA
  filter_upwards [hz hzA] with n hn
  refine ⟨hn.1, ?_⟩
  rw [← funext (hverω n z)]
  exact hn.2

#print axioms IsWholePlaneGFF.exists_rooted_uniform_phaseFrequency_certificate

end HarmonicBalls
