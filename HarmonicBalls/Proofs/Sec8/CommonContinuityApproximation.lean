import HarmonicBalls.Proofs.Sec8.CommonRootedContinuitySets
import HarmonicBalls.Proofs.Sec8.LocalNormalizedMassApproximation

/-! # Reference approximations on common continuity sets

The imported Section 8 argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem. The second-law convergence is not
asserted here.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A reference LQG measure and another locally finite random measure have
common continuity sets, on which the reference normalized masses have local
field approximations. -/
theorem IsWholePlaneGFF.exists_common_continuity_reference_approximations
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} (Q : Measure Ξ) [IsProbabilityMeasure Q] {γ α₀ R : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (ν : Ξ → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hν : AEMeasurable ν Q) (hνloc : ∀ᵐ x ∂Q, IsLocallyFiniteMeasure (ν x))
    (hR : 0 < R)
    (hpos : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → μ ω (ball (0 : ℂ) r) ≠ 0) :
    ∃ ε ∈ Ioo (0 : ℝ) R, ∃ S : Set (Set ℂ), S.Countable ∧ IsPiSystem S ∧
      univ ∈ S ∧ (∀ A ∈ S, MeasurableSet A) ∧
      (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S ∧
      ∃ E : ℕ → Set ℂ, (∀ n, MeasurableSet (E n)) ∧ Monotone E ∧
        (⋃ n, E n) = ball 0 ε ∧
        (∀ n z, z ∈ E n → closedBall z (dyadicScale n) ⊆ ball 0 ε) ∧
        (∀ᵐ x ∂Q, ∀ A ∈ S, (∀ n, ν x (frontier (E n)) = 0 ∧
          ν x (frontier (A ∩ E n)) = 0) ∧ ν x (frontier (⋃ n, E n)) = 0 ∧
          ν x (frontier (A ∩ ⋃ n, E n)) = 0) ∧
        ∃ f : S → ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → ℝ,
          (∀ A n, Measurable (f A n)) ∧ ∀ A,
            TendstoInMeasure P (fun n ω => f A n (Section6.localPairingProc (ball 0 ε) hC ω))
              atTop (fun ω => (normalizedRestriction (μ ω) (ball 0 ε) A.val).toReal) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) :=
    hμ.mono fun _ h => h.isLocallyFiniteMeasure
  obtain ⟨ε, hε, S, hc, hp, hu, ho, hg, E, hEm, hmono, hunion, hbuffer, hfrontμ, hfrontν⟩ :=
    exists_common_continuity_system_of_ae_locallyFinite P Q μ ν
      (hGFF.aemeasurable_lqgMeasure hμ) hν hloc hνloc hR
  have hsets : ∀ A ∈ S, MeasurableSet A := fun A hA => (ho A hA).measurableSet
  have hbounded : Bornology.IsBounded (⋃ n, E n) := by
    rw [hunion]
    exact isBounded_ball
  have hpositive : ∀ᵐ ω ∂P, μ ω (⋃ n, E n) ≠ 0 ∧ μ ω (⋃ n, E n) ≠ ∞ := by
    filter_upwards [hloc, hpos] with ω hω hpω
    let : IsLocallyFiniteMeasure (μ ω) := hω
    rw [hunion]
    exact ⟨hpω ε hε.1, measure_ball_lt_top.ne⟩
  obtain ⟨f, hfm, hflim⟩ := hGFF.exists_localPairing_normalizedMass_approximations
    hμ E hEm hmono hbounded hbuffer hunion S hsets
    (fun A hA => hfrontμ.mono fun _ h => h A hA) hpositive
  exact ⟨ε, hε, S, hc, hp, hu, hsets, hg, E, hEm, hmono, hunion, hbuffer,
    hfrontν, f, hfm, hflim⟩

#print axioms IsWholePlaneGFF.exists_common_continuity_reference_approximations

end HarmonicBalls
