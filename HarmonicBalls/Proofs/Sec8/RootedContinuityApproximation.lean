import HarmonicBalls.Proofs.Sec8.RootedSamplingBallMass

/-! # Reference approximations on rooted continuity sets

The imported Section 8 development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. The rooted convergence of the
approximations remains a separate condition. -/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A reference LQG measure and a recentered normalized weighted root have
common continuity sets and reference-side normalized mass approximations.
The recentered root has positive finite mass in the chosen ball almost surely. -/
theorem IsWholePlaneGFF.exists_rooted_continuity_reference_approximations
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ξ} (Q : Measure Ω) [IsProbabilityMeasure Q] {γ α₀ R : ℝ}
    {hC : Ξ → (ℂ → ℝ) → ℝ} {hcirc : Ξ → ℝ → ℂ → ℝ}
    {ν : Ξ → Measure ℂ} (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ Q)
    (hloc : ∀ᵐ ω ∂Q, IsLocallyFiniteMeasure (μ ω))
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hmass : ∀ᵐ ω ∂Q, ((μ ω).withDensity w) B ≠ 0 ∧
      ((μ ω).withDensity w) B ≠ ∞)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hν : IsLQGMeasureOfField P γ α₀ hcirc ν)
    (hR : 0 < R)
    (hpos : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ν ω (ball (0 : ℂ) r) ≠ 0) :
    ∃ ε ∈ Ioo (0 : ℝ) R, ∃ S : Set (Set ℂ), S.Countable ∧ IsPiSystem S ∧
      univ ∈ S ∧ (∀ A ∈ S, MeasurableSet A) ∧
      (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S ∧
      ∃ E : ℕ → Set ℂ, (∀ n, MeasurableSet (E n)) ∧ Monotone E ∧
        (⋃ n, E n) = ball 0 ε ∧
        (∀ n z, z ∈ E n → closedBall z (dyadicScale n) ⊆ ball 0 ε) ∧
        (∀ᵐ x ∂(Q ⊗ₘ weightedRestrictionKernel Q μ hμ B hB w hw),
          let νroot := (μ x.1).map (fun v : ℂ => v - x.2)
          νroot (ball 0 ε) ≠ 0 ∧ νroot (ball 0 ε) ≠ ∞ ∧
          ∀ A ∈ S, (∀ n, νroot (frontier (E n)) = 0 ∧
            νroot (frontier (A ∩ E n)) = 0) ∧ νroot (frontier (⋃ n, E n)) = 0 ∧
            νroot (frontier (A ∩ ⋃ n, E n)) = 0) ∧
        ∃ f : S → ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → ℝ,
          (∀ A n, Measurable (f A n)) ∧ ∀ A,
            TendstoInMeasure P (fun n ω => f A n (Section6.localPairingProc (ball 0 ε) hC ω))
              atTop (fun ω => (normalizedRestriction (ν ω) (ball 0 ε) A.val).toReal) := by
  let K := weightedRestrictionKernel Q μ hμ B hB w hw
  let : IsProbabilityMeasure (Q ⊗ₘ K) :=
    isProbabilityMeasure_weightedRestriction_compProd Q μ hμ B hB w hw hmass
  have hroot := aemeasurable_recentered_of_weightedRestriction_compProd Q μ hμ hloc B hB w hw
  obtain ⟨ε, hε, S, hc, hp, hu, hs, hg, E, he, hm, hunion, hb, hfront, f, hf, hlim⟩ :=
    hGFF.exists_common_continuity_reference_approximations (Q ⊗ₘ K)
      (fun x : Ω × ℂ => (μ x.1).map (fun v : ℂ => v - x.2)) hν hroot.1 hroot.2 hR hpos
  refine ⟨ε, hε, S, hc, hp, hu, hs, hg, E, he, hm, hunion, hb, ?_, f, hf, hlim⟩
  filter_upwards [hfront,
    ae_recentered_ball_mass_weightedRestriction_compProd Q μ hμ hloc B hB w hw hε.1] with x hx hm
  exact ⟨hm.1, hm.2, hx⟩

#print axioms IsWholePlaneGFF.exists_rooted_continuity_reference_approximations

end HarmonicBalls
