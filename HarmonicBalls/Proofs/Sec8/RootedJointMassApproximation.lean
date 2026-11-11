import HarmonicBalls.Proofs.Sec8.RootedCommonMassApproximation
import HarmonicBalls.Proofs.Sec8.RootedCircleApproximation

/-! # Shared rooted normalized mass approximations

The imported Section 8 development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. Joint domination is an explicit
hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Joint domination of centered circle observations yields common mass
approximations for the reference field and its rooted translation. -/
theorem IsWholePlaneGFF.common_rooted_normalizedMass_of_joint_domination
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ξ} {Q : Measure Ω} {γ α α₀ ε : ℝ}
    {hC : Ξ → (ℂ → ℝ) → ℝ} {hcirc : Ξ → ℝ → ℂ → ℝ}
    {gC : Ω → (ℂ → ℝ) → ℝ} {gcirc : Ω → ℝ → ℂ → ℝ}
    {ν : Ξ → Measure ℂ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (gGFF : IsWholePlaneGFF Q gC gcirc)
    (hν : IsLQGMeasureOfField P γ α₀ hcirc ν)
    (hμ : IsLQGMeasureOfField Q γ α gcirc μ) (hm : AEMeasurable μ Q)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hmass : ∀ᵐ ω ∂Q, ((μ ω).withDensity w) B ≠ 0 ∧
      ((μ ω).withDensity w) B ≠ ∞)
    (hε : 0 < ε) (E : ℕ → Set ℂ) (hmono : Monotone E)
    (hunion : (⋃ n, E n) = ball 0 ε)
    (S : Set (Set ℂ)) (hsets : ∀ A ∈ S, MeasurableSet A)
    (hfrontν : ∀ A ∈ S, ∀ᵐ ω ∂P, (∀ n, ν ω (frontier (E n)) = 0 ∧
        ν ω (frontier (A ∩ E n)) = 0) ∧
      ν ω (frontier (⋃ n, E n)) = 0 ∧ ν ω (frontier (A ∩ ⋃ n, E n)) = 0)
    (hposν : ∀ᵐ ω ∂P, ν ω (⋃ n, E n) ≠ 0 ∧ ν ω (⋃ n, E n) ≠ ∞)
    (hfrontμ : ∀ A ∈ S, ∀ᵐ x ∂(Q ⊗ₘ weightedRestrictionKernel Q μ hm B hB w hw),
      let ρ := (μ x.1).map (fun v : ℂ => v - x.2)
      (∀ n, ρ (frontier (E n)) = 0 ∧ ρ (frontier (A ∩ E n)) = 0) ∧
        ρ (frontier (⋃ n, E n)) = 0 ∧ ρ (frontier (A ∩ ⋃ n, E n)) = 0)
    (Y : Ω × ℂ → (Section6.LocalTest (ball 0 ε) → ℝ)) (hY : Measurable Y)
    (hEm : ∀ n, MeasurableSet (E n))
    (hbuffer : ∀ n z, z ∈ E n → closedBall z (dyadicScale n) ⊆ ball 0 ε)
    (hdom : ∀ n z, z ∈ E n →
      (Q ⊗ₘ weightedRestrictionKernel Q μ hm B hB w hw).map (fun x => (Y x,
        fieldCircleAverage α (gcirc x.1) (dyadicScale n) (z + x.2) -
          fieldCircleAverage α (gcirc x.1) (dyadicScale n) x.2)) ≪
      P.map (fun ω => (Section6.localPairingProc (ball 0 ε) hC ω,
        fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z -
          fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) 0))) :
    ∃ f : S → ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → ℝ,
      (∀ A n, Measurable (f A n)) ∧
      (∀ A, TendstoInMeasure P
        (fun n ω => f A n (Section6.localPairingProc (ball 0 ε) hC ω)) atTop
        (fun ω => (normalizedRestriction (ν ω) (ball 0 ε) A.val).toReal)) ∧
      ∀ A, TendstoInMeasure (Q ⊗ₘ weightedRestrictionKernel Q μ hm B hB w hw)
        (fun n x => f A n (Y x)) atTop
        (fun x => (normalizedRestriction
          ((μ x.1).map (fun v : ℂ => v - x.2)) (ball 0 ε) A.val).toReal) := by
  let : IsProbabilityMeasure Q := gGFF.isProbabilityMeasure
  have hc : ∀ᵐ ω ∂Q, ∀ n,
      Continuous (fieldCircleAverage α (gcirc ω) (dyadicScale n)) :=
    ae_all_iff.mpr fun n => gGFF.ae_continuous_fieldCircleAverage α (dyadicScale_pos n)
  obtain ⟨F, hF, hFν, hFμ⟩ :=
    hGFF.exists_rooted_normalizedLQGApprox_of_joint_domination gGFF hμ hm
      B hB w hw Y hY E hEm hbuffer hdom
  exact hGFF.common_rooted_normalizedMass_approximations Q hν
    (fun ω => fieldCircleAverage α (gcirc ω)) μ hm hμ hc B hB w hw hmass
    hε E hmono hunion S hsets hfrontν hposν hfrontμ Y hY F hF hFν hFμ

end HarmonicBalls
