import HarmonicBalls.Proofs.Sec8.RootedMassApproximation

/-! # Common reference and rooted mass approximations

The imported Section 8 development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. The identity of the decoder under
the rooted law is retained as a hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A single measurable decoder for the reference and translated fields gives
common normalized mass approximations under their respective laws. -/
theorem IsWholePlaneGFF.common_rooted_normalizedMass_approximations
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ξ} (Q : Measure Ω) [IsProbabilityMeasure Q]
    {γ α₀ ε : ℝ} {hC : Ξ → (ℂ → ℝ) → ℝ} {hcirc : Ξ → ℝ → ℂ → ℝ}
    {ν : Ξ → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hν : IsLQGMeasureOfField P γ α₀ hcirc ν)
    (g : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (hm : AEMeasurable μ Q)
    (hμ : IsLQGMeasure Q γ g μ)
    (hc : ∀ᵐ ω ∂Q, ∀ n, Continuous (g ω (dyadicScale n)))
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
    (F : ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → Measure ℂ)
    (hF : ∀ n, Measurable (F n))
    (hFν : ∀ᵐ ω ∂P, ∀ n, F n (Section6.localPairingProc (ball 0 ε) hC ω) =
      normalizedRestriction (lqgApprox γ (fieldCircleAverage α₀ (hcirc ω))
        (dyadicScale n)) (E n))
    (hFμ : ∀ᵐ x ∂(Q ⊗ₘ weightedRestrictionKernel Q μ hm B hB w hw), ∀ n,
      F n (Y x) = normalizedRestriction
        (lqgApprox γ (fun r z => g x.1 r (z + x.2)) (dyadicScale n)) (E n)) :
    ∃ f : S → ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → ℝ,
      (∀ A n, Measurable (f A n)) ∧
      (∀ A, TendstoInMeasure P
        (fun n ω => f A n (Section6.localPairingProc (ball 0 ε) hC ω)) atTop
        (fun ω => (normalizedRestriction (ν ω) (ball 0 ε) A.val).toReal)) ∧
      ∀ A, TendstoInMeasure (Q ⊗ₘ weightedRestrictionKernel Q μ hm B hB w hw)
        (fun n x => f A n (Y x)) atTop
        (fun x => (normalizedRestriction
          ((μ x.1).map (fun v : ℂ => v - x.2)) (ball 0 ε) A.val).toReal) := by
  have hbdd : Bornology.IsBounded (⋃ n, E n) := by
    rw [hunion]
    exact isBounded_ball
  refine ⟨fun A n x => (F n x A.val).toReal, ?_, ?_, ?_⟩
  · intro A n
    exact ENNReal.measurable_toReal.comp
      ((Measure.measurable_coe (hsets A A.property)).comp (hF n))
  · intro A
    exact hGFF.tendstoInMeasure_normalizedMass_of_approximation hν E hmono hbdd hunion
      A.val (hsets A A.property) (hfrontν A A.property) hposν F hF hFν
  · exact tendstoInMeasure_rooted_normalizedMass_of_approximation Q g μ hm hμ hc B hB w hw
      hmass hε E hmono hunion S hsets hfrontμ Y hY F hF hFμ

#print axioms IsWholePlaneGFF.common_rooted_normalizedMass_approximations

end HarmonicBalls
