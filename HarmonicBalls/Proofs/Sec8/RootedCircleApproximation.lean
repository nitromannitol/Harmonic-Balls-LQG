import HarmonicBalls.Proofs.Sec8.RootedCircleMeasurableVersion
import HarmonicBalls.Proofs.Sec8.RootedCircleDecoderTransfer

/-! # Normalized approximations under a rooted comparison

The imported Section 8 development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. The comparison of joint rooted
observations remains an explicit hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Joint domination of the original translated circle observations supplies
one decoder for the reference and rooted normalized approximations. -/
theorem IsWholePlaneGFF.exists_rooted_normalizedLQGApprox_of_joint_domination
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ξ} {Q : Measure Ω} {γ α α₀ ε : ℝ}
    {hC : Ξ → (ℂ → ℝ) → ℝ} {hcirc : Ξ → ℝ → ℂ → ℝ}
    {gC : Ω → (ℂ → ℝ) → ℝ} {gcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (gGFF : IsWholePlaneGFF Q gC gcirc)
    (hμ : IsLQGMeasureOfField Q γ α gcirc μ) (hm : AEMeasurable μ Q)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (Y : Ω × ℂ → (Section6.LocalTest (ball 0 ε) → ℝ)) (hY : Measurable Y)
    (E : ℕ → Set ℂ) (hEm : ∀ n, MeasurableSet (E n))
    (hbuffer : ∀ n z, z ∈ E n → closedBall z (dyadicScale n) ⊆ ball 0 ε)
    (hdom : ∀ n z, z ∈ E n →
      (Q ⊗ₘ weightedRestrictionKernel Q μ hm B hB w hw).map (fun x => (Y x,
        fieldCircleAverage α (gcirc x.1) (dyadicScale n) (z + x.2) -
          fieldCircleAverage α (gcirc x.1) (dyadicScale n) x.2)) ≪
      P.map (fun ω => (Section6.localPairingProc (ball 0 ε) hC ω,
        fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z -
          fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) 0))) :
    ∃ F : ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → Measure ℂ,
      (∀ n, Measurable (F n)) ∧
      (∀ᵐ ω ∂P, ∀ n, F n (Section6.localPairingProc (ball 0 ε) hC ω) =
        normalizedRestriction (lqgApprox γ (fieldCircleAverage α₀ (hcirc ω))
          (dyadicScale n)) (E n)) ∧
      ∀ᵐ x ∂(Q ⊗ₘ weightedRestrictionKernel Q μ hm B hB w hw), ∀ n,
        F n (Y x) = normalizedRestriction
          (lqgApprox γ (fun r z => fieldCircleAverage α (gcirc x.1) r (z + x.2))
            (dyadicScale n)) (E n) := by
  let : IsProbabilityMeasure Q := gGFF.isProbabilityMeasure
  let K := weightedRestrictionKernel Q μ hm B hB w hw
  obtain ⟨g, hgm, hgeq⟩ := gGFF.exists_rooted_circle_measurable_version hμ hm B hB w hw
  have hpoint : ∀ n z, Measurable (fun x => g x (dyadicScale n) z) := by
    intro n z
    exact (hgm n).comp (measurable_id.prodMk measurable_const)
  have hcont : ∀ n, ∀ᵐ x ∂(Q ⊗ₘ K), Continuous (g x (dyadicScale n)) := by
    intro n
    filter_upwards [hgeq] with x hx
    exact hx.2.1 n
  have hdom' : ∀ n z, z ∈ E n →
      (Q ⊗ₘ K).map (fun x => (Y x, g x (dyadicScale n) z - g x (dyadicScale n) 0)) ≪
      P.map (fun ω => (Section6.localPairingProc (ball 0 ε) hC ω,
        fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z -
          fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) 0)) := by
    intro n z hz
    have heq : (Q ⊗ₘ K).map (fun x =>
        (Y x, g x (dyadicScale n) z - g x (dyadicScale n) 0)) =
        (Q ⊗ₘ K).map (fun x => (Y x,
          fieldCircleAverage α (gcirc x.1) (dyadicScale n) (z + x.2) -
            fieldCircleAverage α (gcirc x.1) (dyadicScale n) x.2)) := by
      apply Measure.map_congr
      filter_upwards [hgeq] with x hx
      simp only [hx.1 n z, hx.1 n 0, zero_add]
    rw [heq]
    exact hdom n z hz
  obtain ⟨F, hF, hFref, hFroot⟩ := hGFF.exists_dominated_normalizedLQGApprox
    (Q ⊗ₘ K) Y hY g hpoint hcont E hEm hbuffer hdom'
  refine ⟨F, hF, hFref, ?_⟩
  filter_upwards [hFroot, hgeq] with x hx heq n
  rw [hx n]
  congr 1
  unfold lqgApprox
  congr 1
  funext z
  rw [heq.1 n z]

end HarmonicBalls
