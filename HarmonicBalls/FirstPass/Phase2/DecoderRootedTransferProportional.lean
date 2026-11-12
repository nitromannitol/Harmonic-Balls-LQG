import HarmonicBalls.FirstPass.Phase2.DecoderRootedTransfer
import LatticeProb.Prob.ProportionalContinuousMaps

/-!
# The rooted identity does not depend on the choice of decoder

Two Borel decoders `m`, `M` on `D = ball c₂ r₂` that both satisfy the unrooted identity (18) (each is almost surely a
positive multiple of the internal metric of the Weyl-scaled LQG metric of `h^α = h^ℂ - α log|·|`) are positively
proportional on the observation of the field, almost surely: both are positive multiples of the same function. The set of
observations where they are positively proportional is measurable
(`LatticeProb.exists_measurableSet_ofReal_proportional`, which uses that `D × D` is separable). Hence, by
`rootedIdentity_transfer_of_proportionalSet`, the rooted identity (20) for `M` gives the rooted identity (20) for `m`.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

universe u

/-- **Decoder independence of the rooted identity.** If the Borel decoders `m` and `M` on `D = ball c₂ r₂` both satisfy
the unrooted identity (18) for the field `h^α` of a whole-plane GFF model, then the rooted identity (20) for `M` implies
the rooted identity (20) for `m`, for Lebesgue-a.e. root in `U = ball c₁ r₁`. -/
theorem rootedIdentity_transfer_of_unrooted (hI1 : LocalMarkedRootingIdentityWeightedFrozen.{u})
    {γ ξ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂) (h0 : (0 : ℂ) ∉ closedBall c₂ r₂)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (m M : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) →
      ContinuousMap ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)) ℝ)
    (hm : Measurable m) (hM : Measurable M)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (h18m : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)),
      ENNReal.ofReal (m (localMeanZeroObs α (ball c₂ r₂) (hC ω)) p) =
        ENNReal.ofReal b * internalMetric
          (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal)
          (ball c₂ r₂) p.1.1 p.1.2)
    (h18M : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)),
      ENNReal.ofReal (M (localMeanZeroObs α (ball c₂ r₂) (hC ω)) p) =
        ENNReal.ofReal b * internalMetric
          (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal)
          (ball c₂ r₂) p.1.1 p.1.2)
    (h20M : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)),
        ENNReal.ofReal (M (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric
            (fun u v => (weylScaling (𝔇 (hC ω)) ξ
              (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) u v).toReal)
            (ball c₂ r₂) p.1.1 p.1.2) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)),
        ENNReal.ofReal (m (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric
            (fun u v => (weylScaling (𝔇 (hC ω)) ξ
              (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) u v).toReal)
            (ball c₂ r₂) p.1.1 p.1.2 := by
  obtain ⟨G, hG, hGprop, hGin⟩ := LatticeProb.exists_measurableSet_ofReal_proportional hm hM
  refine rootedIdentity_transfer_of_proportionalSet hI1 hγ0 hγ2 hα hr₁ hr₂ hsub h0 𝔇 m M G hG hGprop
    Ω P hC hcirc hGFF ?_ h20M
  filter_upwards [h18m, h18M] with ω hω₁ hω₂
  obtain ⟨b₁, hb₁, h₁⟩ := hω₁
  obtain ⟨b₂, hb₂, h₂⟩ := hω₂
  exact hGin _ ⟨b₁, b₂, fun p => internalMetric
      (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal)
      (ball c₂ r₂) p.1.1 p.1.2, hb₁, hb₂, fun p => ⟨h₁ p, h₂ p⟩⟩

end HarmonicBalls
