import HarmonicBalls.FirstPass.S11r.RootedJoint
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived

/-!
# Transfer of the rooted identity between decoders

Let `D = ball c₂ r₂` and `U = ball c₁ r₁` with `closedBall c₁ r₁ ⊆ D` and `0 ∉ closedBall c₂ r₂`. A decoder is a Borel map
`m` from the mean-zero local observations of the field on `D` to continuous functions on `D × D`. The rooted identity
(clause (20) of `LocalMetricReplacementStmt`) for a decoder `M` says that, for Lebesgue-a.e. root `z ∈ U`, almost surely
`M` applied to the rooted reference observation `campbellReferenceObs γ α D h z` is a positive multiple of the internal
metric on `D` of the Weyl scaling of `𝔇_h` by the logarithmic singularities at `0` and at `z`.

`rootedIdentity_transfer_of_proportionalSet`: if a measurable set `G` of observations carries a positive proportionality
`m = b M` (on positive parts) and contains the observation of the field `h^α = h^ℂ - α log|·|` almost surely, then the
rooted identity for `M` gives the rooted identity for `m`. The rooted reference observation lies in `G` almost surely for
Lebesgue-a.e. root, by the rooted null transfer `ae_root_rootedObs_eq_zero_of_obs_null_noMeas` (the rooted measure of
the LQG measure `μ_h`, Duplantier-Sheffield and Berestycki-Powell), applied to the complement of `G`; the LQG measure of
the field exists by `lqgMeasureExistence_derived`.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

universe u

/-- **Rooted transfer along a proportionality set.** Let `G` be a measurable set of mean-zero local observations on
`D = ball c₂ r₂` on which the decoders `m` and `M` are positively proportional (`ofReal ∘ m o = b • ofReal ∘ M o`,
`b > 0`), and suppose that the observation `localMeanZeroObs α D h` of the field lies in `G` almost surely. Then the
rooted identity (20) for `M` implies the rooted identity (20) for `m`, for Lebesgue-a.e. root in `U = ball c₁ r₁`. The
input `hI1` is the rooting identity for the LQG measure used by the rooted null transfer. -/
theorem rootedIdentity_transfer_of_proportionalSet (hI1 : LocalMarkedRootingIdentityWeightedFrozen.{u})
    {γ ξ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂) (h0 : (0 : ℂ) ∉ closedBall c₂ r₂)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (m M : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) →
      ContinuousMap ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)) ℝ)
    (G : Set ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)) (hG : MeasurableSet G)
    (hGprop : ∀ o ∈ G, ∃ b : ℝ, 0 < b ∧
      ∀ p, ENNReal.ofReal (m o p) = ENNReal.ofReal b * ENNReal.ofReal (M o p))
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hobs : ∀ᵐ ω ∂P, localMeanZeroObs α (ball c₂ r₂) (hC ω) ∈ G)
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
  obtain ⟨μ, hμ⟩ := lqgMeasureExistence_derived P γ α hC hcirc hGFF hγ0 hγ2 hα
  have hnull : ∀ᵐ ω ∂P, (fun φ => fieldPairing α (hC ω) φ.1) ∉ Gᶜ := by
    filter_upwards [hobs] with ω hω
    exact fun h => h hω
  have hR1 := ae_root_rootedObs_eq_zero_of_obs_null_noMeas hI1 hγ0 hγ2 hα Ω P hC hcirc μ hGFF hμ hr₁ hr₂ hsub h0
    Gᶜ hG.compl hnull
  filter_upwards [hR1, h20M] with z hz hzM
  have hmeas : Measurable (fun ω => (univ ×ˢ Gᶜ).indicator (fun _ => (1 : ℝ≥0∞))
      (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z)) :=
    (measurable_const.indicator (MeasurableSet.univ.prod hG.compl)).comp
      ((measurable_campbellReferenceObs_joint P hC hcirc hGFF γ α (ball c₂ r₂)).comp measurable_prodMk_left)
  have hae := (lintegral_eq_zero_iff hmeas).1 hz
  filter_upwards [hae, hzM] with ω hω hωM
  have hmem : (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2 ∈ G := by
    by_contra hn
    have hin : campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z ∈ (univ ×ˢ Gᶜ : Set _) := ⟨mem_univ _, hn⟩
    have h1 := hω
    simp only [Pi.zero_apply, Set.indicator_of_mem hin] at h1
    exact one_ne_zero h1
  obtain ⟨b, hb, hbp⟩ := hGprop _ hmem
  obtain ⟨b', hb', hb'p⟩ := hωM
  refine ⟨b * b', mul_pos hb hb', fun p => ?_⟩
  rw [hbp p, hb'p p, ENNReal.ofReal_mul hb.le, mul_assoc]

end HarmonicBalls
