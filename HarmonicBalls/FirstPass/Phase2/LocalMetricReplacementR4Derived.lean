import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementGlue
import HarmonicBalls.FirstPass.Phase2.LocalMetricReplacementRootedReduction
import HarmonicBalls.FirstPass.Phase2.DecoderRootedTransferProportional
import HarmonicBalls.FirstPass.LPBridge.MarkedRootingIdentity
import HarmonicBalls.FirstPass.Phase2.RootedInsertionContinuityDerived
import HarmonicBalls.FirstPass.Phase2.LengthUnivDerived
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived

/-!
# The local metric replacement statement, derived

`localMetricReplacementStmt_derived`: `LocalMetricReplacementStmt γ ξ c₁ c₂ r₁ r₂` holds with no hypothesis. By
`localMetricReplacementStmt_of_rootedTransfer` it suffices to show that every Borel decoder `m` of `D = B(c₂, r₂)` that
satisfies the unrooted identity (18) satisfies the rooted identity (20). Fix the normalizing decoder `(ρ, M)` of `D`
and the decoders `(ρ_i, M_i)` of the rational disks. Almost surely the unrooted observation lies in the measurable
event `A` of the rational cover (step 5); hence, for almost every root, so does the rooted observation (step 6); there
the decoder `M` agrees near every point away from the root with a constant multiple of the rooted internal metric
(step 7), and the dense gluing lemma gives the agreement on all of `D × D` (step 10;
`RootedLocalCover.ae_rooted_clause_of_decoders`). Decoder independence
(`rootedIdentity_transfer_of_unrooted`) passes from `M` to `m`.

Terminology: internal metric (Armstrong-Kuusi-Mourrat); LQG metric, quantum-typical root (Duplantier-Sheffield,
Gwynne-Miller).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric

universe u

/-- **The local metric replacement statement, derived.** -/
theorem localMetricReplacementStmt_derived (γ ξ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) :
    LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂ := by
  refine localMetricReplacementStmt_of_rootedTransfer ?_
  intro hγ0 hγ2 hr₁ hr₂ hsub hDU h0 𝔇 h𝔇 m hm h18m α hα Ω _ P _ hC hcirc hGFF
  obtain ⟨ρ, M, hρ, h1, hMm, hid⟩ :=
    localLQGMetricNormalizedMeasurableFixedMetric_derived.{u} γ ξ c₂ r₂ hγ0 hγ2 hr₂ h0 𝔇 h𝔇
  obtain ⟨ρV, MV, hdec⟩ := RootedLocalCover.exists_diskDecoders.{u} hγ0 hγ2 h𝔇
    (D := ball c₂ r₂) (fun h => h0 (ball_subset_closedBall h))
  have hFA : ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α hC hcirc :=
    fun α _ Ω _ P _ hC hcirc => lqgMetricFieldAxioms_forall_derived γ ξ α Ω P hC hcirc
  have hCM := DerivedInputs9.cameronMartinGFFMutualAbsCont_derived.{u}
  have hPhi := lqgInternalMetricWeylAeMeasurableFrozen_derived.{u}
  have h20M := RootedLocalCover.ae_rooted_clause_of_decoders (α := α) LPBridge.localMarkedRootingIdentityWeighted_of_lp
    hCM hPhi hFA lqgMetricLengthUniv_derived rootedPhysicalMetricContinuousAtInsertion_derived
    (fun Ω _ P hC hcirc => lqgMeasureExistence_derived P γ α hC hcirc) hγ0 hγ2 hα hr₁ hr₂ hsub hDU h0 h𝔇 hρ h1
    hMm hid (fun i => (hdec i).1) (fun i => (hdec i).2.1) (fun i => (hdec i).2.2.1)
    (fun i => (hdec i).2.2.2) Ω P hC hcirc hGFF
  have h18M : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)),
      ENNReal.ofReal (M (localMeanZeroObs α (ball c₂ r₂) (hC ω)) p) =
        ENNReal.ofReal b * internalMetric
          (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal)
          (ball c₂ r₂) p.1.1 p.1.2 := (unrooted_identity_fixedMetric_explicit hCM hPhi hFA hγ0 hγ2 hr₂ h0 h𝔇 hρ hMm hid α hα Ω P hC
    hcirc hGFF).mono fun ω h => ⟨Real.exp (-ξ * fieldPairing α (hC ω) ρ), Real.exp_pos _, h⟩
  exact rootedIdentity_transfer_of_unrooted LPBridge.localMarkedRootingIdentityWeighted_of_lp hγ0 hγ2 hα hr₁ hr₂ hsub h0 𝔇
    m M hm hMm Ω P hC hcirc hGFF (h18m α hα Ω P hC hcirc hGFF) h18M h20M

/-- **The input `hN2` of the counted theorems, derived.** -/
theorem localMetricReplacementFrozen_derived : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
    LocalMetricReplacementFrozen.{u} γ ξ c₁ c₂ r₁ r₂ :=
  fun γ ξ _ _ _ c₁ c₂ r₁ r₂ => localMetricReplacementStmt_derived.{u} γ ξ c₁ c₂ r₁ r₂

end HarmonicBalls
