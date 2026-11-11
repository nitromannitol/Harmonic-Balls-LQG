import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.S11r.Frozen
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import HarmonicBalls.LPStage.LocalMeasureKernel5

/-!
# LP-stage bridge for the local measure kernel (rows 51 and 15, z4)

`HarmonicBalls.localMeasureKernelStmt_of_lpStage` is the HB statement `LocalMeasureKernelStmt`
(`FirstPass/S11r/Frozen.lean:144`, row 51), with the binders of `localMeasureKernelStmt_derived` (`γ c₁ c₂ r₁ r₂`).
`HarmonicBalls.localLQGDecoderCommonFrozen_of_lpStage` is the HB statement `LocalLQGDecoderCommonFrozen`
(`FirstPass/Frozen/S11c.lean:388`, row 15), binder-free. Both are obtained from the unconditional LP statements
`localMeasureKernelStmt_lp` and `localLQGDecoderCommonFrozen_lp` (`LPStage/LocalMeasureKernel5.lean`) through the bridge
equivalences `isWholePlaneGFF_iff` (M1), `isLQGMeasureOfField_iff` and `isLQGMeasure_iff` (M4). The HB and LP definitions of
the observables (`localMeanZeroObs`, `campbellReferenceObs`, `rootedCircleAverage`, `rootedMeanZeroObs`, `addCircleAverage`)
have the same bodies, so they agree by unfolding.
-/

namespace HarmonicBalls

open MeasureTheory
open LPBridge

universe u

/-- `LocalMeasureKernelStmt` (row 51) from the LP stage, with the binders of `localMeasureKernelStmt_derived`. -/
theorem localMeasureKernelStmt_of_lpStage (γ : ℝ) (c₁ c₂ : ℂ) (r₁ r₂ : ℝ) :
    LocalMeasureKernelStmt γ c₁ c₂ r₁ r₂ := by
  intro hγ0 hγ2 hr1 hr2 hsub1 hsub2 h0
  obtain ⟨κ, hκ, h1, h2⟩ := LatticeProb.LocalMeasureKernel.LocalDecoderCommon.localMeasureKernelStmt_lp γ c₁ c₂ r₁ r₂
    hγ0 hγ2 hr1 hr2 hsub1 hsub2 h0
  refine ⟨κ, hκ, ?_, ?_⟩
  · intro α hα Ω _ P _ hC hcirc μ hW hμ
    filter_upwards [h1 α hα Ω P hC hcirc μ ((isWholePlaneGFF_iff P hC hcirc).1 hW)
      ((isLQGMeasureOfField_iff P γ α hcirc μ).1 hμ)] with ω hω
    exact hω
  · intro α hα Ω _ P _ hC hcirc hW
    filter_upwards [h2 α hα Ω P hC hcirc ((isWholePlaneGFF_iff P hC hcirc).1 hW)] with z hz μz hμz
    exact hz μz ((isLQGMeasure_iff P γ _ μz).1 hμz)

/-- `LocalLQGDecoderCommonFrozen` (row 15) from the LP stage, binder-free. -/
theorem localLQGDecoderCommonFrozen_of_lpStage : LocalLQGDecoderCommonFrozen.{u} := by
  intro γ hγ0 hγ2 c₂ r₂ hr₂ h0
  obtain ⟨K, hK, h1, h2⟩ :=
    LatticeProb.LocalMeasureKernel.LocalDecoderCommon.localLQGDecoderCommonFrozen_lp γ hγ0 hγ2 c₂ r₂ hr₂ h0
  refine ⟨K, hK, ?_, ?_⟩
  · intro α₀ hα₀ Ω _ P _ hC hcirc μ hW hμ
    exact h1 α₀ hα₀ Ω P hC hcirc μ ((isWholePlaneGFF_iff P hC hcirc).1 hW)
      ((isLQGMeasureOfField_iff P γ α₀ hcirc μ).1 hμ)
  · intro α₀ hα₀ z Ω _ P _ hC hcirc μz hW hμz
    exact h2 α₀ hα₀ z Ω P hC hcirc μz ((isWholePlaneGFF_iff P hC hcirc).1 hW)
      ((isLQGMeasure_iff P γ _ μz).1 hμz)

end HarmonicBalls
