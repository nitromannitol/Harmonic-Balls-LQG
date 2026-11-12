import HarmonicBalls.Proofs.GFF.DistMetricPairingAddFun

/-! # The distribution reconstructed from an affinely pulled back pairing functional

For a distribution `T`, a scale `r > 0`, a point `z` and a constant `c`, the pairing functional of
`T(r · + z) + c` built from the canonical extension of `T` to non-test functions reconstructs to the
distribution `T(r · + z) + c`: the normalization `(h(r · + z), φ) = r⁻² (h, φ((· - z)/r))` of
`affinePullbackPairing` agrees with `LQGMetric.affineComp`, and the constant is `LQGMetric.addConst`. -/

noncomputable section
open MeasureTheory
namespace HarmonicBalls

/-- The affine pullback pairing of the extension of a distribution `T` pairs like the distribution
`T(r · + z)` with every test function. -/
theorem affinePullbackPairing_distributionPairingExtension_test (T : LQGMetric.DistC) {r : ℝ}
    (hr : 0 < r) (z : ℂ) (φ : LQGMetric.TestC) :
    affinePullbackPairing (distributionPairingExtension T) r z φ = LQGMetric.affineComp r z T φ := by
  have hfun : (fun y => (φ : ℂ → ℝ) ((y - z) / r)) = ⇑(LQGMetric.testAffinePull r z φ) := by
    funext y
    rw [LQGMetric.testAffinePull_apply r z hr.ne']
  rw [affinePullbackPairing, hfun, distributionPairingExtension_test]
  rfl

/-- Coordinate change for the distribution reconstructed from pairings: reading `T(r · + z) + c` through
`pairingDistribution` of the affine pullback pairing of the extension of `T` gives the distribution
`T(r · + z) + c`. -/
theorem pairingDistribution_addFunPairing_affinePullbackPairing {r : ℝ} (hr : 0 < r) (z : ℂ)
    (T : LQGMetric.DistC) (c : ℝ) :
    pairingDistribution
        (addFunPairing (affinePullbackPairing (distributionPairingExtension T) r z) (fun _ => c)) =
      LQGMetric.addConst (LQGMetric.affineComp r z T) c :=
  pairingDistribution_addFunPairing_of_eq _ (LQGMetric.affineComp r z T)
    (affinePullbackPairing_distributionPairingExtension_test T hr z) (ContinuousMap.const ℂ c)

end HarmonicBalls
