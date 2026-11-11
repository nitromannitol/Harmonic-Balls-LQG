import HarmonicBalls.FirstPass.S8c.LocalObservation
import HarmonicBalls.Proofs.Sec11.PinchRootedKernel

/-!
# Absolute continuity of the local root kernel

File `HarmonicBalls/FirstPass/Closure/LocalRootKernelAc.lean`, namespace `HarmonicBalls`.

The external Prop `LocalRootedFieldMeasureDomination` (`hL1`, `FirstPass/Frozen/S8c.lean:55`) is stated with the
root kernel `localRootKernel` (`FirstPass/S8c/LocalObservation.lean:51`), the normalized restriction `λ|B_1(0) / λ(B_1(0))`.
The helper `localRootKernel` is the weighted restriction kernel `weightedRestrictionKernel`
(`Proofs/Sec11/PinchRootedKernel.lean:28`) with unit weight, and that kernel is a measurable version of
`normalizedRestriction` (`Proofs/Sec8/LocalMeasureRatios.lean:16`, `normalizedRestriction μ U = (μ U)⁻¹ • μ.restrict U`).

`ae_weightedRestrictionKernel_eq` (`Proofs/Sec11/PinchRootedKernel.lean`) identifies the kernel almost surely with the
normalized restriction of the weighted measure, and a unit density does not change the measure. A normalized restriction
is a nonnegative scalar multiple of the restriction, hence absolutely continuous with respect to it, including when the
scalar is `0` (zero or infinite mass). So the minimal interface `localRootKernel_ac_ae` holds with no hypothesis beyond
measurability of `lam`. It is a proved lemma; it adds no Prop.
-/

open MeasureTheory Metric
open scoped ENNReal

namespace HarmonicBalls

/-- **Local root kernel is absolutely continuous with respect to the restriction to the unit ball.** For an
almost everywhere measurable LQG measure family `lam`, almost surely the normalized root kernel
`localRootKernel P lam hlam ω = λ|B_1(0) / λ(B_1(0))` is absolutely continuous with respect to `(lam ω).restrict (ball 0 1)`.
This is the domination used by the local rooted comparison of Lemma 8.2 (`LocalRootedFieldMeasureDomination`). -/
theorem localRootKernel_ac_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (lam : Ω → Measure ℂ) (hlam : AEMeasurable lam P) :
    ∀ᵐ ω ∂P, localRootKernel P lam hlam ω ≪ (lam ω).restrict (Metric.ball 0 1) := by
  filter_upwards [ae_weightedRestrictionKernel_eq P lam hlam (Metric.ball 0 1) measurableSet_ball
    (fun _ => 1) measurable_const] with ω hω
  have hk : localRootKernel P lam hlam ω =
      normalizedRestriction ((lam ω).withDensity (fun _ => 1)) (Metric.ball 0 1) := hω
  have hd : (lam ω).withDensity (fun _ => 1) = lam ω := withDensity_one
  rw [hk, hd]
  unfold normalizedRestriction
  exact Measure.smul_absolutelyContinuous

end HarmonicBalls
