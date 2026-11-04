import HarmonicBalls.Proofs.Sec8.MeanZeroTestEquivalence
import HarmonicBalls.Proofs.Sec11.PinchUnnormalizedKernel
import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw
import Mathlib.Probability.Kernel.Composition.Prod

/-! # Measurability of the unnormalized rooted pairing kernel

A measurable field observation and an almost-everywhere measurable random
measure produce a jointly observed unnormalized root kernel, provided the
restricted mass is almost surely finite. The LQG unit-disk case follows from
local finiteness. No rooted change-of-measure formula is assumed. The imported
Section 6 development uses Leonardo Bonanno's whole-plane GFF formalization.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

/-- An observed field paired with an unnormalized restricted root has an
almost-everywhere measurable measure-valued kernel. -/
theorem aemeasurable_observed_restricted_root_kernel
    {Ω F : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    (P : Measure Ω) (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (X : Ω → F) (hX : Measurable X) (B : Set ℂ) (hB : MeasurableSet B)
    (hfin : ∀ᵐ ω ∂P, μ ω B ≠ ∞) :
    AEMeasurable (fun ω => ((μ ω).restrict B).map (fun z => (X ω, z))) P := by
  let κ := unnormalizedWeightedRestrictionKernel P μ hμ B hB (fun _ => 1) measurable_const
  let K := (Kernel.deterministic X hX) ×ₖ κ
  have hfin' : ∀ᵐ ω ∂P, ((μ ω).withDensity (fun _ => 1)) B ≠ ∞ := by
    simpa only [withDensity_const, one_smul] using hfin
  have heq : ∀ᵐ ω ∂P, κ ω = (μ ω).restrict B := by
    simpa only [withDensity_const, one_smul] using
      ae_unnormalizedWeightedRestrictionKernel_eq P μ hμ B hB
        (fun _ => 1) measurable_const hfin'
  apply K.aemeasurable.congr
  filter_upwards [heq] with ω hω
  apply Measure.ext
  intro s hs
  rw [Kernel.deterministic_prod_apply' hX κ ω hs, Measure.map_apply measurable_prodMk_left hs]
  rw [hω]

/-- For the whole-plane GFF, the unnormalized unit-disk rooted law in raw
mean-zero pairing coordinates has an almost-everywhere measurable kernel. -/
theorem IsWholePlaneGFF.aemeasurable_raw_rooted_unitBall_kernel
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ) :
    AEMeasurable (fun ω => ((μ ω).restrict (ball 0 1)).map
      (fun z => ((fun φ : RawMeanZeroTest => hC ω φ.1), z))) P := by
  have hfc : (fun ω => fieldCircleAverage 0 (hcirc ω)) = hcirc := by
    funext ω r z
    simp [fieldCircleAverage]
  have hμ' : IsLQGMeasureOfField P γ 0 hcirc μ := by
    simpa only [IsLQGMeasureOfField, hfc] using hμ
  have hmeas : AEMeasurable μ P := hh.aemeasurable_lqgMeasure hμ'
  have hfield : Measurable (fun ω => fun φ : RawMeanZeroTest => hC ω φ.1) := by
    apply measurable_pi_iff.mpr
    intro φ
    exact hh.measurable_pairing φ.1 φ.2.1
  have hfin : ∀ᵐ ω ∂P, μ ω (ball 0 1) ≠ ∞ := by
    filter_upwards [hμ] with ω hω
    let : IsLocallyFiniteMeasure (μ ω) := hω.isLocallyFiniteMeasure
    exact measure_ball_ne_top
  exact aemeasurable_observed_restricted_root_kernel P μ hmeas _ hfield _ measurableSet_ball hfin

#print axioms aemeasurable_observed_restricted_root_kernel
#print axioms IsWholePlaneGFF.aemeasurable_raw_rooted_unitBall_kernel

end HarmonicBalls
