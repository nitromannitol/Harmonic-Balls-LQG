import Mathlib
import HarmonicBalls.FirstPass.S8c.WeylOffOrigin

/-!
# Absolute continuity of the insertion LQG measure on the unit ball (Step 8)

Source: Step 8 of Lemma 11.13 of Bou-Rabee and Gwynne, arXiv:2208.11795).

For a whole-plane GFF `P` with `0 < γ < 2` and `α₀ < Q(γ)`, let `μ0` be the LQG measure with no insertion (`IsLQGMeasureOfField P γ 0`)
and `μα` the LQG measure with insertion `α₀`. Then almost surely `μα ω|_{B(0,1)} ≪ μ0 ω|_{B(0,1)}`, and a `μ0`-a.e. property on
`B(0,1)` transfers to `μα`-a.e. on `B(0,1)`.

The only non-elementary input is the FROZEN Weyl relation `LocalLQGInsertionWeylOffOrigin` (`FirstPass/Frozen/S8c.lean`), used as is.
No new hypothesis and no new Prop are introduced.

`localRoot_weyl_ae` (`FirstPass/S8c/WeylOffOrigin.lean:64`) cannot be applied literally: its signature takes the full non-atomicity
`LQGMeasureNonatomic` (Proposed/LQG.lean:77, pending source-check), but its proof reads only `μ {0} = 0`. The proof below repeats
its body (`absCont_restrict_of_density_off_origin`, WeylOffOrigin.lean:48, with density `|z|^{γα₀}`) with the atom-at-0 hypothesis
`hNonα`, so the Proposed input is not needed. The binder `hNon0` is kept as `_hNon0`; the proof does not use it.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls.FirstPassS11iAnnularWeylAbsCont

universe u

/-- **Absolute continuity of the insertion measure on the unit ball (Step 8).** For a whole-plane GFF `P`,
`0 < γ < 2`, `α₀ < Q(γ)`, the LQG measure `μ0` with no insertion and the LQG measure `μα` with insertion `α₀`, almost surely
`(μα ω).restrict (B(0,1)) ≪ (μ0 ω).restrict (B(0,1))`.

Hypotheses: the frozen Weyl relation `hWeyl` (`Frozen/S8c.lean:73`), the binders of the statement, and the range `0 < γ`, `γ < 2`, `α₀ < lqgQ γ`.
The atom-at-zero hypotheses are `_hNon0` (unused) and `hNonα`. -/
theorem insertedMeasure_ac_zeroInsertion_on_unitBall (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ0 μα : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ0 : IsLQGMeasureOfField P γ 0 hcirc μ0)
    (hμα : IsLQGMeasureOfField P γ α₀ hcirc μα)
    (_hNon0 : ∀ᵐ ω ∂P, μ0 ω {0} = 0)
    (hNonα : ∀ᵐ ω ∂P, μα ω {0} = 0) :
    ∀ᵐ ω ∂P, (μα ω).restrict (ball (0 : ℂ) 1) ≪ (μ0 ω).restrict (ball (0 : ℂ) 1) := by
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  filter_upwards [hWeyl Ω P γ α₀ hC hcirc μα μ0 hGFF hγ0 hγ2 hα hμα hμ0, hNonα] with ω hω hNω
  refine absCont_restrict_of_density_off_origin (μα ω) (μ0 ω)
    (f := fun z : ℂ => ENNReal.ofReal (‖z‖ ^ (γ * α₀))) ?_ ?_ hω hNω measurableSet_ball
  · exact ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)
  · intro z hz
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) _)

/-- **Null-set transfer on the unit ball (Step 8).** Almost surely, a property holding `μ0`-almost
everywhere on `B(0,1)` holds `μα`-almost everywhere on `B(0,1)`. This is `AbsolutelyContinuous.ae_le` applied to
`insertedMeasure_ac_zeroInsertion_on_unitBall`. The whole-plane version under full non-atomicity is
`HarmonicBalls.FirstPassS11iStep8Transfer.ae_ae_of_ae_ae_noInsertion_of_nonatomic` (S11i/Step8TransferWeyl.lean:66); this corollary
needs only the atom at `0`. -/
theorem ae_ae_ball_of_ae_ae_insertedMeasure (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ0 μα : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ0 : IsLQGMeasureOfField P γ 0 hcirc μ0)
    (hμα : IsLQGMeasureOfField P γ α₀ hcirc μα)
    (_hNon0 : ∀ᵐ ω ∂P, μ0 ω {0} = 0)
    (hNonα : ∀ᵐ ω ∂P, μα ω {0} = 0)
    (p : Ω → ℂ → Prop)
    (hp : ∀ᵐ ω ∂P, ∀ᵐ z ∂((μ0 ω).restrict (ball (0 : ℂ) 1)), p ω z) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂((μα ω).restrict (ball (0 : ℂ) 1)), p ω z := by
  filter_upwards [insertedMeasure_ac_zeroInsertion_on_unitBall hWeyl P γ α₀ hC hcirc μ0 μα hGFF hγ0 hγ2 hα hμ0 hμα
    _hNon0 hNonα, hp] with ω hac hpω
  exact hac.ae_le hpω

end HarmonicBalls.FirstPassS11iAnnularWeylAbsCont
