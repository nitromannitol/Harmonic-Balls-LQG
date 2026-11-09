import HarmonicBalls.Proofs.Potential.GreenPotentialLInfinityFunctional
import HarmonicBalls.Proofs.Potential.GreenRowL1Continuous

/-!
# Operator-norm continuity of the Green functional of a pole on `L∞`

For a bounded open planar set `U` and a pole `x : ℂ`, `greenPotentialLInfinityFunctional hU hUb x` is the
continuous real-linear functional `Φ_x : f ↦ ∫ y, G_U(x, y) * f y` on `Lp ℝ ∞ volume`. Here `G_U` is the Green
function of Armitage–Gardiner (value `0` off `U`, as in `Defs/Green.lean`), and the integral is computed on a
representative of the `L∞` class `f` (`GreenPotentialLInfinityFunctional.lean`). This file proves the dependence
of `Φ_x` on the pole, in the operator norm of `Lp ℝ ∞ volume →L[ℝ] ℝ`:

* (norm estimate) `‖Φ_x - Φ_z‖ ≤ ∫ y, |G_U(x, y) - G_U(z, y)|` for all poles `x z : ℂ`
  (`norm_greenPotentialLInfinityFunctional_sub_le`);
* (distance estimate) `dist Φ_x Φ_z ≤ dist (greenRowL1 x) (greenRowL1 z)`, the `L¹` distance of the Green rows
  (`dist_greenPotentialLInfinityFunctional_le`); by `dist_greenRowL1` the right-hand side is the same integral;
* (continuity) `x ↦ Φ_x` is continuous on `U` for the operator norm
  (`continuousOn_greenPotentialLInfinityFunctional`);
* (uniform continuity) `x ↦ Φ_x` is uniformly continuous for the operator norm on every compact `K ⊆ U`
  (`uniformContinuousOn_greenPotentialLInfinityFunctional`).

Proof outline. Fix `f`, and let `g(y) = G_U(x, y) - G_U(z, y)`. Both Green rows are integrable on `ℂ`, so
`Φ_x f - Φ_z f = ∫ g(y) f(y) dy`. Then `|∫ g f| ≤ ∫ |g| |f|`, and `|f| ≤ ‖f‖` almost everywhere
(`abs_coeFn_le_norm_ae_top`) gives `|Φ_x f - Φ_z f| ≤ (∫ |g|) ‖f‖`. The pole continuity is the continuity of the
`L¹` Green row `x ↦ G_U(x, ·)` on `U` (`GreenRowL1Continuous`, from the small-disc and off-disc argument of
`GreenPoleL1Continuity`), transferred through the norm estimate.

The functional keeps its literal definition. No operator is assumed, the Green integral is not replaced by an
abstract kernel operator, and no norm estimate, pole continuity or representative choice is a hypothesis. Only
`IsOpen U` and `Bornology.IsBounded U` are assumed. No boundary regularity, no singular-source representative,
no general-domain reciprocity and no literature input enter.

The local volume estimate and the potential-theoretic infrastructure reached through the import closure use work
of Leonardo Bonanno, through the pinned Lattice-Probability (lean-v4.35) port.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Real Metric

/-- Operator-norm estimate for a difference of two Green functionals of poles on `L∞`: for a bounded open `U`
and poles `x z : ℂ`, `‖Φ_x - Φ_z‖ ≤ ∫ y, |G_U(x, y) - G_U(z, y)|`, where `Φ_w` is
`greenPotentialLInfinityFunctional hU hUb w`. The integrand is bounded by `|G_U(x, y) - G_U(z, y)| * ‖f‖`,
using `|f| ≤ ‖f‖` almost everywhere. -/
theorem norm_greenPotentialLInfinityFunctional_sub_le {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (x z : ℂ) :
    ‖greenPotentialLInfinityFunctional hU hUb x - greenPotentialLInfinityFunctional hU hUb z‖ ≤
      ∫ y, |greenFunction U x y - greenFunction U z y| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun y => abs_nonneg _) (fun f => ?_)
  have hx := integrable_greenFunction_mul_coeFn hU hUb x f
  have hz := integrable_greenFunction_mul_coeFn hU hUb z f
  have hdiff : Integrable (fun y => (greenFunction U x y - greenFunction U z y) * (f : ℂ → ℝ) y) volume :=
    (hx.sub hz).congr (Filter.Eventually.of_forall fun y => by simp only [Pi.sub_apply, sub_mul])
  have hrow : Integrable (fun y => |greenFunction U x y - greenFunction U z y|) volume :=
    integrable_abs_greenFunction_sub_pole hU hUb x z
  have key : (greenPotentialLInfinityFunctional hU hUb x - greenPotentialLInfinityFunctional hU hUb z) f
      = ∫ y, (greenFunction U x y - greenFunction U z y) * (f : ℂ → ℝ) y := by
    rw [sub_apply, greenPotentialLInfinityFunctional_apply,
      greenPotentialLInfinityFunctional_apply]
    simp only [sub_mul]
    exact (integral_sub hx hz).symm
  rw [Real.norm_eq_abs, key]
  calc |∫ y, (greenFunction U x y - greenFunction U z y) * (f : ℂ → ℝ) y|
      ≤ ∫ y, |(greenFunction U x y - greenFunction U z y) * (f : ℂ → ℝ) y| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y, |greenFunction U x y - greenFunction U z y| * ‖f‖ := by
        refine integral_mono_ae hdiff.abs (hrow.mul_const ‖f‖) ?_
        filter_upwards [abs_coeFn_le_norm_ae_top f] with y hy
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
    _ = (∫ y, |greenFunction U x y - greenFunction U z y|) * ‖f‖ :=
        integral_mul_const ‖f‖ (fun y => |greenFunction U x y - greenFunction U z y|)

/-- The operator-norm distance of two Green functionals of poles is at most the `L¹` distance of the two
Green rows: `dist Φ_x Φ_z ≤ dist (greenRowL1 x) (greenRowL1 z)`. -/
theorem dist_greenPotentialLInfinityFunctional_le {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (x z : ℂ) :
    dist (greenPotentialLInfinityFunctional hU hUb x) (greenPotentialLInfinityFunctional hU hUb z) ≤
      dist (greenRowL1 hU hUb x) (greenRowL1 hU hUb z) := by
  rw [dist_greenRowL1, dist_eq_norm]
  exact norm_greenPotentialLInfinityFunctional_sub_le hU hUb x z

/-- The Green functional of a pole depends continuously on the pole, for the operator norm, on the open set `U`:
`ContinuousOn (fun x => Φ_x) U`. -/
theorem continuousOn_greenPotentialLInfinityFunctional {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) :
    ContinuousOn (fun x => greenPotentialLInfinityFunctional hU hUb x) U := by
  intro x hx
  have hrow : Tendsto (fun z => dist (greenRowL1 hU hUb z) (greenRowL1 hU hUb x)) (𝓝[U] x) (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.1 (continuousOn_greenRowL1 hU hUb x hx)
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero' (Filter.Eventually.of_forall fun z => dist_nonneg)
    (Filter.Eventually.of_forall fun z => dist_greenPotentialLInfinityFunctional_le hU hUb z x) hrow

/-- On every compact `K ⊆ U` the Green functional of a pole is uniformly continuous for the operator norm:
`UniformContinuousOn (fun x => Φ_x) K`. -/
theorem uniformContinuousOn_greenPotentialLInfinityFunctional {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {K : Set ℂ} (hKU : K ⊆ U) (hK : IsCompact K) :
    UniformContinuousOn (fun x => greenPotentialLInfinityFunctional hU hUb x) K := by
  refine Metric.uniformContinuousOn_iff.2 fun ε hε => ?_
  obtain ⟨δ, hδ, h⟩ :=
    Metric.uniformContinuousOn_iff.1 (uniformContinuousOn_greenRowL1 hU hUb hKU hK) ε hε
  exact ⟨δ, hδ, fun a ha b hb hab =>
    (dist_greenPotentialLInfinityFunctional_le hU hUb a b).trans_lt (h a ha b hb hab)⟩

end HarmonicBalls
