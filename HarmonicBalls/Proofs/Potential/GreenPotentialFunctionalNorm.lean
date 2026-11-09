import HarmonicBalls.Proofs.Potential.GreenPotentialLInfinityFunctional

/-!
# Positivity and the exact operator norm of the Green potential of a pole on `L∞`

For a bounded open planar set `U` and a pole `x : ℂ`, `greenPotentialLInfinityFunctional hU hUb x` is the literal
Green potential of the pole on `L∞` (`GreenPotentialLInfinityFunctional.lean`): a class
`f : Lp ℝ ∞ (volume : Measure ℂ)` is sent to `∫ y, G_U(x, y) * f y`, computed on a representative of `f`
(`greenPotentialLInfinityFunctional_apply`). Here `G_U(x, ·) = greenFunction U x` is the zero-extended Green row of
Armitage–Gardiner, with value `0` off `U` (`Defs/Green.lean`). Nothing is replaced: no positive functional is
assumed and no norm is assumed. This file proves:

* (positivity) if `0 ≤ f` almost everywhere, then `0 ≤ greenPotentialLInfinityFunctional hU hUb x f`
  (`greenPotentialLInfinityFunctional_nonneg`); `greenPotentialLInfinityFunctional_nonneg_of_lp` states the same for
  `0 ≤ f` in the order of `Lp`;
* (off-`U` zero functional) if `x ∉ U`, the zero-extended row vanishes identically, so the functional is the zero
  continuous linear map on `L∞` (`greenPotentialLInfinityFunctional_eq_zero_of_notMem`); the empty set is a case of
  this, since every pole lies outside `∅` (`greenPotentialLInfinityFunctional_empty`);
* (the constant `1`) the class of the constant function `1` has norm `1` on the plane (`norm_toLp_const_one`), and
  its value is the row mass: `greenPotentialLInfinityFunctional hU hUb x 1 = ∫ y, G_U(x, y) dy`
  (`greenPotentialLInfinityFunctional_const_one`);
* (exact norm) `‖greenPotentialLInfinityFunctional hU hUb x‖ = ∫ y, G_U(x, y) dy` for every pole `x`
  (`norm_greenPotentialLInfinityFunctional_eq`). The upper bound is `norm_greenPotentialLInfinityFunctional_le`; the
  lower bound evaluates the functional on `1` and uses `G_U ≥ 0`. No case distinction is needed: for `x ∉ U`, and for
  `U = ∅`, both sides are `0`.

Only `IsOpen U` and `IsBounded U` are assumed. No boundary regularity, no singular-source representative and no
literature input enter.

The local volume estimate and the potential-theoretic infrastructure reached through the import closure use work of
Leonardo Bonanno, through the pinned Lattice-Probability (lean-v4.35) port.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Real Metric
open scoped ENNReal

/-- Positivity of the Green potential of a pole on `L∞`: if `0 ≤ f` almost everywhere, then
`0 ≤ greenPotentialLInfinityFunctional hU hUb x f`. The integrand `G_U(x, y) * f y` is almost everywhere
nonnegative, because `G_U ≥ 0` everywhere (`greenFunction_nonneg`) and `f ≥ 0` almost everywhere; the integral of
an almost everywhere nonnegative function is nonnegative. -/
theorem greenPotentialLInfinityFunctional_nonneg {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (x : ℂ) {f : Lp ℝ ∞ (volume : Measure ℂ)} (hf : 0 ≤ᵐ[volume] (f : ℂ → ℝ)) :
    0 ≤ greenPotentialLInfinityFunctional hU hUb x f := by
  rw [greenPotentialLInfinityFunctional_apply]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hf] with y hy
  exact mul_nonneg (greenFunction_nonneg hUb x y) hy

/-- Positivity on the order of `Lp`: for `0 ≤ f` in `Lp ℝ ∞ volume`, the Green potential of a pole is nonnegative.
`Lp.coeFn_nonneg` identifies this order with almost everywhere nonnegativity of a representative. -/
theorem greenPotentialLInfinityFunctional_nonneg_of_lp {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (x : ℂ) {f : Lp ℝ ∞ (volume : Measure ℂ)} (hf : 0 ≤ f) :
    0 ≤ greenPotentialLInfinityFunctional hU hUb x f :=
  greenPotentialLInfinityFunctional_nonneg hU hUb x ((Lp.coeFn_nonneg f).2 hf)

/-- Off `U` the Green functional of a pole vanishes: if `x ∉ U`, then `G_U(x, y) = 0` for every `y`
(`greenFunction_of_notMem_left`), so `greenPotentialLInfinityFunctional hU hUb x f = 0` for every `f` in `L∞`.
The functional is the zero continuous linear map. -/
theorem greenPotentialLInfinityFunctional_eq_zero_of_notMem {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {x : ℂ} (hx : x ∉ U) :
    greenPotentialLInfinityFunctional hU hUb x = 0 := by
  ext f
  rw [greenPotentialLInfinityFunctional_apply, zero_apply]
  simp [greenFunction_of_notMem_left hx]

/-- The empty set: every pole lies outside `∅`, so the Green functional of every pole is the zero functional on
`L∞`. -/
theorem greenPotentialLInfinityFunctional_empty (x : ℂ) :
    greenPotentialLInfinityFunctional isOpen_empty Bornology.isBounded_empty x = 0 :=
  greenPotentialLInfinityFunctional_eq_zero_of_notMem isOpen_empty Bornology.isBounded_empty
    (Set.notMem_empty x)

/-- The class of the constant function `1` in `L∞(volume)` on the plane has norm `1`: its representative is the
constant `1`, and the essential supremum of a nonzero constant is its modulus (`eLpNormEssSup_const`, with
`volume ≠ 0`). -/
theorem norm_toLp_const_one :
    ‖MemLp.toLp (fun _ : ℂ => (1 : ℝ))
      (memLp_top_const (1 : ℝ) : MemLp (fun _ : ℂ => (1 : ℝ)) ∞ (volume : Measure ℂ))‖ = 1 := by
  rw [Lp.norm_toLp, eLpNorm_exponent_top aestronglyMeasurable_const,
    eLpNormEssSup_const _ (NeZero.ne (volume : Measure ℂ))]
  simp

/-- The Green functional of a pole at the class of the constant function `1` is the row mass:
`greenPotentialLInfinityFunctional hU hUb x 1 = ∫ y, G_U(x, y) dy`. The representative of the class is `1` almost
everywhere (`MemLp.coeFn_toLp`). -/
theorem greenPotentialLInfinityFunctional_const_one {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (x : ℂ) :
    greenPotentialLInfinityFunctional hU hUb x
      (MemLp.toLp (fun _ : ℂ => (1 : ℝ))
        (memLp_top_const (1 : ℝ) : MemLp (fun _ : ℂ => (1 : ℝ)) ∞ (volume : Measure ℂ)))
      = ∫ y, greenFunction U x y := by
  rw [greenPotentialLInfinityFunctional_apply]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_top_const (1 : ℝ) :
    MemLp (fun _ : ℂ => (1 : ℝ)) ∞ (volume : Measure ℂ))] with y hy
  simp [hy]

/-- Exact operator norm of the Green potential of a pole on `L∞`: for a bounded open `U` and every pole `x : ℂ`,
`‖greenPotentialLInfinityFunctional hU hUb x‖ = ∫ y, G_U(x, y) dy`. The bound `≤` is
`norm_greenPotentialLInfinityFunctional_le`. For `≥`, `∫ G_U(x, y) dy = Φ_x 1 ≤ ‖Φ_x‖ * ‖1‖ = ‖Φ_x‖`, by
`greenPotentialLInfinityFunctional_const_one`, `norm_toLp_const_one` and `G_U ≥ 0`. -/
theorem norm_greenPotentialLInfinityFunctional_eq {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (x : ℂ) :
    ‖greenPotentialLInfinityFunctional hU hUb x‖ = ∫ y, greenFunction U x y := by
  refine le_antisymm (norm_greenPotentialLInfinityFunctional_le hU hUb x) ?_
  have hG : 0 ≤ ∫ y, greenFunction U x y := integral_nonneg fun y => greenFunction_nonneg hUb x y
  have h1 := (greenPotentialLInfinityFunctional hU hUb x).le_opNorm
    (MemLp.toLp (fun _ : ℂ => (1 : ℝ))
      (memLp_top_const (1 : ℝ) : MemLp (fun _ : ℂ => (1 : ℝ)) ∞ (volume : Measure ℂ)))
  rw [norm_toLp_const_one, mul_one, Real.norm_eq_abs,
    greenPotentialLInfinityFunctional_const_one hU hUb x, abs_of_nonneg hG] at h1
  exact h1

/-- Off `U` the Green functional has norm `0`: if `x ∉ U`, then `‖greenPotentialLInfinityFunctional hU hUb x‖ = 0`. -/
theorem norm_greenPotentialLInfinityFunctional_eq_zero_of_notMem {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {x : ℂ} (hx : x ∉ U) :
    ‖greenPotentialLInfinityFunctional hU hUb x‖ = 0 := by
  rw [greenPotentialLInfinityFunctional_eq_zero_of_notMem hU hUb hx, norm_zero]

/-- The empty set: the Green functional of every pole has norm `0`, in agreement with `∫ G_∅(x, y) dy = 0`. -/
theorem norm_greenPotentialLInfinityFunctional_empty (x : ℂ) :
    ‖greenPotentialLInfinityFunctional isOpen_empty Bornology.isBounded_empty x‖ = 0 := by
  rw [greenPotentialLInfinityFunctional_empty, norm_zero]

end HarmonicBalls
