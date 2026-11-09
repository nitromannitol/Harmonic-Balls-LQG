import HarmonicBalls.Proofs.Potential.BoundedDensityGreenStability

/-!
# The Green potential of a pole as a continuous functional on `L∞`

For a bounded open planar set `U` and a pole `x : ℂ`, the zero-extended Green row `y ↦ G_U(x, y)` is
`greenFunction U x` (the Green function of Armitage–Gardiner, value `0` off `U`, as in `Defs/Green.lean`).
For a class `f : Lp ℝ ∞ (volume : Measure ℂ)`, that is an essentially bounded real function taken modulo
almost-everywhere equality, the Green integral `∫ y, G_U(x, y) * f y` is computed on a representative of `f`.
This file packages it as a continuous real-linear functional on `L∞`:

* `greenPotentialLInfinityLinear hU hUb x` is the real-linear map `f ↦ ∫ y, G_U(x, y) * f y`;
* `greenPotentialLInfinityFunctional hU hUb x` is the same map as a continuous linear map
  `Lp ℝ ∞ volume →L[ℝ] ℝ`; its value on `f` is `∫ y, G_U(x, y) * f y` for the representative `⇑f`
  (`greenPotentialLInfinityFunctional_apply`);
* (integrability) `y ↦ G_U(x, y) * f y` is integrable for every `f ∈ L∞`
  (`integrable_greenFunction_mul_coeFn`), from the almost-everywhere bound `|f| ≤ ‖f‖`
  (`abs_coeFn_le_norm_ae_top`);
* (norm estimate) `|∫ G_U(x, y) f(y) dy| ≤ (∫ G_U(x, y) dy) * ‖f‖`
  (`abs_greenPotentialLInfinityFunctional_le`), hence `‖Φ_x‖ ≤ ∫ G_U(x, y) dy`
  (`norm_greenPotentialLInfinityFunctional_le`);
* (uniform bound) there is one constant `C ≥ 0`, depending only on `U`, with `‖Φ_x‖ ≤ C` for every pole `x`
  (`exists_greenPotentialLInfinityFunctional_norm_le`), from the uniform row mass bound of
  `BoundedDensityGreenStability`.

Linearity uses only almost-everywhere equalities of representatives (`Lp.coeFn_add`, `Lp.coeFn_smul`) and
integral congruence. The Green integral is not replaced by an assumed operator: the functional is defined by
the literal integral. Only `IsOpen U` and `IsBounded U` are assumed. No boundary regularity, no singular-source
representative, and no literature input enter.

The local volume estimate and the potential-theoretic infrastructure reached through the import closure use
work of Leonardo Bonanno, through the pinned Lattice-Probability (lean-v4.35) port.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Real Metric
open scoped ENNReal

/-- An `L∞` class is bounded by its norm almost everywhere: `|f y| ≤ ‖f‖` for almost every `y`, for any
representative `⇑f` of `f : Lp ℝ ∞ volume`. -/
theorem abs_coeFn_le_norm_ae_top (f : Lp ℝ ∞ (volume : Measure ℂ)) :
    ∀ᵐ y ∂(volume : Measure ℂ), |(f : ℂ → ℝ) y| ≤ ‖f‖ := by
  have hess : ∀ᵐ y ∂(volume : Measure ℂ), ‖(f : ℂ → ℝ) y‖ₑ ≤ ‖f‖ₑ := by
    have h := enorm_ae_le_eLpNormEssSup (f : ℂ → ℝ) (volume : Measure ℂ)
    rwa [← eLpNorm_exponent_top (Lp.aestronglyMeasurable f), ← Lp.enorm_def] at h
  filter_upwards [hess] with y hy
  rw [← Real.norm_eq_abs]
  refine (ENNReal.ofReal_le_ofReal_iff (norm_nonneg f)).1 ?_
  simpa [enorm_eq_ofReal_abs] using hy

/-- Integrability of the Green potential of an `L∞` class: for a bounded open `U`, a pole `x`, and an element
`f` of `Lp ℝ ∞ volume`, the function `y ↦ G_U(x, y) * f y` is integrable on `ℂ` for its representative `⇑f`. -/
theorem integrable_greenFunction_mul_coeFn {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (x : ℂ) (f : Lp ℝ ∞ (volume : Measure ℂ)) :
    Integrable (fun y => greenFunction U x y * (f : ℂ → ℝ) y) volume :=
  integrable_greenFunction_mul_of_ae_bounded hU hUb x (Lp.aestronglyMeasurable f)
    (abs_coeFn_le_norm_ae_top f)

/-- The Green potential of a pole `x` as a real-linear map on `L∞`: `f ↦ ∫ y, G_U(x, y) * f y`, computed on a
representative of `f`. Additivity and homogeneity hold because representatives add and scale almost everywhere
and the integral is invariant under almost-everywhere equality. -/
noncomputable def greenPotentialLInfinityLinear {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (x : ℂ) : Lp ℝ ∞ (volume : Measure ℂ) →ₗ[ℝ] ℝ where
  toFun f := ∫ y, greenFunction U x y * (f : ℂ → ℝ) y
  map_add' f g := by
    refine Eq.trans ?_ (integral_add (integrable_greenFunction_mul_coeFn hU hUb x f)
      (integrable_greenFunction_mul_coeFn hU hUb x g))
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add f g] with y hy
    simp only [hy, Pi.add_apply, mul_add]
  map_smul' c f := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c f] with y hy
    simp only [hy, Pi.smul_apply, smul_eq_mul]
    ring

/-- Norm estimate for the Green potential of a pole on `L∞`: for every `f`,
`|∫ G_U(x, y) * f y dy| ≤ (∫ G_U(x, y) dy) * ‖f‖`. The proof bounds the integrand by the nonnegative row times
the essential sup of `f`, using `G_U ≥ 0`. -/
theorem abs_greenPotentialLInfinityLinear_le {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (x : ℂ) (f : Lp ℝ ∞ (volume : Measure ℂ)) :
    |greenPotentialLInfinityLinear hU hUb x f| ≤ (∫ y, greenFunction U x y) * ‖f‖ := by
  have hrow := integrable_greenFunction_pole hU hUb x
  calc |greenPotentialLInfinityLinear hU hUb x f|
      = |∫ y, greenFunction U x y * (f : ℂ → ℝ) y| := rfl
    _ ≤ ∫ y, |greenFunction U x y * (f : ℂ → ℝ) y| := abs_integral_le_integral_abs
    _ ≤ ∫ y, greenFunction U x y * ‖f‖ := by
        refine integral_mono_ae (integrable_greenFunction_mul_coeFn hU hUb x f).abs
          (hrow.mul_const ‖f‖) ?_
        filter_upwards [abs_coeFn_le_norm_ae_top f] with y hy
        rw [abs_mul, abs_of_nonneg (greenFunction_nonneg hUb x y)]
        exact mul_le_mul_of_nonneg_left hy (greenFunction_nonneg hUb x y)
    _ = (∫ y, greenFunction U x y) * ‖f‖ := integral_mul_const ‖f‖ (fun y => greenFunction U x y)

/-- The Green potential of a pole `x` as a continuous real-linear functional on `L∞`, for a bounded open `U`:
`greenPotentialLInfinityFunctional hU hUb x f = ∫ y, G_U(x, y) * f y` for a representative of `f`. Its operator
norm is bounded by the row mass `∫ G_U(x, y) dy` (`norm_greenPotentialLInfinityFunctional_le`). -/
noncomputable def greenPotentialLInfinityFunctional {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (x : ℂ) : Lp ℝ ∞ (volume : Measure ℂ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous (greenPotentialLInfinityLinear hU hUb x) (∫ y, greenFunction U x y)
    (fun f => by
      rw [Real.norm_eq_abs]
      exact abs_greenPotentialLInfinityLinear_le hU hUb x f)

/-- Value of the Green functional: `greenPotentialLInfinityFunctional hU hUb x f = ∫ y, G_U(x, y) * f y`, where
`⇑f` is the representative of the `L∞` class `f`. -/
theorem greenPotentialLInfinityFunctional_apply {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (x : ℂ) (f : Lp ℝ ∞ (volume : Measure ℂ)) :
    greenPotentialLInfinityFunctional hU hUb x f = ∫ y, greenFunction U x y * (f : ℂ → ℝ) y :=
  rfl

/-- Norm estimate for the Green functional: `|∫ G_U(x, y) * f y dy| ≤ (∫ G_U(x, y) dy) * ‖f‖` for every `f`. -/
theorem abs_greenPotentialLInfinityFunctional_le {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (x : ℂ) (f : Lp ℝ ∞ (volume : Measure ℂ)) :
    |greenPotentialLInfinityFunctional hU hUb x f| ≤ (∫ y, greenFunction U x y) * ‖f‖ :=
  abs_greenPotentialLInfinityLinear_le hU hUb x f

/-- Operator norm of the Green functional of a pole: `‖greenPotentialLInfinityFunctional hU hUb x‖ ≤ ∫ G_U(x, y) dy`. -/
theorem norm_greenPotentialLInfinityFunctional_le {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (x : ℂ) :
    ‖greenPotentialLInfinityFunctional hU hUb x‖ ≤ ∫ y, greenFunction U x y :=
  ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun y => greenFunction_nonneg hUb x y)
    (fun f => by
      rw [Real.norm_eq_abs]
      exact abs_greenPotentialLInfinityFunctional_le hU hUb x f)

/-- One constant bounds the operator norms of all Green functionals on `L∞`. For a bounded open `U` there is
`C ≥ 0`, depending only on `U`, with `‖greenPotentialLInfinityFunctional hU hUb x‖ ≤ C` for every pole `x : ℂ`.
The constant is the uniform row mass of `BoundedDensityGreenStability`. -/
theorem exists_greenPotentialLInfinityFunctional_norm_le {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, ‖greenPotentialLInfinityFunctional hU hUb x‖ ≤ C := by
  obtain ⟨C, hC0, hrow⟩ := exists_greenFunction_row_integral_le hU hUb
  exact ⟨C, hC0, fun x => (norm_greenPotentialLInfinityFunctional_le hU hUb x).trans (hrow x).2⟩

end HarmonicBalls
