import HarmonicBalls.Defs.Notation

/-! # Green functions of open subsets of the plane

Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795), Section 2.2
(subsec:green, lines 466-489). The paper's `G_O` is the Green function of a bounded open set `O ⊆ ℂ`, normalized by
`ΔG_O(x,·) = -δ_x` (Proposition 2.3, prop:green-properties, line 480). We follow the classical construction
(Armitage–Gardiner, *Classical Potential Theory*, §4.1): the Green function is the Newtonian (logarithmic) kernel
minus its greatest harmonic minorant on `O`,
`G_O(x,y) = N(x,y) - I_O[N(x,·)](y)`, `N(x,y) = -(2π)⁻¹ log ‖x - y‖`.
References using the kernel `-log ‖x - y‖` (without the factor `(2π)⁻¹`) obtain `2π G_O`.

* `newtonKernel x y = -(2π)⁻¹ log ‖x - y‖`, the fundamental solution of `-Δ` (`ΔN(x,·) = -δ_x`);
  `newtonKernelEReal x` is the same function with its true value `+∞` at the pole `x`;
* `IsHarmonicMinorant O u h`, `greatestHarmonicMinorant O u`: harmonic minorants of an extended-real function
  and their pointwise supremum;
* `greenFunction O x y`: the Green function `G_O(x,y)`;
* `greenBall R x y = (2π)⁻¹ log (|R² - x̄ y| / (R |x - y|))`, the explicit Green function of `B_R(0)`
  (cf. the commented formula of lines 471-477); the identity `greenFunction (ball 0 R) = greenBall R` off the
  diagonal is a separate theorem;
* `greenPotential O μ x = ∫ G_O(x,y) μ(dy)`, the Green potential of a measure, e.g. `q_{B_R}` of
  eq:expected-exit-time (line 3533) and the functions of the class `H̃_O(D)` (eq:harmonic-fns, line 137).

## Junk values

The paper's `G_O : Ō × Ō → ℝ ∪ {∞}` is `+∞` on the diagonal. Here `greenFunction O x y : ℝ` takes the junk value
`0` on the diagonal `x = y`; every definition or statement evaluating `G_O` on the diagonal must exclude it
explicitly. We also set `greenFunction O x y = 0` if `x ∉ O` or `y ∉ O`; for a ball
(or any regular open set) this is the boundary value `G_O(x,·) = 0` on `∂O` of Proposition 2.3.
For an open set with no harmonic minorant of the kernel (a non-Greenian set, e.g. `O = ℂ`) the greatest harmonic
minorant is `⊥` and the value is junk; the paper only uses bounded `O`, which are Greenian
(`greenFunction_nonneg`).
-/

namespace HarmonicBalls

open MeasureTheory ComplexConjugate

/-- The Newtonian (logarithmic) kernel of the plane, `N(x,y) = -(2π)⁻¹ log ‖x - y‖`, the fundamental solution of
`-Δ`: `ΔN(x,·) = -δ_x`, the normalization of Proposition 2.3 (line 480) and of the commented formula of
lines 471-477. On the diagonal the true value is `+∞`; here `Real.log 0 = 0` gives the junk value `0`
(see `newtonKernelEReal`). -/
noncomputable def newtonKernel (x y : ℂ) : ℝ :=
  -(2 * Real.pi)⁻¹ * Real.log ‖x - y‖

/-- The Newtonian kernel with pole `x` as an extended-real (superharmonic) function: `+∞` at `y = x` and
`newtonKernel x y` elsewhere. Harmonic minorants are taken of this function, so that the pole imposes no
constraint. -/
noncomputable def newtonKernelEReal (x y : ℂ) : EReal :=
  if y = x then ⊤ else (newtonKernel x y : EReal)

/-- `h` is a *harmonic minorant* of `u : ℂ → [-∞, ∞]` on `O`: `h` is harmonic on (a neighbourhood of each point
of) `O` and `h ≤ u` on `O` (Armitage–Gardiner §4.1). -/
def IsHarmonicMinorant (O : Set ℂ) (u : ℂ → EReal) (h : ℂ → ℝ) : Prop :=
  InnerProductSpace.HarmonicOnNhd h O ∧ ∀ y ∈ O, (h y : EReal) ≤ u y

/-- The *greatest harmonic minorant* `I_O[u]` of `u` on `O`: the pointwise supremum of all harmonic minorants of
`u` on `O` (Armitage–Gardiner §4.1). It is `⊥` where `u` has no harmonic minorant on `O`. When `u` is superharmonic
on the open set `O` and has a harmonic minorant there, `I_O[u]` is itself harmonic on `O` and hence the largest
harmonic minorant; that is a theorem, not part of this definition. -/
noncomputable def greatestHarmonicMinorant (O : Set ℂ) (u : ℂ → EReal) (y : ℂ) : EReal :=
  ⨆ (h : ℂ → ℝ) (_ : IsHarmonicMinorant O u h), (h y : EReal)

open Classical in
/-- The *Green function* `G_O(x,y)` of an open set `O ⊆ ℂ` (subsec:green, line 468), normalized by
`ΔG_O(x,·) = -δ_x` (Proposition 2.3, line 480): for `x, y ∈ O` with `x ≠ y`,
`G_O(x,y) = newtonKernel x y - I_O[newtonKernelEReal x](y)` (Armitage–Gardiner §4.1, with the kernel normalized by
`(2π)⁻¹`). Junk values: `0` on the diagonal `x = y` (where the paper's value is `+∞`) and `0` if `x ∉ O` or
`y ∉ O`. -/
noncomputable def greenFunction (O : Set ℂ) (x y : ℂ) : ℝ :=
  if x ∈ O ∧ y ∈ O ∧ x ≠ y then
    newtonKernel x y - (greatestHarmonicMinorant O (newtonKernelEReal x) y).toReal
  else 0

/-- The explicit Green function of the ball `B_R(0)`,
`G_{B_R}(x,y) = (2π)⁻¹ log (|R² - x̄ y| / (R |x - y|))` for `x, y ∈ B_R(0)`, `x ≠ y` (cf. the commented formula of
lines 471-477, for `R = 1`). Outside `B_R(0) × B_R(0)` this formula is not the Green function; on the diagonal it
takes the junk value `0`, as `greenFunction` does. -/
noncomputable def greenBall (R : ℝ) (x y : ℂ) : ℝ :=
  (2 * Real.pi)⁻¹ * Real.log (‖(R : ℂ) ^ 2 - conj x * y‖ / (R * ‖x - y‖))

/-- The *Green potential* `x ↦ ∫ G_O(x,y) μ(dy)` of a measure `μ` on `O` (Armitage–Gardiner §4.2). For `O = B_R`
and `μ` the LQG measure this is `q_{B_R}` of eq:expected-exit-time (line 3533); the paper writes the integrand as
`G_{B_R}(y,·)`, which agrees by the symmetry of the Green function. Green potentials of signed Radon measures
`ν = ν₊ - ν₋` (the class `H̃_O(D)`, eq:harmonic-fns, line 137) are differences
`greenPotential O ν₊ - greenPotential O ν₋`. Since `greenFunction O x y = 0` for `y ∉ O`, the integral is over `O`.
Junk value `0` when `y ↦ G_O(x,y)` is not `μ`-integrable; if `μ` has an atom at `x`, the diagonal junk value of
`greenFunction` enters. -/
noncomputable def greenPotential (O : Set ℂ) (μ : Measure ℂ) (x : ℂ) : ℝ :=
  ∫ y, greenFunction O x y ∂μ

/-! ## Sanity lemmas -/

theorem newtonKernel_comm (x y : ℂ) : newtonKernel x y = newtonKernel y x := by
  rw [newtonKernel, newtonKernel, norm_sub_rev]

theorem greenFunction_of_notMem_left {O : Set ℂ} {x : ℂ} (hx : x ∉ O) (y : ℂ) : greenFunction O x y = 0 := by
  simp [greenFunction, hx]

theorem greenFunction_of_notMem_right {O : Set ℂ} {y : ℂ} (hy : y ∉ O) (x : ℂ) : greenFunction O x y = 0 := by
  simp [greenFunction, hy]

/-- The diagonal junk value. -/
theorem greenFunction_self (O : Set ℂ) (x : ℂ) : greenFunction O x x = 0 := by
  simp [greenFunction]

theorem greatestHarmonicMinorant_le {O : Set ℂ} {u : ℂ → EReal} {y : ℂ} (hy : y ∈ O) :
    greatestHarmonicMinorant O u y ≤ u y :=
  iSup₂_le fun _ hh => hh.2 y hy

theorem IsHarmonicMinorant.le_greatestHarmonicMinorant {O : Set ℂ} {u : ℂ → EReal} {h : ℂ → ℝ}
    (hh : IsHarmonicMinorant O u h) (y : ℂ) : (h y : EReal) ≤ greatestHarmonicMinorant O u y :=
  le_iSup₂ (f := fun (h : ℂ → ℝ) (_ : IsHarmonicMinorant O u h) => (h y : EReal)) h hh

/-- On a set contained in `closedBall x r`, the constant `-(2π)⁻¹ log r` is a harmonic minorant of the kernel with
pole `x`; in particular bounded open sets are Greenian. -/
theorem isHarmonicMinorant_const_newtonKernelEReal {O : Set ℂ} {x : ℂ} {r : ℝ}
    (hO : O ⊆ Metric.closedBall x r) :
    IsHarmonicMinorant O (newtonKernelEReal x) (fun _ => -(2 * Real.pi)⁻¹ * Real.log r) := by
  refine ⟨InnerProductSpace.harmonicOnNhd_const _, fun y hy => ?_⟩
  by_cases hyx : y = x
  · simp [newtonKernelEReal, hyx]
  · simp only [newtonKernelEReal, hyx, ite_false, EReal.coe_le_coe_iff, newtonKernel]
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hyx))
    have hle : ‖x - y‖ ≤ r := by
      have := hO hy
      rwa [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] at this
    have hlog := Real.log_le_log hpos hle
    have hπ : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
    rw [neg_mul, neg_mul, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_left hlog hπ

/-- Weak positivity of the Green function of a bounded set (cf. Proposition 2.3, "Positive", line 483). -/
theorem greenFunction_nonneg {O : Set ℂ} (hO : Bornology.IsBounded O) (x y : ℂ) : 0 ≤ greenFunction O x y := by
  unfold greenFunction
  split_ifs with h
  · obtain ⟨-, hy, hxy⟩ := h
    obtain ⟨r, hOr⟩ := hO.subset_closedBall x
    have hlow := (isHarmonicMinorant_const_newtonKernelEReal hOr).le_greatestHarmonicMinorant y
    have hup : greatestHarmonicMinorant O (newtonKernelEReal x) y ≤ (newtonKernel x y : EReal) := by
      simpa [newtonKernelEReal, Ne.symm hxy] using greatestHarmonicMinorant_le (u := newtonKernelEReal x) hy
    have hbot : greatestHarmonicMinorant O (newtonKernelEReal x) y ≠ ⊥ :=
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlow
    have := EReal.toReal_le_toReal hup hbot (EReal.coe_ne_top _)
    rw [EReal.toReal_coe] at this
    linarith
  · exact le_rfl

theorem greenPotential_nonneg {O : Set ℂ} (hO : Bornology.IsBounded O) (μ : Measure ℂ) (x : ℂ) :
    0 ≤ greenPotential O μ x :=
  integral_nonneg (greenFunction_nonneg hO x)

/-- `G_{B_R}(0,y) = (2π)⁻¹ log (R / |y|)` (cf. the case `x = 0` of the commented formula, line 475). -/
theorem greenBall_zero_left {R : ℝ} (hR : 0 < R) {y : ℂ} (hy : y ≠ 0) :
    greenBall R 0 y = (2 * Real.pi)⁻¹ * Real.log (R / ‖y‖) := by
  have hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  rw [greenBall, map_zero, zero_mul, sub_zero, zero_sub, norm_neg, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR, sq, mul_div_mul_left _ _ hR.ne']

/-- The diagonal junk value of `greenBall` agrees with that of `greenFunction`. -/
theorem greenBall_self (R : ℝ) (x : ℂ) : greenBall R x x = 0 := by
  simp [greenBall]

end HarmonicBalls
