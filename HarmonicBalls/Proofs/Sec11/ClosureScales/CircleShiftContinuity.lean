import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleDecoderAdditionCompatibility

/-!
# Joint continuity of the circle-code insertion on the actual carrier

Source: r10 written proof `notes/sec11-proof/sec11-proof-r10.tex`. Lemma `l:r9-circle-code` states the literal
insertion `Γ_z c (r, w) = c (r, w) - γ log max (r, |w - z|) + γ ∫ log max (1, |v|) σ_{r,w}(dv)` (TeX lines
1257-1284, equation `eq:r9-Gamma`). Its proof asserts that `Γ` is jointly Borel, in fact continuous (TeX lines
1380-1392). The independent audit of that assertion is `AUDIT-r9.md` line 18, table row "1027–1038" (round-9 TeX
numbering). The audit note is `docs/campaign/audits/CircleShiftContinuity.md`.

Carrier. `CircleDomain = {p : ℝ × ℂ // 0 < p.1}` with its subspace topology, and `C(CircleDomain, ℝ)` with the
compact-open topology (a Polish space, `CountableCircleDecoder.lean`). The functions are the literal
`circleDMSShiftFun` and `circleAverageFun` of `CircleDecoderAdditionCompatibility.lean`. Nothing here uses a
probability space, a reconstruction, a bound at infinity, or a continuous-insertion premise. The import closure of
this file contains no Lattice-Probability module, so no credit line is required (see the audit note).

Main results.
* `continuous_circleAverageFun`: `u ↦ circleAverageFun u u.continuous` is continuous from `C(ℂ, ℝ)` to
  `C(CircleDomain, ℝ)`.
* `continuous_circleDMSShiftFun`: `(γ, z, F) ↦ circleDMSShiftFun γ z F` is continuous from
  `ℝ × ℂ × C(CircleDomain, ℝ)` to `C(CircleDomain, ℝ)`.
* `measurable_circleDMSShiftFun` and `measurable_circleDMSShiftFun_comp`: the jointly Borel version, and measurability
  under arbitrary measurable coefficient, root and profile maps.
* `continuous_circleDMSShiftFun_fixedGamma`: for a fixed coefficient `γ`, `(F, z) ↦ circleDMSShiftFun γ z F` is
  continuous from `C(CircleDomain, ℝ) × ℂ` to `C(CircleDomain, ℝ)`.
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace HarmonicBalls

/-- Joint continuity of the circle average in the function and in the point `p = (r, c) : CircleDomain`, with radius
`r = p.val.1` and centre `c = p.val.2`: `(u, p) ↦ ⨍_{∂B_{p.val.1}(p.val.2)} u` is continuous on
`C(ℂ, ℝ) × CircleDomain`, with the compact-open topology on `C(ℂ, ℝ)`.
The integrand `(u, p, θ) ↦ u (circleMap p.val.2 p.val.1 θ)` is jointly continuous by continuity of evaluation, and the
parametric interval integral over the compact parameter interval `[0, 2π]` is continuous. -/
theorem continuous_circleAverage_joint :
    Continuous fun q : C(ℂ, ℝ) × CircleDomain => Real.circleAverage q.1 q.2.val.2 q.2.val.1 := by
  unfold Real.circleAverage
  refine continuous_const.mul ?_
  have hcm : Continuous fun x : (C(ℂ, ℝ) × CircleDomain) × ℝ =>
      (x.1.1, circleMap x.1.2.val.2 x.1.2.val.1 x.2) := by
    unfold circleMap
    fun_prop
  have hf : Continuous fun x : (C(ℂ, ℝ) × CircleDomain) × ℝ =>
      x.1.1 (circleMap x.1.2.val.2 x.1.2.val.1 x.2) :=
    continuous_eval.comp hcm
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (q : C(ℂ, ℝ) × CircleDomain) (θ : ℝ) => q.1 (circleMap q.2.val.2 q.2.val.1 θ)) hf 0 (2 * Real.pi)

/-- The circle average of a continuous function, as a continuous function of the function itself:
`u ↦ circleAverageFun u u.continuous` is continuous from `C(ℂ, ℝ)` (compact-open topology) to
`C(CircleDomain, ℝ)`. -/
theorem continuous_circleAverageFun :
    Continuous (fun u : C(ℂ, ℝ) => circleAverageFun u u.continuous) :=
  ContinuousMap.continuous_of_continuous_uncurry _ continuous_circleAverage_joint

/-- Joint continuity of the literal shift
`((γ, z, F), p) ↦ F p - γ log max (p.val.1, |p.val.2 - z|) + γ ⨍_{∂B_{p.val.1}(p.val.2)} log max (1, |·|)`
on `(ℝ × ℂ × C(CircleDomain, ℝ)) × CircleDomain`. The logarithm is continuous because
`max (r, |c - z|) ≥ r > 0` on `CircleDomain`. -/
theorem continuous_circleDMSShift_joint :
    Continuous fun q : (ℝ × ℂ × C(CircleDomain, ℝ)) × CircleDomain =>
      q.1.2.2 q.2 - q.1.1 * Real.log (max q.2.val.1 ‖q.2.val.2 - q.1.2.1‖)
        + q.1.1 * Real.circleAverage logMaxOne q.2.val.2 q.2.val.1 := by
  have hγ : Continuous fun q : (ℝ × ℂ × C(CircleDomain, ℝ)) × CircleDomain => q.1.1 :=
    continuous_fst.comp continuous_fst
  have hev : Continuous fun q : (ℝ × ℂ × C(CircleDomain, ℝ)) × CircleDomain => q.1.2.2 q.2 :=
    continuous_eval.comp ((continuous_snd.comp (continuous_snd.comp continuous_fst)).prodMk continuous_snd)
  have hmax : Continuous fun q : (ℝ × ℂ × C(CircleDomain, ℝ)) × CircleDomain =>
      max q.2.val.1 ‖q.2.val.2 - q.1.2.1‖ := by
    fun_prop
  have hlog : Continuous fun q : (ℝ × ℂ × C(CircleDomain, ℝ)) × CircleDomain =>
      Real.log (max q.2.val.1 ‖q.2.val.2 - q.1.2.1‖) :=
    hmax.log fun q => (lt_max_of_lt_left q.2.property).ne'
  have hpair : Continuous fun q : (ℝ × ℂ × C(CircleDomain, ℝ)) × CircleDomain =>
      (q.2.val.2, q.2.val.1) := by
    fun_prop
  have hcirc : Continuous fun q : (ℝ × ℂ × C(CircleDomain, ℝ)) × CircleDomain =>
      Real.circleAverage logMaxOne q.2.val.2 q.2.val.1 :=
    continuous_circleAverage_logMaxOne.comp hpair
  exact (hev.sub (hγ.mul hlog)).add (hγ.mul hcirc)

/-- **Joint continuity of the circle-code insertion.** The map `(γ, z, F) ↦ circleDMSShiftFun γ z F` is continuous
from `ℝ × ℂ × C(CircleDomain, ℝ)` (product topology, compact-open topology on the profile `F`) to
`C(CircleDomain, ℝ)`. -/
theorem continuous_circleDMSShiftFun :
    Continuous (fun p : ℝ × ℂ × C(CircleDomain, ℝ) => circleDMSShiftFun p.1 p.2.1 p.2.2) :=
  ContinuousMap.continuous_of_continuous_uncurry _ continuous_circleDMSShift_joint

/-- The jointly Borel version of `continuous_circleDMSShiftFun`, for the Borel σ-algebras
(`ContinuousMap.measurableSpace` on `C(CircleDomain, ℝ)`). -/
theorem measurable_circleDMSShiftFun :
    Measurable (fun p : ℝ × ℂ × C(CircleDomain, ℝ) => circleDMSShiftFun p.1 p.2.1 p.2.2) :=
  continuous_circleDMSShiftFun.measurable

/-- Measurable composition: for arbitrary measurable coefficient `γ`, root `z` and profile `F` on a measurable space
`S`, the insertion `s ↦ circleDMSShiftFun (γ s) (z s) (F s)` is measurable. -/
theorem measurable_circleDMSShiftFun_comp {S : Type*} [MeasurableSpace S] {γ : S → ℝ} {z : S → ℂ}
    {F : S → C(CircleDomain, ℝ)} (hγ : Measurable γ) (hz : Measurable z) (hF : Measurable F) :
    Measurable fun s => circleDMSShiftFun (γ s) (z s) (F s) :=
  measurable_circleDMSShiftFun.comp (hγ.prodMk (hz.prodMk hF))

/-- Fixed-coefficient specialization (the source assertion for a fixed `γ`): for each `γ`,
`(F, z) ↦ circleDMSShiftFun γ z F` is continuous from `C(CircleDomain, ℝ) × ℂ` to `C(CircleDomain, ℝ)`. -/
theorem continuous_circleDMSShiftFun_fixedGamma (γ : ℝ) :
    Continuous (fun q : C(CircleDomain, ℝ) × ℂ => circleDMSShiftFun γ q.2 q.1) :=
  continuous_circleDMSShiftFun.comp (continuous_const.prodMk (continuous_snd.prodMk continuous_fst))

/-- Measurable version of the fixed-coefficient specialization. -/
theorem measurable_circleDMSShiftFun_fixedGamma (γ : ℝ) :
    Measurable (fun q : C(CircleDomain, ℝ) × ℂ => circleDMSShiftFun γ q.2 q.1) :=
  (continuous_circleDMSShiftFun_fixedGamma γ).measurable

/-- The Borel version of `continuous_circleAverageFun`. -/
theorem measurable_circleAverageFun :
    Measurable (fun u : C(ℂ, ℝ) => circleAverageFun u u.continuous) :=
  continuous_circleAverageFun.measurable

/-- Measurable composition of the circle average with a measurable family `U : S → C(ℂ, ℝ)`. -/
theorem measurable_circleAverageFun_comp {S : Type*} [MeasurableSpace S] {U : S → C(ℂ, ℝ)}
    (hU : Measurable U) :
    Measurable fun s => circleAverageFun (U s) (U s).continuous :=
  measurable_circleAverageFun.comp hU

end HarmonicBalls
