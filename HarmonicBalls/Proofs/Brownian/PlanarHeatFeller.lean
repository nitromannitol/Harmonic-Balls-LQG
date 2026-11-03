import Mathlib
import HarmonicBalls.Proofs.Brownian.PlanarHeatSemigroup

/-! # Feller property of the planar heat semigroup

The planar heat semigroup `planarHeatSemigroup` is a Feller semigroup: it maps `C₀(ℂ, ℝ)` into
itself and its `C₀` orbits are continuous in time.

The proof uses the scaling representation
`planarGaussian z t = stdPlanarGaussian.map (fun w ↦ z + √t * w)` of the transition law, which
turns the transition operator on `f ∈ C₀(ℂ, ℝ)` into
`z ↦ ∫ f (z + √t * w) d stdPlanarGaussian(w)`. It ports verbatim the one-dimensional argument of
`MarkovProcess.Examples.HeatSemigroup` (replacing `ℝ`, `gaussianReal 0 1`, `|z|` by `ℂ`,
`stdPlanarGaussian`, `‖w‖`): continuity and vanishing at infinity follow by dominated convergence,
and the short-time uniform control of the orbit displacement follows from uniform continuity of `f`
and tightness of the standard Gaussian.

Main results:

* `kernelIntegral_planarHeatSemigroup`: the scaling representation of the transition operator.
* `mapsC0_planarHeatSemigroup`: `planarHeatSemigroup` maps `C₀(ℂ, ℝ)` into itself.
* `hasContinuousC0Orbits_planarHeatSemigroup`: its `C₀` orbits are continuous in time.
* `isFellerKernelSemigroup_planarHeatSemigroup`: the Feller property.
-/

namespace HarmonicBalls

open Filter MeasureTheory ProbabilityTheory MarkovProcess
open scoped ENNReal NNReal ZeroAtInfty

/-- **The scaling representation of the planar heat semigroup.**  Integrating a `C₀` function
against the transition measure at time `t` from `z` is integrating its translate
`w ↦ f (z + √t * w)` against the standard planar Gaussian. -/
theorem kernelIntegral_planarHeatSemigroup (t : ℝ≥0) (f : C₀(ℂ, ℝ)) (z : ℂ) :
    kernelIntegral (planarHeatSemigroup t) f z =
      ∫ w, f (z + (Real.sqrt t : ℂ) * w) ∂stdPlanarGaussian := by
  rw [kernelIntegral, planarHeatSemigroup_apply, planarGaussian_eq_map_add_sqrt_mul]
  exact integral_map (φ := fun w : ℂ ↦ z + (Real.sqrt t : ℂ) * w) (f := fun y : ℂ ↦ f y)
    (by fun_prop) f.continuous.aestronglyMeasurable

/-- A `C₀` function on `ℂ` is bounded by its norm. -/
private theorem norm_apply_le_norm_c0_complex (f : C₀(ℂ, ℝ)) (z : ℂ) : ‖f z‖ ≤ ‖f‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact f.toBCF.norm_coe_le_norm z

/-- The norm of `(√t : ℂ) * w` is `√t * ‖w‖`. -/
private theorem norm_ofReal_sqrt_mul (t : ℝ≥0) (w : ℂ) :
    ‖(Real.sqrt t : ℂ) * w‖ = Real.sqrt t * ‖w‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

private theorem integrable_c0_comp_complex (f : C₀(ℂ, ℝ)) (t : ℝ≥0) (z : ℂ) :
    Integrable (fun w : ℂ ↦ f (z + (Real.sqrt t : ℂ) * w)) stdPlanarGaussian := by
  refine Integrable.mono' (integrable_const ‖f‖) ?_ (Filter.Eventually.of_forall fun w ↦ ?_)
  · exact (f.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact norm_apply_le_norm_c0_complex f _

/-- The planar heat semigroup maps `C₀(ℂ, ℝ)` into itself. -/
theorem mapsC0_planarHeatSemigroup : planarHeatSemigroup.MapsC0 := by
  intro t f
  have hrep : kernelIntegral (planarHeatSemigroup t) f =
      fun z ↦ ∫ w, f (z + (Real.sqrt t : ℂ) * w) ∂stdPlanarGaussian :=
    funext (kernelIntegral_planarHeatSemigroup t f)
  rw [hrep]
  constructor
  · refine continuous_of_dominated (F := fun (z w : ℂ) ↦ f (z + (Real.sqrt t : ℂ) * w))
      (bound := fun _ ↦ ‖f‖) ?_ ?_ (integrable_const (μ := stdPlanarGaussian) ‖f‖) ?_
    · exact fun z ↦ (f.continuous.comp (by fun_prop)).aestronglyMeasurable
    · exact fun z ↦ Filter.Eventually.of_forall fun w ↦ norm_apply_le_norm_c0_complex f _
    · exact Filter.Eventually.of_forall fun w ↦ f.continuous.comp (by fun_prop)
  · have hcg : (Filter.cocompact ℂ).IsCountablyGenerated := by
      rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop]
      infer_instance
    refine Filter.tendsto_iff_seq_tendsto.mpr fun u hu ↦ ?_
    have hlim : Filter.Tendsto
        (fun n ↦ ∫ w, f (u n + (Real.sqrt t : ℂ) * w) ∂stdPlanarGaussian) atTop
        (nhds (∫ _w : ℂ, (0 : ℝ) ∂stdPlanarGaussian)) := by
      refine tendsto_integral_of_dominated_convergence
        (F := fun (n : ℕ) (w : ℂ) ↦ f (u n + (Real.sqrt t : ℂ) * w)) (fun _ ↦ ‖f‖)
        (fun _ ↦ (f.continuous.comp (by fun_prop)).aestronglyMeasurable)
        (integrable_const (μ := stdPlanarGaussian) ‖f‖)
        (fun _ ↦ Filter.Eventually.of_forall fun _ ↦ norm_apply_le_norm_c0_complex f _)
        (Filter.Eventually.of_forall fun w ↦ ?_)
      have htranslate : Filter.Tendsto (fun y : ℂ ↦ y + (Real.sqrt t : ℂ) * w)
          (Filter.cocompact ℂ) (Filter.cocompact ℂ) :=
        CocompactMapClass.cocompact_tendsto
          ((Homeomorph.addRight ((Real.sqrt t : ℂ) * w)).toCocompactMap)
      exact f.zero_at_infty'.comp (htranslate.comp hu)
    rw [integral_zero] at hlim
    exact hlim

/-- A finite measure on the complex plane puts arbitrarily little mass far from the origin. -/
private theorem exists_measure_norm_ge_lt (nu : Measure ℂ) [IsFiniteMeasure nu] {eps : ℝ}
    (heps : 0 < eps) : ∃ R : ℝ, 0 < R ∧ (nu {w : ℂ | R ≤ ‖w‖}).toReal < eps := by
  have hmeasA : ∀ n : ℕ, NullMeasurableSet {w : ℂ | (n : ℝ) ≤ ‖w‖} nu := fun n ↦
    ((isClosed_le continuous_const continuous_norm).measurableSet).nullMeasurableSet
  have hanti : Antitone (fun n : ℕ ↦ {w : ℂ | (n : ℝ) ≤ ‖w‖}) := by
    intro n m hnm w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    exact le_trans (Nat.cast_le.mpr hnm) hw
  have hempty : (⋂ n : ℕ, {w : ℂ | (n : ℝ) ≤ ‖w‖}) = (∅ : Set ℂ) := by
    refine Set.eq_empty_of_forall_notMem fun w hw ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_gt ‖w‖
    exact absurd (Set.mem_iInter.mp hw n) (not_le.mpr hn)
  have htend := tendsto_measure_iInter_atTop hmeasA hanti ⟨0, measure_ne_top nu _⟩
  rw [hempty, measure_empty] at htend
  have hev : ∀ᶠ n : ℕ in atTop, nu {w : ℂ | (n : ℝ) ≤ ‖w‖} < ENNReal.ofReal eps :=
    htend.eventually_lt_const (by simpa using heps)
  obtain ⟨n, hn⟩ := (hev.and (Filter.eventually_gt_atTop 0)).exists
  exact ⟨(n : ℝ), by exact_mod_cast hn.2, ENNReal.toReal_lt_of_lt_ofReal hn.1⟩

/-- The `C₀` orbit displacement of the planar heat semigroup is uniformly small over short times:
for every `ε > 0` there is a `δ > 0` such that the transition operator moves a `C₀` function by at
most `ε` in the uniform norm over every time shorter than `δ`. -/
theorem exists_norm_c0Operator_sub_le_planarHeatSemigroup (f : C₀(ℂ, ℝ)) {eps : ℝ}
    (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ h : ℝ≥0, (h : ℝ) < delta →
      ‖planarHeatSemigroup.c0Operator mapsC0_planarHeatSemigroup h f - f‖ ≤ eps := by
  obtain ⟨delta0, hdelta0, huc⟩ := Metric.uniformContinuous_iff.mp
    (ZeroAtInftyContinuousMap.uniformContinuous f) (eps / 2) (half_pos heps)
  have hfpos : (0 : ℝ) < 4 * (‖f‖ + 1) := by positivity
  obtain ⟨R, hR, hRmeas⟩ := exists_measure_norm_ge_lt stdPlanarGaussian
    (eps := eps / (4 * (‖f‖ + 1))) (by positivity)
  set S : Set ℂ := {w : ℂ | R ≤ ‖w‖} with hS
  have hSmeas : MeasurableSet S := (isClosed_le continuous_const continuous_norm).measurableSet
  set bound : ℂ → ℝ := fun w ↦ eps / 2 + 2 * ‖f‖ * S.indicator (fun _ ↦ (1 : ℝ)) w with hbound
  have hindInt : Integrable (S.indicator (fun _ ↦ (1 : ℝ))) stdPlanarGaussian :=
    (integrable_indicator_iff hSmeas).mpr (integrableOn_const (measure_ne_top _ _))
  have hboundInt : Integrable bound stdPlanarGaussian :=
    (integrable_const (μ := stdPlanarGaussian) (eps / 2)).add (hindInt.const_mul _)
  have hboundIntegral : ∫ w, bound w ∂stdPlanarGaussian ≤ eps := by
    rw [hbound, integral_add (integrable_const (μ := stdPlanarGaussian) (eps / 2))
      (hindInt.const_mul _), integral_const, MeasureTheory.integral_const_mul,
      integral_indicator_const (1 : ℝ) hSmeas]
    have hnorm : 0 ≤ ‖f‖ := norm_nonneg f
    have hkey : 2 * ‖f‖ * (stdPlanarGaussian.real S) ≤ eps / 2 := by
      have hpos : (0 : ℝ) ≤ stdPlanarGaussian.real S := measureReal_nonneg
      calc 2 * ‖f‖ * (stdPlanarGaussian.real S)
          ≤ 2 * (‖f‖ + 1) * (eps / (4 * (‖f‖ + 1))) := by
            apply mul_le_mul _ (le_of_lt hRmeas) hpos (by positivity)
            exact mul_le_mul_of_nonneg_left (by linarith only []) (by norm_num)
        _ = eps / 2 := by field_simp; ring
    rw [probReal_univ]
    simp only [smul_eq_mul, mul_one]
    linarith only [hkey]
  refine ⟨(delta0 / R) ^ 2, by positivity, fun h hh ↦ ?_⟩
  have hsqrt : Real.sqrt h * R < delta0 := by
    have h1 : Real.sqrt h < delta0 / R := by
      have := Real.sqrt_lt_sqrt h.coe_nonneg hh
      rwa [Real.sqrt_sq (by positivity)] at this
    calc Real.sqrt h * R < (delta0 / R) * R := by
          exact mul_lt_mul_of_pos_right h1 hR
      _ = delta0 := div_mul_cancel₀ delta0 (ne_of_gt hR)
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (le_of_lt heps)).2 fun z ↦ ?_
  show ‖planarHeatSemigroup.c0Operator mapsC0_planarHeatSemigroup h f z - f z‖ ≤ eps
  rw [SubMarkovKernelSemigroup.c0Operator_apply, kernelIntegral_planarHeatSemigroup]
  have hsub : (∫ w, f (z + (Real.sqrt h : ℂ) * w) ∂stdPlanarGaussian) - f z =
      ∫ w, (f (z + (Real.sqrt h : ℂ) * w) - f z) ∂stdPlanarGaussian := by
    rw [integral_sub (integrable_c0_comp_complex f h z) (integrable_const (f z)), integral_const,
      probReal_univ, one_smul]
  rw [hsub]
  refine le_trans (norm_integral_le_of_norm_le hboundInt
    (Filter.Eventually.of_forall fun w ↦ ?_)) hboundIntegral
  by_cases hw : w ∈ S
  · have h1 : ‖f (z + (Real.sqrt h : ℂ) * w) - f z‖ ≤ 2 * ‖f‖ := by
      calc ‖f (z + (Real.sqrt h : ℂ) * w) - f z‖ ≤ ‖f (z + (Real.sqrt h : ℂ) * w)‖ + ‖f z‖ :=
            norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ :=
            add_le_add (norm_apply_le_norm_c0_complex f _) (norm_apply_le_norm_c0_complex f _)
        _ = 2 * ‖f‖ := by ring
    rw [hbound]
    simp only [Set.indicator_of_mem hw, mul_one]
    linarith only [h1, heps]
  · have hdist : dist (z + (Real.sqrt h : ℂ) * w) z < delta0 := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_ofReal_sqrt_mul]
      have hwR : ‖w‖ < R := lt_of_not_ge (by simpa only [hS, Set.mem_ofPred_eq] using hw)
      calc Real.sqrt h * ‖w‖ ≤ Real.sqrt h * R :=
            mul_le_mul_of_nonneg_left (le_of_lt hwR) (Real.sqrt_nonneg _)
        _ < delta0 := hsqrt
    have h2 : ‖f (z + (Real.sqrt h : ℂ) * w) - f z‖ ≤ eps / 2 := by
      rw [← dist_eq_norm]
      exact le_of_lt (huc hdist)
    rw [hbound]
    simp only [Set.indicator_of_notMem hw, mul_zero, add_zero]
    exact h2

/-- The `C₀` orbits of the planar heat semigroup are continuous in time. -/
theorem hasContinuousC0Orbits_planarHeatSemigroup :
    planarHeatSemigroup.HasContinuousC0Orbits mapsC0_planarHeatSemigroup := by
  intro f
  rw [Metric.continuous_iff]
  intro b eps heps
  obtain ⟨delta, hdelta, hkey⟩ :=
    exists_norm_c0Operator_sub_le_planarHeatSemigroup f (half_pos heps)
  refine ⟨delta, hdelta, fun a hab ↦ ?_⟩
  have hcontraction : ∀ c d : ℝ≥0, c ≤ d → (d : ℝ) - (c : ℝ) < delta →
      dist (planarHeatSemigroup.c0Operator mapsC0_planarHeatSemigroup d f)
        (planarHeatSemigroup.c0Operator mapsC0_planarHeatSemigroup c f) ≤ eps / 2 := by
    intro c d hcd hlt
    have hdc : c + (d - c) = d := add_tsub_cancel_of_le hcd
    have hcoe : ((d - c : ℝ≥0) : ℝ) < delta := by
      rw [NNReal.coe_sub hcd]
      exact hlt
    have hop : planarHeatSemigroup.c0Operator mapsC0_planarHeatSemigroup d f =
        planarHeatSemigroup.c0Operator mapsC0_planarHeatSemigroup c
          (planarHeatSemigroup.c0Operator mapsC0_planarHeatSemigroup (d - c) f) := by
      conv_lhs => rw [← hdc]
      rw [SubMarkovKernelSemigroup.c0Operator_add]
      rfl
    rw [dist_eq_norm, hop, ← map_sub]
    calc ‖planarHeatSemigroup.c0Operator mapsC0_planarHeatSemigroup c
            (planarHeatSemigroup.c0Operator mapsC0_planarHeatSemigroup (d - c) f - f)‖
        ≤ ‖planarHeatSemigroup.c0Operator mapsC0_planarHeatSemigroup c‖ *
            ‖planarHeatSemigroup.c0Operator mapsC0_planarHeatSemigroup (d - c) f - f‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (eps / 2) := by
          refine mul_le_mul (SubMarkovKernelSemigroup.norm_c0Operator_le _ _ c)
            (hkey _ hcoe) (norm_nonneg _) zero_le_one
      _ = eps / 2 := one_mul _
  have habs : |(a : ℝ) - (b : ℝ)| < delta := by
    rw [← NNReal.dist_eq]
    exact hab
  rcases le_total b a with hba | hab'
  · have := hcontraction b a hba (by
      rw [abs_of_nonneg (by
        have : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hba
        linarith only [this])] at habs
      exact habs)
    linarith only [this, heps]
  · have := hcontraction a b hab' (by
      rw [abs_sub_comm, abs_of_nonneg (by
        have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab'
        linarith only [this])] at habs
      exact habs)
    rw [dist_comm]
    linarith only [this, heps]

/-- **The planar heat semigroup is a Feller semigroup.** -/
theorem isFellerKernelSemigroup_planarHeatSemigroup :
    planarHeatSemigroup.IsFellerKernelSemigroup :=
  ⟨mapsC0_planarHeatSemigroup, hasContinuousC0Orbits_planarHeatSemigroup⟩

end HarmonicBalls
