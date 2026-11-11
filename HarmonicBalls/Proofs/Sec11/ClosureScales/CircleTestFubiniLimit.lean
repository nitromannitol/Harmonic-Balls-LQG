import Mathlib
import HarmonicBalls.Defs.Laplacian
import HarmonicBalls.Proofs.Potential.Fundamental
import HarmonicBalls.Proofs.Sec11.ClosureScales.RouteACircleSmooth
import HarmonicBalls.Proofs.Sec11.ClosureScales.CirclePotential
import HarmonicBalls.Proofs.Sec11.ClosureScales.RootedShiftProfile
import HarmonicBalls.Proposed.DuplantierMillerSheffield

/-!
# Deterministic test-integral limit of circle averages

Deterministic prerequisite of the `R` direction of the circle-code lemma, following the written
argument: the circle/plane Fubini
identity moves the circle average from a locally integrable insertion onto a smooth compactly
supported test, and the averaged tests `φ_r` converge to `φ` with one fixed compact enlargement.

For a test function `φ` (`IsTestFunction univ φ`) and `0 < r ≤ 1` the averaged test is
`φ_r(v) = Real.circleAverage φ v r`. We prove:

* `φ_r` is a smooth compactly supported test function whose support lies in the fixed compact
  enlargement `testEnlargement φ = tsupport φ + closedBall 0 1`, and `φ_r → φ` uniformly as `r ↓ 0`;
* for `g` locally integrable on `ℂ`, `∫ w, ⨍_{∂B(w,r)} g · φ = ∫ v, g v · φ_r v`, with the absolute
  integrability needed for the Fubini step;
* hence `∫ w, ⨍_{∂B(w,r)} g · φ → ∫ v, g v · φ v` as `r ↓ 0`, derived from the uniform convergence
  and the common compact support.

The instances are every continuous `u`, and every `dmsShift γ z` (the logarithmic shift of
Duplantier-Miller-Sheffield, Lemma A.10), whose circle averages are the literal formula
`-γ * log (max r ‖w - z‖) + γ * ⨍_{∂B(w,r)} logMaxOne`, valid also for circles through `z`.
The test `φ` is fixed first; the centre `z` and the continuous addition `u` are quantified after it.
No probabilistic event, field, or literature hypothesis is used.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff Pointwise
open Real

noncomputable section

namespace HarmonicBalls.CircleTestFubini

/-- The fixed compact enlargement `tsupport φ + closedBall 0 1` of the support of a test function. -/
def testEnlargement (φ : ℂ → ℝ) : Set ℂ :=
  tsupport φ + Metric.closedBall (0 : ℂ) 1

/-- The angle parameter `θ ∈ (0, 2π]` with Lebesgue measure. -/
abbrev angleMeasure : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * π))

instance angleMeasure_isFiniteMeasure : IsFiniteMeasure angleMeasure :=
  Real.isFiniteMeasure_restrict_Ioc _ _

lemma isCompact_testEnlargement {φ : ℂ → ℝ} (hφ : HasCompactSupport φ) :
    IsCompact (testEnlargement φ) :=
  (show IsCompact (tsupport φ) from hφ).add (isCompact_closedBall _ _)

lemma circleMap_eq_add_centre (w : ℂ) (r θ : ℝ) : circleMap w r θ = w + circleMap 0 r θ := by
  have h := circleMap_sub_center w r θ
  linear_combination h

lemma circleAverage_eq_Ioc (f : ℂ → ℝ) (w : ℂ) (r : ℝ) :
    Real.circleAverage f w r = (2 * π)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * π), f (circleMap w r θ) := by
  rw [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le (by positivity)]

lemma circleMap_zero_add_two_pi (r θ : ℝ) : circleMap 0 r (θ + 2 * π) = circleMap 0 r θ := by
  simp only [circleMap, zero_add]
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

lemma circleMap_zero_add_pi (r θ : ℝ) : circleMap 0 r (θ + π) = -circleMap 0 r θ := by
  simp only [circleMap, zero_add]
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- A half-period shift of a `2π`-periodic function over one period. -/
lemma integral_shift_periodic (G : ℝ → ℝ) (hG : Function.Periodic G (2 * π)) :
    ∫ θ in Ioc (0 : ℝ) (2 * π), G (θ + π) = ∫ θ in Ioc (0 : ℝ) (2 * π), G θ := by
  rw [← intervalIntegral.integral_of_le (by positivity), ← intervalIntegral.integral_of_le (by positivity)]
  calc ∫ θ in (0 : ℝ)..2 * π, G (θ + π) = ∫ θ in (0 : ℝ) + π..2 * π + π, G θ :=
        intervalIntegral.integral_comp_add_right (f := G) π
    _ = ∫ θ in π..π + 2 * π, G θ := by rw [zero_add, add_comm (2 * π) π]
    _ = ∫ θ in (0 : ℝ)..0 + 2 * π, G θ := hG.intervalIntegral_add_eq π 0
    _ = ∫ θ in (0 : ℝ)..2 * π, G θ := by rw [zero_add]

/-- Reflection through the centre: `∫ φ(v - c θ) dθ = ∫ φ(v + c θ) dθ` over one period. -/
lemma setIntegral_sub_circle_eq (φ : ℂ → ℝ) (v : ℂ) (r : ℝ) :
    ∫ θ in Ioc (0 : ℝ) (2 * π), φ (v - circleMap 0 r θ) =
      ∫ θ in Ioc (0 : ℝ) (2 * π), φ (v + circleMap 0 r θ) := by
  have hper : Function.Periodic (fun θ : ℝ => φ (v + circleMap 0 r θ)) (2 * π) := fun θ => by
    simp only [circleMap_zero_add_two_pi]
  have h := integral_shift_periodic _ hper
  simp only [circleMap_zero_add_pi, ← sub_eq_add_neg] at h
  exact h

lemma integral_circleAverage_centre (φ : ℂ → ℝ) (v : ℂ) (r : ℝ) :
    ∫ θ in Ioc (0 : ℝ) (2 * π), φ (v + circleMap 0 r θ) = 2 * π * Real.circleAverage φ v r := by
  rw [circleAverage_eq_Ioc, ← mul_assoc, mul_inv_cancel₀ (show (2 * π : ℝ) ≠ 0 by positivity), one_mul]
  congr 1
  funext θ
  rw [circleMap_eq_add_centre v r θ]

/-! ### The averaged test function -/

/-- The averaged test vanishes outside the fixed enlargement when `|r| ≤ 1`. -/
lemma circleAverage_eq_zero_of_notMem {φ : ℂ → ℝ} {v : ℂ} {r : ℝ} (hr : |r| ≤ 1)
    (hv : v ∉ testEnlargement φ) : Real.circleAverage φ v r = 0 := by
  have hz : ∀ θ : ℝ, φ (circleMap v r θ) = 0 := by
    intro θ
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply hv
    unfold testEnlargement
    refine Set.mem_add.2 ⟨circleMap v r θ, hmem, -circleMap 0 r θ, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, norm_neg, norm_circleMap_zero]
      exact hr
    · rw [circleMap_eq_add_centre v r θ]
      ring
  rw [circleAverage_eq_Ioc]
  simp [hz]

lemma tsupport_circleAverage_subset {φ : ℂ → ℝ} (hφ : HasCompactSupport φ) {r : ℝ} (hr : |r| ≤ 1) :
    tsupport (fun v => Real.circleAverage φ v r) ⊆ testEnlargement φ := by
  unfold tsupport
  apply closure_minimal _ (isCompact_testEnlargement hφ).isClosed
  intro v hv
  by_contra hnot
  exact hv (circleAverage_eq_zero_of_notMem hr hnot)

lemma hasCompactSupport_circleAverage {φ : ℂ → ℝ} (hφ : HasCompactSupport φ) {r : ℝ}
    (hr : |r| ≤ 1) : HasCompactSupport (fun v => Real.circleAverage φ v r) :=
  (isCompact_testEnlargement hφ).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_circleAverage_subset hφ hr)

/-- **Averaged test function.** For `|r| ≤ 1`, `φ_r = ⨍_{∂B(·,r)} φ` is a smooth compactly supported
test function with support in the fixed compact enlargement `testEnlargement φ`. -/
theorem isTestFunction_circleAverage {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) {r : ℝ}
    (hr : |r| ≤ 1) : IsTestFunction (testEnlargement φ) (fun v => Real.circleAverage φ v r) :=
  ⟨contDiff_circleAverage_of_contDiff hφ.1 hφ.2.1 r, hasCompactSupport_circleAverage hφ.2.1 hr,
    tsupport_circleAverage_subset hφ.2.1 hr⟩

/-- **Averaged test function in the plane.** -/
theorem isTestFunction_univ_circleAverage {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) {r : ℝ}
    (hr : |r| ≤ 1) : IsTestFunction univ (fun v => Real.circleAverage φ v r) :=
  ⟨contDiff_circleAverage_of_contDiff hφ.1 hφ.2.1 r, hasCompactSupport_circleAverage hφ.2.1 hr,
    subset_univ _⟩

/-- **Fixed compact enlargement.** `testEnlargement φ` is compact, and for every radius `0 < r ≤ 1`
the averaged test `φ_r` is a smooth compactly supported test function (on `univ`, and supported in
the one fixed enlargement). -/
theorem fixed_enlargement_circleAverage {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    IsCompact (testEnlargement φ) ∧
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        IsTestFunction (testEnlargement φ) (fun v => Real.circleAverage φ v r) ∧
          IsTestFunction univ (fun v => Real.circleAverage φ v r) := by
  refine ⟨isCompact_testEnlargement hφ.2.1, fun r hr0 hr1 => ?_⟩
  have hr : |r| ≤ 1 := abs_le.2 ⟨by linarith, hr1⟩
  exact ⟨isTestFunction_circleAverage hφ hr, isTestFunction_univ_circleAverage hφ hr⟩

/-- A uniform bound on `φ` gives the same bound on every circle average. -/
lemma norm_circleAverage_le {φ : ℂ → ℝ} {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) (v : ℂ) (r : ℝ) :
    ‖Real.circleAverage φ v r‖ ≤ M := by
  have hpos : (0 : ℝ) < 2 * π := by positivity
  have hI : ‖∫ θ in Ioc (0 : ℝ) (2 * π), φ (circleMap v r θ)‖ ≤ M * (2 * π) := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) (2 * π))
      (f := fun θ => φ (circleMap v r θ)) (C := M) measure_Ioc_lt_top (fun θ _ => hM _)
    rwa [Real.volume_real_Ioc_of_le (by positivity : (0 : ℝ) ≤ 2 * π), sub_zero] at h
  rw [circleAverage_eq_Ioc, norm_mul, norm_inv, Real.norm_of_nonneg hpos.le]
  have h2π : (2 * π : ℝ) ≠ 0 := hpos.ne'
  calc (2 * π)⁻¹ * ‖∫ θ in Ioc (0 : ℝ) (2 * π), φ (circleMap v r θ)‖
      ≤ (2 * π)⁻¹ * (M * (2 * π)) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = M := by field_simp

/-- **Uniform convergence of the averaged tests.** -/
lemma tendstoUniformly_circleAverage {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    TendstoUniformly (fun (r : ℝ) (v : ℂ) => Real.circleAverage φ v r) φ (𝓝[>] (0 : ℝ)) := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have huc : UniformContinuous φ := hφ.2.1.uniformContinuous_of_continuous hφ.1.continuous
  obtain ⟨δ, hδ, hδφ⟩ := Metric.uniformContinuous_iff.1 huc (ε / 2) (half_pos hε)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr v
  have hr0 : 0 < r := hr.1
  have hrδ : r < δ := hr.2
  have hconst : ∫ θ in Ioc (0 : ℝ) (2 * π), φ v = 2 * π * φ v := by
    rw [setIntegral_const, Real.volume_real_Ioc_of_le (by positivity : (0 : ℝ) ≤ 2 * π), smul_eq_mul]
    ring
  have hcont : Continuous fun θ : ℝ => φ (circleMap v r θ) :=
    hφ.1.continuous.comp (continuous_circleMap v r)
  have hdiff : Real.circleAverage φ v r - φ v
      = (2 * π)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * π), (φ (circleMap v r θ) - φ v) := by
    rw [integral_sub hcont.integrableOn_Ioc
        (continuous_const (y := φ v) : Continuous fun _ : ℝ => φ v).integrableOn_Ioc, hconst,
      circleAverage_eq_Ioc]
    field_simp
  have hbound : ∀ θ ∈ Ioc (0 : ℝ) (2 * π), ‖φ (circleMap v r θ) - φ v‖ ≤ ε / 2 := by
    intro θ _
    have hd : dist (circleMap v r θ) v < δ := by
      rw [dist_eq_norm, circleMap_eq_add_centre v r θ, add_sub_cancel_left, norm_circleMap_zero,
        abs_of_pos hr0]
      exact hrδ
    rw [← dist_eq_norm]
    exact (hδφ hd).le
  have hI : ‖∫ θ in Ioc (0 : ℝ) (2 * π), (φ (circleMap v r θ) - φ v)‖ ≤ ε / 2 * (2 * π) := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) (2 * π))
      (f := fun θ => φ (circleMap v r θ) - φ v) (C := ε / 2) measure_Ioc_lt_top hbound
    rwa [Real.volume_real_Ioc_of_le (by positivity : (0 : ℝ) ≤ 2 * π), sub_zero] at h
  rw [dist_comm, dist_eq_norm, hdiff, norm_mul, norm_inv, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * π)]
  calc (2 * π)⁻¹ * ‖∫ θ in Ioc (0 : ℝ) (2 * π), (φ (circleMap v r θ) - φ v)‖
      ≤ (2 * π)⁻¹ * (ε / 2 * (2 * π)) := mul_le_mul_of_nonneg_left hI (by positivity)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- Pointwise convergence `φ_r(v) → φ(v)` as `r ↓ 0`. -/
lemma tendsto_circleAverage_test {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) (v : ℂ) :
    Tendsto (fun r : ℝ => Real.circleAverage φ v r) (𝓝[>] (0 : ℝ)) (𝓝 (φ v)) :=
  (tendstoUniformly_circleAverage hφ).tendsto_at v

/-! ### Integrability and the Fubini identity -/

lemma integrable_indicator_norm {g : ℂ → ℝ} (hgl : LocallyIntegrable g) {K : Set ℂ}
    (hK : IsCompact K) : Integrable (fun v => K.indicator (fun v => ‖g v‖) v) := by
  have h1 : IntegrableOn (fun v => ‖g v‖) K := Integrable.norm (hgl.integrableOn_isCompact hK)
  exact h1.integrable_indicator hK.isClosed.measurableSet

lemma integrable_indicator_norm_mul {g : ℂ → ℝ} (hgl : LocallyIntegrable g) {K : Set ℂ}
    (hK : IsCompact K) (M : ℝ) : Integrable (fun v => M * K.indicator (fun v => ‖g v‖) v) :=
  (integrable_indicator_norm hgl hK).const_mul M

/-- Pointwise domination of `g · φ_r` by a fixed integrable function, for `|r| ≤ 1`. -/
lemma norm_mul_circleAverage_le {g : ℂ → ℝ} {φ : ℂ → ℝ} {M : ℝ} (hM : ∀ x, ‖φ x‖ ≤ M) {r : ℝ}
    (hr : |r| ≤ 1) (v : ℂ) :
    ‖g v * Real.circleAverage φ v r‖ ≤ M * (testEnlargement φ).indicator (fun v => ‖g v‖) v := by
  by_cases hv : v ∈ testEnlargement φ
  · rw [Set.indicator_of_mem hv, norm_mul, mul_comm M]
    exact mul_le_mul_of_nonneg_left (norm_circleAverage_le hM v r) (norm_nonneg _)
  · rw [circleAverage_eq_zero_of_notMem hr hv, Set.indicator_of_notMem hv]
    simp

lemma integrable_mul_circleAverage {g : ℂ → ℝ} (hgl : LocallyIntegrable g) {φ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) {r : ℝ} (hr : |r| ≤ 1) :
    Integrable (fun v => g v * Real.circleAverage φ v r) := by
  obtain ⟨M, hM⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2.1
  have hcont : Continuous (fun v => Real.circleAverage φ v r) :=
    (contDiff_circleAverage_of_contDiff hφ.1 hφ.2.1 r).continuous
  refine Integrable.mono' (integrable_indicator_norm_mul hgl (isCompact_testEnlargement hφ.2.1) M)
    (hgl.aestronglyMeasurable.mul hcont.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun v => norm_mul_circleAverage_le hM hr v

/-- The kernel `(θ, v) ↦ g v · φ(v - c θ)` on `(0, 2π] × ℂ` is integrable, where `c θ = r e^{iθ}`. -/
lemma integrable_kernel {g : ℂ → ℝ} (hgm : Measurable g) (hgl : LocallyIntegrable g) {φ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) {r : ℝ} (hr : |r| ≤ 1) :
    Integrable (fun p : ℝ × ℂ => g p.2 * φ (p.2 - circleMap 0 r p.1)) (angleMeasure.prod volume) := by
  obtain ⟨M, hM⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2.1
  have hprod : Integrable (fun p : ℝ × ℂ => M * (testEnlargement φ).indicator (fun v => ‖g v‖) p.2)
      (angleMeasure.prod volume) :=
    (integrable_const (μ := angleMeasure) M).mul_prod
      (integrable_indicator_norm hgl (isCompact_testEnlargement hφ.2.1))
  have hmeas : Measurable (fun p : ℝ × ℂ => g p.2 * φ (p.2 - circleMap 0 r p.1)) :=
    (hgm.comp measurable_snd).mul (hφ.1.continuous.measurable.comp
      (measurable_snd.sub ((continuous_circleMap 0 r).measurable.comp measurable_fst)))
  refine Integrable.mono' hprod hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  by_cases hv : p.2 ∈ testEnlargement φ
  · rw [Set.indicator_of_mem hv, norm_mul]
    calc ‖g p.2‖ * ‖φ (p.2 - circleMap 0 r p.1)‖ ≤ ‖g p.2‖ * M :=
          mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      _ = M * ‖g p.2‖ := mul_comm _ _
  · have hzero : φ (p.2 - circleMap 0 r p.1) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      apply hv
      unfold testEnlargement
      refine Set.mem_add.2 ⟨p.2 - circleMap 0 r p.1, hmem, circleMap 0 r p.1, ?_, sub_add_cancel _ _⟩
      rw [mem_closedBall_zero_iff, norm_circleMap_zero]
      exact hr
    rw [Set.indicator_of_notMem hv, hzero]
    simp

/-- **Circle/plane Fubini identity for measurable `g`.** -/
theorem integral_circleAverage_mul_eq_of_measurable {g : ℂ → ℝ} (hgm : Measurable g)
    (hgl : LocallyIntegrable g) {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) {r : ℝ} (hr : |r| ≤ 1) :
    Integrable (fun w => Real.circleAverage g w r * φ w) ∧
      ∫ w, Real.circleAverage g w r * φ w = ∫ v, g v * Real.circleAverage φ v r := by
  have hH := integrable_kernel hgm hgl hφ hr
  -- the shear `(θ, w) ↦ (θ, w + c θ)` preserves `angleMeasure × volume`
  have hgmeas : Measurable (Function.uncurry fun (θ : ℝ) (w : ℂ) => w + circleMap 0 r θ) :=
    measurable_snd.add ((continuous_circleMap 0 r).measurable.comp measurable_fst)
  have hae : ∀ᵐ θ ∂angleMeasure, Measure.map (fun w : ℂ => w + circleMap 0 r θ) volume = volume :=
    Filter.Eventually.of_forall fun θ => map_add_right_eq_self volume (circleMap 0 r θ)
  have hT : MeasurePreserving (fun p : ℝ × ℂ => (p.1, p.2 + circleMap 0 r p.1))
      (angleMeasure.prod volume) (angleMeasure.prod volume) :=
    MeasurePreserving.skew_product (MeasurePreserving.id angleMeasure) hgmeas hae
  have hF : Integrable (fun p : ℝ × ℂ => g (p.2 + circleMap 0 r p.1) * φ p.2)
      (angleMeasure.prod volume) := by
    have h := (hT.integrable_comp hH.aestronglyMeasurable).2 hH
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp_apply, add_sub_cancel_right]
  have hFs := hF.swap
  have hLHS : ∀ w : ℂ, Real.circleAverage g w r * φ w
      = (2 * π)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * π), g (w + circleMap 0 r θ) * φ w := by
    intro w
    rw [circleAverage_eq_Ioc, mul_assoc, ← integral_mul_const]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    dsimp only
    rw [circleMap_eq_add_centre w r θ]
  have hLHSint : Integrable (fun w => Real.circleAverage g w r * φ w) := by
    have h := (hFs.integral_prod_left).const_mul (2 * π)⁻¹
    refine h.congr (Filter.Eventually.of_forall fun w => ?_)
    exact (hLHS w).symm
  have hinner : ∀ θ : ℝ, ∫ w, g (w + circleMap 0 r θ) * φ w
      = ∫ v, g v * φ (v - circleMap 0 r θ) := by
    intro θ
    have h := integral_add_right_eq_self (μ := (volume : Measure ℂ))
      (fun v : ℂ => g v * φ (v - circleMap 0 r θ)) (circleMap 0 r θ)
    simp only [add_sub_cancel_right] at h
    exact h
  have hswap : ∫ w, ∫ θ in Ioc (0 : ℝ) (2 * π), g (w + circleMap 0 r θ) * φ w
      = ∫ θ in Ioc (0 : ℝ) (2 * π), ∫ w, g (w + circleMap 0 r θ) * φ w :=
    integral_integral_swap (f := fun w θ => g (w + circleMap 0 r θ) * φ w) hFs
  have hLHS_eq : ∫ w, Real.circleAverage g w r * φ w
      = (2 * π)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * π), ∫ v, g v * φ (v - circleMap 0 r θ) := by
    calc ∫ w, Real.circleAverage g w r * φ w
        = ∫ w, (2 * π)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * π), g (w + circleMap 0 r θ) * φ w :=
          integral_congr_ae (Filter.Eventually.of_forall hLHS)
      _ = (2 * π)⁻¹ * ∫ w, ∫ θ in Ioc (0 : ℝ) (2 * π), g (w + circleMap 0 r θ) * φ w :=
          integral_const_mul _ _
      _ = (2 * π)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * π), ∫ w, g (w + circleMap 0 r θ) * φ w := by
          rw [hswap]
      _ = (2 * π)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * π), ∫ v, g v * φ (v - circleMap 0 r θ) := by
          congr 1
          exact integral_congr_ae (Filter.Eventually.of_forall hinner)
  have hH_swap : ∫ θ in Ioc (0 : ℝ) (2 * π), ∫ v, g v * φ (v - circleMap 0 r θ)
      = ∫ v, ∫ θ in Ioc (0 : ℝ) (2 * π), g v * φ (v - circleMap 0 r θ) :=
    integral_integral_swap (f := fun θ v => g v * φ (v - circleMap 0 r θ)) hH
  have hstep : ∀ v : ℂ, ∫ θ in Ioc (0 : ℝ) (2 * π), g v * φ (v - circleMap 0 r θ)
      = g v * (2 * π * Real.circleAverage φ v r) := by
    intro v
    rw [integral_const_mul, setIntegral_sub_circle_eq φ v r, integral_circleAverage_centre φ v r]
  refine ⟨hLHSint, ?_⟩
  rw [hLHS_eq, hH_swap]
  simp_rw [hstep]
  rw [← integral_const_mul]
  congr 1
  funext v
  field_simp

/-- Changing `g` on a Lebesgue null set does not change its circle averages for almost every centre
`w`: the disagreement set has null product measure with the angle, by translation invariance. -/
lemma ae_circleAverage_eq_of_ae_eq {g g' : ℂ → ℝ} (h : g =ᵐ[volume] g') {r : ℝ} :
    ∀ᵐ w ∂(volume : Measure ℂ), Real.circleAverage g w r = Real.circleAverage g' w r := by
  obtain ⟨t, hsub, htm, ht0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  have hQm : MeasurableSet {p : ℂ × ℝ | p.1 + circleMap 0 r p.2 ∈ t} :=
    htm.preimage (measurable_fst.add ((continuous_circleMap 0 r).measurable.comp measurable_snd))
  have hQ0 : (volume.prod angleMeasure) {p : ℂ × ℝ | p.1 + circleMap 0 r p.2 ∈ t} = 0 := by
    rw [Measure.prod_apply_symm hQm]
    have hsec : ∀ θ : ℝ, volume ((fun w : ℂ => (w, θ)) ⁻¹' {p : ℂ × ℝ | p.1 + circleMap 0 r p.2 ∈ t})
        = 0 := by
      intro θ
      have hpre : (fun w : ℂ => (w, θ)) ⁻¹' {p : ℂ × ℝ | p.1 + circleMap 0 r p.2 ∈ t}
          = (fun w : ℂ => w + circleMap 0 r θ) ⁻¹' t := rfl
      rw [hpre, measure_preimage_add_right]
      exact ht0
    simp only [hsec, lintegral_zero]
  have hae : ∀ᵐ z ∂(volume.prod angleMeasure), z ∉ {p : ℂ × ℝ | p.1 + circleMap 0 r p.2 ∈ t} := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hQ0
  filter_upwards [Measure.ae_ae_of_ae_prod hae] with w hw
  rw [circleAverage_eq_Ioc, circleAverage_eq_Ioc]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hw] with θ hθ
  by_contra hne
  have hm : w + circleMap 0 r θ ∈ t := by
    rw [← circleMap_eq_add_centre w r θ]
    exact hsub (show circleMap w r θ ∈ {x : ℂ | ¬ g x = g' x} from hne)
  exact hθ hm

/-- **Circle/plane Fubini identity for locally integrable `g`.** -/
theorem integral_circleAverage_mul_eq {g : ℂ → ℝ} (hgl : LocallyIntegrable g) {φ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) {r : ℝ} (hr : |r| ≤ 1) :
    Integrable (fun w => Real.circleAverage g w r * φ w) ∧
      Integrable (fun v => g v * Real.circleAverage φ v r) ∧
      ∫ w, Real.circleAverage g w r * φ w = ∫ v, g v * Real.circleAverage φ v r := by
  set g' : ℂ → ℝ := hgl.aestronglyMeasurable.mk g with hg'
  have hae : g =ᵐ[volume] g' := hgl.aestronglyMeasurable.ae_eq_mk
  have hgm' : Measurable g' := hgl.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hgl' : LocallyIntegrable g' := hgl.congr hae
  obtain ⟨hI, hEq⟩ := integral_circleAverage_mul_eq_of_measurable hgm' hgl' hφ hr
  have hLHS : (fun w => Real.circleAverage g w r * φ w)
      =ᵐ[volume] (fun w => Real.circleAverage g' w r * φ w) := by
    filter_upwards [ae_circleAverage_eq_of_ae_eq hae (r := r)] with w hw
    simp only [hw]
  have hRHS : (fun v => g v * Real.circleAverage φ v r)
      =ᵐ[volume] (fun v => g' v * Real.circleAverage φ v r) := by
    filter_upwards [hae] with v hv
    simp only [hv]
  refine ⟨hI.congr hLHS.symm, integrable_mul_circleAverage hgl hφ hr, ?_⟩
  rw [integral_congr_ae hLHS, hEq, integral_congr_ae hRHS]

/-! ### The limit `r ↓ 0` -/

/-- **Deterministic test-integral limit.** For a test function `φ` and a locally integrable `g`,
`∫ w, ⨍_{∂B(w,r)} g · φ → ∫ v, g v · φ v` as `r ↓ 0`. -/
theorem tendsto_integral_circleAverage_mul {g : ℂ → ℝ} (hgl : LocallyIntegrable g) {φ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) :
    Tendsto (fun r : ℝ => ∫ w, Real.circleAverage g w r * φ w) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ v, g v * φ v)) := by
  obtain ⟨M, hM⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2.1
  have hbound := integrable_indicator_norm_mul hgl (isCompact_testEnlargement hφ.2.1) M
  have hlim : Tendsto (fun r : ℝ => ∫ v, g v * Real.circleAverage φ v r) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ v, g v * φ v)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun v => M * (testEnlargement φ).indicator (fun v => ‖g v‖) v) ?_ ?_ hbound ?_
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with r hr
      have hr1 : |r| ≤ 1 := abs_le.2 ⟨by linarith [hr.1], hr.2.le⟩
      exact (integral_circleAverage_mul_eq hgl hφ hr1).2.1.aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with r hr
      have hr1 : |r| ≤ 1 := abs_le.2 ⟨by linarith [hr.1], hr.2.le⟩
      exact Filter.Eventually.of_forall fun v => norm_mul_circleAverage_le hM hr1 v
    · exact Filter.Eventually.of_forall fun v => (tendsto_circleAverage_test hφ v).const_mul (g v)
  refine Tendsto.congr' ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with r hr
  have hr1 : |r| ≤ 1 := abs_le.2 ⟨by linarith [hr.1], hr.2.le⟩
  exact (integral_circleAverage_mul_eq hgl hφ hr1).2.2.symm

/-- **Instance: every continuous addition `u`.** The test `φ` is fixed first; `u` is arbitrary
and continuous. -/
theorem tendsto_integral_continuous_circleAverage_mul (φ : ℂ → ℝ) (hφ : IsTestFunction univ φ)
    (u : ℂ → ℝ) (hu : Continuous u) :
    Tendsto (fun r : ℝ => ∫ w, Real.circleAverage u w r * φ w) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ v, u v * φ v)) :=
  tendsto_integral_circleAverage_mul hu.locallyIntegrable hφ

/-! ### The logarithmic instance `dmsShift γ z` -/

lemma locallyIntegrable_dmsShift (γ : ℝ) (z : ℂ) : LocallyIntegrable (dmsShift γ z) := by
  have h1 : LocallyIntegrable (fun w : ℂ => Real.log ‖w - z‖) :=
    locallyIntegrable_comp_sub_of_integrableOn_ball (f := fun y : ℂ => Real.log ‖y‖)
      integrableOn_ball_log_norm z
  have h2 : LocallyIntegrable (fun w : ℂ => Real.log (max ‖w‖ 1)) := by
    apply Continuous.locallyIntegrable
    exact (continuous_norm.max continuous_const).log
      (fun w => (lt_max_of_lt_right zero_lt_one).ne')
  have hfun : dmsShift γ z = fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max ‖w‖ 1) := rfl
  rw [hfun]
  exact (h1.smul (-γ)).add (h2.smul γ)

lemma circleAverage_const_mul_fun (c : ℝ) (f : ℂ → ℝ) (w : ℂ) (r : ℝ) :
    Real.circleAverage (fun y => c * f y) w r = c * Real.circleAverage f w r := by
  simp only [Real.circleAverage_def, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- **Literal circle average of `dmsShift`.** For every centre `w` (including circles through `z`)
and radius `r > 0`, `⨍_{∂B(w,r)} dmsShift γ z = -γ log max(r, |w - z|) + γ ⨍_{∂B(w,r)} logMaxOne`. -/
theorem circleAverage_dmsShift (γ : ℝ) (z w : ℂ) {r : ℝ} (hr : 0 < r) :
    Real.circleAverage (dmsShift γ z) w r =
      -γ * Real.log (max r ‖w - z‖) + γ * Real.circleAverage logMaxOne w r := by
  have hlog : CircleIntegrable (fun y : ℂ => Real.log ‖y - z‖) w r :=
    circleIntegrable_log_norm_sub_const r
  have hlog' : CircleIntegrable (fun y : ℂ => -γ * Real.log ‖y - z‖) w r := by
    unfold CircleIntegrable at hlog ⊢
    exact hlog.const_mul (-γ)
  have hmax : CircleIntegrable (fun y : ℂ => γ * logMaxOne y) w r := by
    have h : CircleIntegrable logMaxOne w r := continuous_logMaxOne.continuousOn.circleIntegrable hr.le
    unfold CircleIntegrable at h ⊢
    exact h.const_mul γ
  have hfun : dmsShift γ z = fun y => -γ * Real.log ‖y - z‖ + γ * logMaxOne y := by
    funext y
    rw [dmsShift, logMaxOne, max_comm ‖y‖ 1]
  rw [hfun, Real.circleAverage_fun_add hlog' hmax, circleAverage_const_mul_fun,
    circleAverage_const_mul_fun,
    HarmonicBalls.CirclePotential.circleAverage_log_norm_sub_eq_log_max hr, norm_sub_rev z w]

/-- **Instance: `dmsShift γ z` against a fixed test.** -/
theorem tendsto_integral_dmsShift_circleAverage_mul (φ : ℂ → ℝ) (hφ : IsTestFunction univ φ)
    (γ : ℝ) (z : ℂ) :
    Tendsto (fun r : ℝ => ∫ w, Real.circleAverage (dmsShift γ z) w r * φ w) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ v, dmsShift γ z v * φ v)) :=
  tendsto_integral_circleAverage_mul (locallyIntegrable_dmsShift γ z) hφ

/-- **Logarithmic instance with the literal formula.** The circle averages are replaced by
`-γ log (max r ‖w - z‖) + γ ⨍ logMaxOne`, and the limit against `φ` is unchanged. -/
theorem tendsto_integral_dmsShift_literal (φ : ℂ → ℝ) (hφ : IsTestFunction univ φ) (γ : ℝ)
    (z : ℂ) :
    Tendsto (fun r : ℝ => ∫ w, (-γ * Real.log (max r ‖w - z‖)
        + γ * Real.circleAverage logMaxOne w r) * φ w) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ v, dmsShift γ z v * φ v)) := by
  refine Tendsto.congr' ?_ (tendsto_integral_dmsShift_circleAverage_mul φ hφ γ z)
  filter_upwards [self_mem_nhdsWithin] with r hr
  congr 1
  funext w
  rw [circleAverage_dmsShift γ z w hr]

end HarmonicBalls.CircleTestFubini
