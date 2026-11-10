import Mathlib
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.Notation
import HarmonicBalls.Proposed.LQG

/-! # Step 12, singular measure identity (FirstPass S11q, worker n1)

Source: Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795), Section 2.2
(Fact 2.1 I and III, printed p. 9), as organised in `notes/fp-gaps/CHATGPT-n3-step12-gaps.md`, sections 1-2.
The field `h = h^ℂ - α₀ log |·|` has circle averages `fieldCircleAverage α₀ (hcirc ω)` (`Defs/GFF.lean`).
The inputs are the Proposed Props `LQGMeasureWeylScaling` (Fact 2.1 III, used at insertion `0`) and
`LQGMeasureNonatomic` (Fact 2.1 I, at insertions `0` and `α₀`), used as explicit hypotheses.
Nothing else is assumed: the singular identity is proved here from the continuous Weyl scaling by truncating the
logarithm at scale `δ/2`, where it agrees with the paper's `-α₀ log |·|` on `{|z| ≥ δ}`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The singular weight `|z|^(-γ α₀)` of eq. (1) of the Step 12 note, with value `1` at `z = 0`
(Lean's convention `Real.log 0 = 0`; the point `0` is Lebesgue-null and `μ`-null by nonatomicity). -/
noncomputable def LQGSingularWeight (γ α₀ : ℝ) (z : ℂ) : ℝ :=
  Real.exp (-(γ * α₀) * Real.log ‖z‖)

/-- The truncated logarithmic potential `x ↦ -α₀ log max(‖x‖, m)`. It is continuous for `m > 0` and equals
`-α₀ log ‖x‖` on `{‖x‖ ≥ m}`. -/
noncomputable def truncLogWeight (α₀ m : ℝ) (x : ℂ) : ℝ :=
  -α₀ * Real.log (max ‖x‖ m)

lemma continuous_truncLogWeight (α₀ : ℝ) {m : ℝ} (hm : 0 < m) :
    Continuous (truncLogWeight α₀ m) := by
  unfold truncLogWeight
  refine Continuous.mul continuous_const (Continuous.log (by fun_prop) fun x => ?_)
  exact (lt_of_lt_of_le hm (le_max_right _ _)).ne'

/-- Circle average of the truncated potential, for a circle lying in `{‖x‖ ≥ m}`: it equals
`-α₀ log max(r, |z|)` (Armitage-Gardiner, mean value property of `log |·|`). -/
lemma circleAverage_truncLogWeight {α₀ m r : ℝ} {z : ℂ} (hr : 0 < r) (hm : m ≤ ‖z‖ - r) :
    Real.circleAverage (truncLogWeight α₀ m) z r = -α₀ * Real.log (max r ‖z‖) := by
  have hcongr : Real.circleAverage (truncLogWeight α₀ m) z r
      = Real.circleAverage (fun x => -α₀ * Real.log ‖x‖) z r := by
    refine Real.circleAverage_congr_sphere fun x hx => ?_
    rw [mem_sphere, abs_of_pos hr, dist_eq_norm] at hx
    have h2 := norm_sub_norm_le z x
    rw [norm_sub_rev] at h2
    have h3 : m ≤ ‖x‖ := by linarith
    simp only [truncLogWeight, max_eq_left h3]
  have hfun : (fun x : ℂ => -α₀ * Real.log ‖x‖) = (-α₀) • (fun x : ℂ => Real.log ‖x‖) := by
    funext x
    simp [smul_eq_mul]
  rw [hcongr, hfun, Real.circleAverage_smul, smul_eq_mul, circleAverage_log_norm hr z]

/-- On a circle at radius `r ≤ ‖z‖ - m`, the circle average of the whole-plane field plus the truncated potential
is the circle average of `h = h^ℂ - α₀ log |·|`. -/
lemma addCircleAverage_truncLogWeight_eq {α₀ m : ℝ} (hc : ℝ → ℂ → ℝ) {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hm : m ≤ ‖z‖ - r) :
    addCircleAverage (fieldCircleAverage 0 hc) (truncLogWeight α₀ m) r z
      = fieldCircleAverage α₀ hc r z := by
  simp only [addCircleAverage, fieldCircleAverage, zero_mul, sub_zero]
  rw [circleAverage_truncLogWeight hr hm, circleAverage_log_norm hr z]
  ring

/-- The two densities of `LQGMeasureWeylScaling` (truncation at `δ/2`) and of `LQGSingularWeight` agree on
`{‖z‖ ≥ δ}`. -/
lemma ofReal_exp_truncLogWeight_eq {γ α₀ δ : ℝ} {z : ℂ} (hz : δ ≤ ‖z‖) (hδ : 0 < δ) :
    ENNReal.ofReal (Real.exp (γ * truncLogWeight α₀ (δ / 2) z))
      = ENNReal.ofReal (LQGSingularWeight γ α₀ z) := by
  simp only [LQGSingularWeight, truncLogWeight]
  rw [max_eq_left (show δ / 2 ≤ ‖z‖ by linarith)]
  rw [show γ * (-α₀ * Real.log ‖z‖) = -(γ * α₀) * Real.log ‖z‖ by ring]

/-! ### Restriction of densities which agree on a set

Only the values on `S` matter when the integrand vanishes off `S`. No measurability of the densities is needed. -/

lemma withDensity_restrict_eq_of_eqOn {μ : Measure ℂ} {f g : ℂ → ℝ≥0∞} {S : Set ℂ}
    (hS : MeasurableSet S) (hfg : ∀ z ∈ S, f z = g z) :
    (μ.withDensity f).restrict S = (μ.withDensity g).restrict S := by
  rw [restrict_withDensity hS, restrict_withDensity hS]
  exact withDensity_congr_ae (ae_restrict_of_forall_mem hS hfg)

lemma lintegral_withDensity_eq_of_eqOn {μ : Measure ℂ} {f g : ℂ → ℝ≥0∞} {S : Set ℂ}
    (hS : MeasurableSet S) (hfg : ∀ z ∈ S, f z = g z) {F : ℂ → ℝ≥0∞} (hF : ∀ z, z ∉ S → F z = 0) :
    ∫⁻ z, F z ∂(μ.withDensity f) = ∫⁻ z, F z ∂(μ.withDensity g) := by
  have h1 : ∀ ν : Measure ℂ, ∫⁻ z, F z ∂ν = ∫⁻ z in S, F z ∂ν := fun ν =>
    (setLIntegral_eq_of_support_subset (fun z hz => by
      by_contra h
      exact hz (hF z h))).symm
  rw [h1 (μ.withDensity f), h1 (μ.withDensity g)]
  show ∫⁻ z, F z ∂((μ.withDensity f).restrict S) = ∫⁻ z, F z ∂((μ.withDensity g).restrict S)
  rw [withDensity_restrict_eq_of_eqOn hS hfg]

lemma integral_withDensity_eq_of_eqOn {μ : Measure ℂ} {f g : ℂ → ℝ≥0∞} {S : Set ℂ}
    (hS : MeasurableSet S) (hfg : ∀ z ∈ S, f z = g z) {φ : ℂ → ℝ} (hφ : ∀ z, z ∉ S → φ z = 0) :
    ∫ z, φ z ∂(μ.withDensity f) = ∫ z, φ z ∂(μ.withDensity g) := by
  have h1 : ∀ ν : Measure ℂ, ∫ z, φ z ∂ν = ∫ z in S, φ z ∂ν := fun ν =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => hφ z hz)).symm
  rw [h1 (μ.withDensity f), h1 (μ.withDensity g)]
  show ∫ z, φ z ∂((μ.withDensity f).restrict S) = ∫ z, φ z ∂((μ.withDensity g).restrict S)
  rw [withDensity_restrict_eq_of_eqOn hS hfg]

/-- The regularised measure `ε^{γ²/2} e^{γ h_ε} dz` (`lqgApprox`) only depends on the circle averages on
`{‖z‖ ≥ δ}`, as far as test functions vanishing on `{‖z‖ < δ}` are concerned. -/
lemma integral_lqgApprox_eq_of_eqOn {γ δ ε : ℝ} {H H' : ℝ → ℂ → ℝ}
    (hHH : ∀ z, δ ≤ ‖z‖ → H ε z = H' ε z) {φ : ℂ → ℝ} (hφ : ∀ z, ‖z‖ < δ → φ z = 0) :
    ∫ z, φ z ∂(lqgApprox γ H ε) = ∫ z, φ z ∂(lqgApprox γ H' ε) := by
  unfold lqgApprox
  refine integral_withDensity_eq_of_eqOn (measurableSet_le measurable_const measurable_norm)
    (fun z hz => ?_) (fun z hz => hφ z (not_le.mp hz))
  simp only [hHH z hz]

/-! ### Step A: the identity for test functions vanishing near `0` -/

/-- For a fixed sample point `ω` (`hc` the circle averages of `h^ℂ`), integrals of test functions vanishing on
`{‖z‖ < δ}` agree for `μα` (insertion `α₀`) and `μ₀ · |z|^(-γα₀)`. Both sides come from the vague limits along the
dyadic scales: the truncated potential `-α₀ log max(|·|, δ/2)` is continuous and agrees with the circle averages of
`h` on the circles that matter. -/
lemma integral_singular_eq {γ α₀ δ : ℝ} (hδ : 0 < δ) (hc : ℝ → ℂ → ℝ) (μα μ₀ : Measure ℂ)
    (hα : IsLQGLimit γ (fieldCircleAverage α₀ hc) μα)
    (hW : IsLQGLimit γ (addCircleAverage (fieldCircleAverage 0 hc) (truncLogWeight α₀ (δ / 2)))
      (μ₀.withDensity fun x => ENNReal.ofReal (Real.exp (γ * truncLogWeight α₀ (δ / 2) x))))
    {φ : ℂ → ℝ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφ : ∀ z, ‖z‖ < δ → φ z = 0) :
    ∫ z, φ z ∂μα = ∫ z, φ z ∂(μ₀.withDensity fun x => ENNReal.ofReal (LQGSingularWeight γ α₀ x)) := by
  have hm : 0 < δ / 2 := by positivity
  have hev : ∀ᶠ k : ℕ in atTop, dyadicScale k < δ / 2 := by
    have h0 : Tendsto (fun k : ℕ => dyadicScale k) atTop (𝓝 0) := by
      unfold dyadicScale
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    exact h0.eventually (gt_mem_nhds hm)
  have heq : (fun k : ℕ => ∫ z, φ z ∂(lqgApprox γ (fieldCircleAverage α₀ hc) (dyadicScale k)))
      =ᶠ[atTop] (fun k : ℕ => ∫ z, φ z ∂(lqgApprox γ
        (addCircleAverage (fieldCircleAverage 0 hc) (truncLogWeight α₀ (δ / 2))) (dyadicScale k))) := by
    filter_upwards [hev] with k hk
    refine integral_lqgApprox_eq_of_eqOn (fun z hz => ?_) hφ
    rw [addCircleAverage_truncLogWeight_eq (α₀ := α₀) (m := δ / 2) (z := z) hc (dyadicScale_pos k)
      (by linarith)]
  have hlim := tendsto_nhds_unique_of_eventuallyEq (hα.tendsto_integral φ hφc hφs)
    (hW.tendsto_integral φ hφc hφs) heq
  rw [hlim]
  exact integral_withDensity_eq_of_eqOn (measurableSet_le measurable_const measurable_norm)
    (fun z hz => ofReal_exp_truncLogWeight_eq hz hδ) (fun z hz => hφ z (not_le.mp hz))

/-- Lintegral form of Step A for nonnegative test functions vanishing on `{‖z‖ < δ}`. -/
lemma lintegral_singular_eq_of_vanish {γ α₀ δ : ℝ} (hδ : 0 < δ) (hc : ℝ → ℂ → ℝ) (μα μ₀ : Measure ℂ)
    (hα : IsLQGLimit γ (fieldCircleAverage α₀ hc) μα)
    (hW : IsLQGLimit γ (addCircleAverage (fieldCircleAverage 0 hc) (truncLogWeight α₀ (δ / 2)))
      (μ₀.withDensity fun x => ENNReal.ofReal (Real.exp (γ * truncLogWeight α₀ (δ / 2) x))))
    {F : ℂ → ℝ} (hFc : Continuous F) (hFs : HasCompactSupport F) (hF0 : ∀ z, 0 ≤ F z)
    (hFδ : ∀ z, ‖z‖ < δ → F z = 0) :
    ∫⁻ z, ENNReal.ofReal (F z) ∂μα
      = ∫⁻ z, ENNReal.ofReal (F z)
          ∂(μ₀.withDensity fun x => ENNReal.ofReal (LQGSingularWeight γ α₀ x)) := by
  have := hα.isLocallyFiniteMeasure
  have := hW.isLocallyFiniteMeasure
  have hS : MeasurableSet {z : ℂ | δ ≤ ‖z‖} := measurableSet_le measurable_const measurable_norm
  have hB := integral_singular_eq hδ hc μα μ₀ hα hW hFc hFs hFδ
  have hint : Integrable F μα := hFc.integrable_of_hasCompactSupport hFs
  have hintW : Integrable F (μ₀.withDensity fun x => ENNReal.ofReal (Real.exp (γ * truncLogWeight α₀ (δ / 2) x))) :=
    hFc.integrable_of_hasCompactSupport hFs
  have hFS : ∀ z, z ∉ {z : ℂ | δ ≤ ‖z‖} → F z = 0 := fun z hz => hFδ z (not_le.mp hz)
  have hfg : ∀ z ∈ {z : ℂ | δ ≤ ‖z‖},
      ENNReal.ofReal (LQGSingularWeight γ α₀ z)
        = ENNReal.ofReal (Real.exp (γ * truncLogWeight α₀ (δ / 2) z)) :=
    fun z hz => (ofReal_exp_truncLogWeight_eq hz hδ).symm
  have hlW : ∫⁻ z, ENNReal.ofReal (F z) ∂(μ₀.withDensity fun x => ENNReal.ofReal (LQGSingularWeight γ α₀ x))
      = ∫⁻ z, ENNReal.ofReal (F z)
          ∂(μ₀.withDensity fun x => ENNReal.ofReal (Real.exp (γ * truncLogWeight α₀ (δ / 2) x))) :=
    lintegral_withDensity_eq_of_eqOn hS hfg (fun z hz => by simp [hFS z hz])
  have hBW : ∫ z, F z ∂(μ₀.withDensity fun x => ENNReal.ofReal (LQGSingularWeight γ α₀ x))
      = ∫ z, F z ∂(μ₀.withDensity fun x => ENNReal.ofReal (Real.exp (γ * truncLogWeight α₀ (δ / 2) x))) :=
    integral_withDensity_eq_of_eqOn hS hfg hFS
  have hfinμ : ∫⁻ z, ENNReal.ofReal (F z) ∂μα = ENNReal.ofReal (∫ z, F z ∂μα) :=
    (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hF0)).symm
  have hfinW : ∫⁻ z, ENNReal.ofReal (F z)
        ∂(μ₀.withDensity fun x => ENNReal.ofReal (Real.exp (γ * truncLogWeight α₀ (δ / 2) x)))
      = ENNReal.ofReal (∫ z, F z
        ∂(μ₀.withDensity fun x => ENNReal.ofReal (Real.exp (γ * truncLogWeight α₀ (δ / 2) x)))) :=
    (ofReal_integral_eq_lintegral_ofReal hintW (ae_of_all _ hF0)).symm
  rw [hlW, hfinμ, hfinW, hB, hBW]

/-! ### Step B: cut-offs and extension to all nonnegative test functions -/

/-- Cut-off `g_n(z) = min 1 (max 0 ((n+1)|z| - 1))`: `0` on `{|z| ≤ 1/(n+1)}`, `1` on `{|z| ≥ 2/(n+1)}`. -/
noncomputable def cutoffN (n : ℕ) (z : ℂ) : ℝ :=
  min 1 (max 0 (((n : ℝ) + 1) * ‖z‖ - 1))

lemma continuous_cutoffN (n : ℕ) : Continuous (cutoffN n) := by
  unfold cutoffN
  fun_prop

lemma cutoffN_nonneg (n : ℕ) (z : ℂ) : 0 ≤ cutoffN n z :=
  le_min zero_le_one (le_max_left _ _)

lemma cutoffN_le_one (n : ℕ) (z : ℂ) : cutoffN n z ≤ 1 :=
  min_le_left _ _

lemma cutoffN_zero_of_lt {n : ℕ} {z : ℂ} (hz : ‖z‖ < 1 / ((n : ℝ) + 1)) : cutoffN n z = 0 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h : ((n : ℝ) + 1) * ‖z‖ - 1 ≤ 0 := by
    have := (lt_div_iff₀ hpos).mp hz
    nlinarith
  unfold cutoffN
  rw [max_eq_left h, min_eq_right zero_le_one]

lemma cutoffN_mono (z : ℂ) : Monotone (fun n : ℕ => cutoffN n z) := by
  intro a b hab
  have hab' : ((a : ℝ) + 1) ≤ ((b : ℝ) + 1) := by
    have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    linarith
  unfold cutoffN
  exact min_le_min_left _ (max_le_max le_rfl (by nlinarith [norm_nonneg z]))

lemma cutoffN_tendsto {z : ℂ} (hz : z ≠ 0) : Tendsto (fun n : ℕ => cutoffN n z) atTop (𝓝 1) := by
  have ht : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * ‖z‖) atTop atTop :=
    Tendsto.atTop_mul_const ht (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have h2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ ((n : ℝ) + 1) * ‖z‖ := h1.eventually_ge_atTop 2
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [h2] with n hn
  unfold cutoffN
  rw [max_eq_right (show (0 : ℝ) ≤ ((n : ℝ) + 1) * ‖z‖ - 1 by linarith),
    min_eq_left (show (1 : ℝ) ≤ ((n : ℝ) + 1) * ‖z‖ - 1 by linarith)]

/-- The identity of Step A extended to all nonnegative continuous compactly supported test functions (lintegral form);
the cut-offs `cutoffN n` tend to `1` off `0`, and both measures vanish at `0`. -/
lemma lintegral_singular_eq {γ α₀ : ℝ} (hc : ℝ → ℂ → ℝ) (μα μ₀ : Measure ℂ)
    (hα : IsLQGLimit γ (fieldCircleAverage α₀ hc) μα)
    (hW : ∀ f : ℂ → ℝ, Continuous f →
      IsLQGLimit γ (addCircleAverage (fieldCircleAverage 0 hc) f)
        (μ₀.withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))))
    (hN0 : ∀ x : ℂ, μ₀ {x} = 0) (hNα : ∀ x : ℂ, μα {x} = 0)
    {F : ℂ → ℝ} (hFc : Continuous F) (hFs : HasCompactSupport F) (hF0 : ∀ z, 0 ≤ F z) :
    ∫⁻ z, ENNReal.ofReal (F z) ∂μα
      = ∫⁻ z, ENNReal.ofReal (F z)
          ∂(μ₀.withDensity fun x => ENNReal.ofReal (LQGSingularWeight γ α₀ x)) := by
  set ν := μ₀.withDensity fun x => ENNReal.ofReal (LQGSingularWeight γ α₀ x) with hν
  have hν0 : ν {0} = 0 := (withDensity_absolutelyContinuous μ₀ _) (hN0 0)
  have hae : ∀ᵐ z ∂μα, z ≠ 0 := by
    rw [ae_iff]
    simpa using hNα 0
  have hae' : ∀ᵐ z ∂ν, z ≠ 0 := by
    rw [ae_iff]
    simpa using hν0
  have hcut : ∀ n : ℕ, ∫⁻ z, ENNReal.ofReal (F z * cutoffN n z) ∂μα
      = ∫⁻ z, ENNReal.ofReal (F z * cutoffN n z) ∂ν := by
    intro n
    have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact lintegral_singular_eq_of_vanish hδ hc μα μ₀ hα (hW _ (continuous_truncLogWeight α₀ (by positivity)))
      (hFc.mul (continuous_cutoffN n)) (hFs.mul_right) (fun z => mul_nonneg (hF0 z) (cutoffN_nonneg n z))
      (fun z hz => by simp [cutoffN_zero_of_lt hz])
  have hmono : ∀ z, Monotone (fun n : ℕ => ENNReal.ofReal (F z * cutoffN n z)) := fun z a b hab =>
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (cutoffN_mono z hab) (hF0 z))
  have hlim : ∀ {m : Measure ℂ}, (∀ᵐ z ∂m, z ≠ 0) →
      Tendsto (fun n : ℕ => ∫⁻ z, ENNReal.ofReal (F z * cutoffN n z) ∂m) atTop
        (𝓝 (∫⁻ z, ENNReal.ofReal (F z) ∂m)) := by
    intro m hm
    refine lintegral_tendsto_of_tendsto_of_monotone (fun n => ?_) (ae_of_all _ fun z => hmono z) ?_
    · exact (ENNReal.measurable_ofReal.comp ((hFc.mul (continuous_cutoffN n)).measurable)).aemeasurable
    · filter_upwards [hm] with z hz
      have := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := F z)).mul (cutoffN_tendsto hz))
      rwa [mul_one] at this
  have hμl := hlim hae
  have hνl := hlim hae'
  have hfun : (fun n : ℕ => ∫⁻ z, ENNReal.ofReal (F z * cutoffN n z) ∂μα)
      = (fun n : ℕ => ∫⁻ z, ENNReal.ofReal (F z * cutoffN n z) ∂ν) := funext hcut
  rw [hfun] at hμl
  exact tendsto_nhds_unique hμl hνl

/-! ### Local finiteness, measure equality, and identity (1)-(2) -/

/-- The bump `z ↦ max 0 (min 1 (R + 1 - ‖z‖))`: `1` on `closedBall 0 R`, `0` off `closedBall 0 (R+1)`. -/
noncomputable def bumpBall (R : ℝ) (z : ℂ) : ℝ :=
  max 0 (min 1 (R + 1 - ‖z‖))

lemma continuous_bumpBall (R : ℝ) : Continuous (bumpBall R) := by
  unfold bumpBall
  fun_prop

lemma bumpBall_nonneg (R : ℝ) (z : ℂ) : 0 ≤ bumpBall R z := le_max_left _ _

lemma bumpBall_le_one (R : ℝ) (z : ℂ) : bumpBall R z ≤ 1 := max_le zero_le_one (min_le_left _ _)

lemma one_le_bumpBall {R : ℝ} {z : ℂ} (hz : ‖z‖ ≤ R) : 1 ≤ bumpBall R z := by
  unfold bumpBall
  rw [min_eq_left (show (1 : ℝ) ≤ R + 1 - ‖z‖ by linarith)]
  exact le_max_right _ _

lemma bumpBall_eq_zero {R : ℝ} {z : ℂ} (hz : R + 1 < ‖z‖) : bumpBall R z = 0 := by
  unfold bumpBall
  rw [min_eq_right (show R + 1 - ‖z‖ ≤ 1 by linarith), max_eq_left (show R + 1 - ‖z‖ ≤ 0 by linarith)]

/-- The singular measure `μ₀ · |z|^(-γα₀)` is locally finite, given the Weyl scaling of `μ₀` at all continuous
weights and the nonatomicity of both measures. -/
lemma isFiniteMeasureOnCompacts_singular {γ α₀ : ℝ} (hc : ℝ → ℂ → ℝ) (μα μ₀ : Measure ℂ)
    (hα : IsLQGLimit γ (fieldCircleAverage α₀ hc) μα)
    (hW : ∀ f : ℂ → ℝ, Continuous f →
      IsLQGLimit γ (addCircleAverage (fieldCircleAverage 0 hc) f)
        (μ₀.withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))))
    (hN0 : ∀ x : ℂ, μ₀ {x} = 0) (hNα : ∀ x : ℂ, μα {x} = 0) :
    IsFiniteMeasureOnCompacts (μ₀.withDensity fun x => ENNReal.ofReal (LQGSingularWeight γ α₀ x)) := by
  have := hα.isLocallyFiniteMeasure
  constructor
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine lt_of_le_of_lt (measure_mono hR) ?_
  have hsupp : HasCompactSupport (bumpBall R) :=
    HasCompactSupport.intro (isCompact_closedBall 0 (R + 1)) (fun z hz =>
      bumpBall_eq_zero (not_le.mp fun h => hz (mem_closedBall_zero_iff.mpr h)))
  have h1 : (μ₀.withDensity fun x => ENNReal.ofReal (LQGSingularWeight γ α₀ x)) (closedBall 0 R)
      ≤ ∫⁻ z, ENNReal.ofReal (bumpBall R z)
          ∂(μ₀.withDensity fun x => ENNReal.ofReal (LQGSingularWeight γ α₀ x)) := by
    calc (μ₀.withDensity fun x => ENNReal.ofReal (LQGSingularWeight γ α₀ x)) (closedBall 0 R)
        = ∫⁻ z in closedBall 0 R, (1 : ℝ≥0∞)
            ∂(μ₀.withDensity fun x => ENNReal.ofReal (LQGSingularWeight γ α₀ x)) := by simp
      _ ≤ ∫⁻ z in closedBall 0 R, ENNReal.ofReal (bumpBall R z)
            ∂(μ₀.withDensity fun x => ENNReal.ofReal (LQGSingularWeight γ α₀ x)) :=
          setLIntegral_mono' measurableSet_closedBall (fun z hz => by
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (one_le_bumpBall (mem_closedBall_zero_iff.mp hz)))
      _ ≤ _ := setLIntegral_le_lintegral _ _
  have h2 := lintegral_singular_eq hc μα μ₀ hα hW hN0 hNα (continuous_bumpBall R) hsupp (bumpBall_nonneg R)
  have h3 : ∫⁻ z, ENNReal.ofReal (bumpBall R z) ∂μα ≤ μα (closedBall 0 (R + 1)) := by
    calc ∫⁻ z, ENNReal.ofReal (bumpBall R z) ∂μα
        ≤ ∫⁻ z, (closedBall (0 : ℂ) (R + 1)).indicator 1 z ∂μα := lintegral_mono (fun z => by
          by_cases hz : ‖z‖ ≤ R + 1
          · rw [Set.indicator_of_mem (mem_closedBall_zero_iff.mpr hz), Pi.one_apply]
            exact ENNReal.ofReal_le_one.mpr (bumpBall_le_one R z)
          · rw [Set.indicator_of_notMem (fun h => hz (mem_closedBall_zero_iff.mp h)),
              bumpBall_eq_zero (not_le.mp hz), ENNReal.ofReal_zero])
      _ = μα (closedBall 0 (R + 1)) := lintegral_indicator_one measurableSet_closedBall
  have h4 : μα (closedBall 0 (R + 1)) < ⊤ := (isCompact_closedBall 0 (R + 1)).measure_lt_top
  exact lt_of_le_of_lt (h1.trans (le_of_eq h2.symm |>.trans h3)) h4

/-- Two locally finite measures on `ℂ` with equal lintegrals of nonnegative test functions agree; the singular
measure is locally finite by `isFiniteMeasureOnCompacts_singular`. -/
lemma singular_measure_of_ω {γ α₀ : ℝ} (hc : ℝ → ℂ → ℝ) (μα μ₀ : Measure ℂ)
    (hα : IsLQGLimit γ (fieldCircleAverage α₀ hc) μα)
    (hW : ∀ f : ℂ → ℝ, Continuous f →
      IsLQGLimit γ (addCircleAverage (fieldCircleAverage 0 hc) f)
        (μ₀.withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))))
    (hN0 : ∀ x : ℂ, μ₀ {x} = 0) (hNα : ∀ x : ℂ, μα {x} = 0) :
    μα = μ₀.withDensity fun x => ENNReal.ofReal (LQGSingularWeight γ α₀ x) := by
  have := hα.isLocallyFiniteMeasure
  have := isFiniteMeasureOnCompacts_singular hc μα μ₀ hα hW hN0 hNα
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro f
  have hFc : Continuous (fun z => (f z : ℝ)) := NNReal.continuous_coe.comp f.continuous
  have hFs : HasCompactSupport (fun z => (f z : ℝ)) := f.hasCompactSupport.comp_left NNReal.coe_zero
  have hF0 : ∀ z, 0 ≤ (f z : ℝ) := fun z => NNReal.coe_nonneg _
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hF0) hFc.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hF0) hFc.aestronglyMeasurable]
  congr 1
  exact lintegral_singular_eq hc μα μ₀ hα hW hN0 hNα hFc hFs hF0

/-- **Identity (1) of the Step 12 note** (HB Fact 2.1 I and III, printed p. 9; no freeze). For `0 < γ < 2` and
`α₀ < Q`, almost surely `μ_{α₀} = |z|^(-γα₀) μ₀` as Radon measures on `ℂ` (`LQGSingularWeight`), where `μ₀` is the
LQG measure of the whole-plane field without insertion and `μ_{α₀}` the one with insertion `α₀`. The inputs are
the Proposed Props `LQGMeasureWeylScaling` (at insertion `0`) and `LQGMeasureNonatomic` (at `0` and `α₀`). -/
theorem singular_measure_identity {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (P : Measure Ω) (hGFF : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hWeyl : LQGMeasureWeylScaling P γ 0 hC hcirc) (hNa0 : LQGMeasureNonatomic P γ 0 hC hcirc)
    (hNa : LQGMeasureNonatomic P γ α₀ hC hcirc)
    {μ₀ μα : Ω → Measure ℂ} (h₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (hμα : IsLQGMeasureOfField P γ α₀ hcirc μα) :
    ∀ᵐ ω ∂P, μα ω = (μ₀ ω).withDensity (fun z => ENNReal.ofReal (LQGSingularWeight γ α₀ z)) := by
  have hQ0 : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hW := hWeyl hGFF hγ0 hγ2 hQ0 μ₀ h₀
  have hN0 := hNa0 hGFF hγ0 hγ2 hQ0 μ₀ h₀
  have hNα := hNa hGFF hγ0 hγ2 hα μα hμα
  have hA : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μα ω) := hμα
  filter_upwards [hW, hN0, hNα, hA] with ω hWω hN0ω hNαω hAω
  exact singular_measure_of_ω (hcirc ω) (μα ω) (μ₀ ω) hAω hWω hN0ω hNαω

/-! ### Section 7: coordinate identities under dilation (gaps note section 7.1)

For `R > 0` the dilated field `h^{(R)}` of eq. (35) has circle averages `h^{(R)}_r(z) = h_{Rr}(Rz) - h_R(0)`, and its
normalisation constant is `c_R = h_R(0) + Q log R` (eq. (31)). The identity below is an exact change of variables in the
regularised densities; it does not need `LQGMeasureCoordChange`. -/

/-- Circle averages `h^{(R)}_r(z) = h_{Rr}(Rz) - h_R(0)` of the dilated field (eq. (35)); `H r z = h_r(z)`. -/
noncomputable def dilatedCircleAverage (H : ℝ → ℂ → ℝ) (R : ℝ) : ℝ → ℂ → ℝ :=
  fun r z => H (R * r) (R * z) - H R 0

/-- The normalisation constant `c_R = h_R(0) + Q log R` of eq. (31), with `Q = lqgQ γ`. -/
noncomputable def dilationConstant (γ : ℝ) (H : ℝ → ℂ → ℝ) (R : ℝ) : ℝ :=
  H R 0 + lqgQ γ * Real.log R

lemma gamma_mul_lqgQ {γ : ℝ} (hγ : 0 < γ) : γ * lqgQ γ = 2 + γ ^ 2 / 2 := by
  unfold lqgQ
  field_simp

/-- Exponent bookkeeping: `ε^{γ²/2} e^{-γ h} R^{-2} = e^{-γ (h + Q log R)} (Rε)^{γ²/2}`, using `γ Q = 2 + γ²/2`. -/
lemma dilate_exponent_identity {γ R ε h : ℝ} (hγ : 0 < γ) (hR : 0 < R) (hε : 0 < ε) :
    ε ^ (γ ^ 2 / 2) * Real.exp (-(γ * h)) * (R ^ 2)⁻¹
      = Real.exp (-(γ * (h + lqgQ γ * Real.log R))) * (R * ε) ^ (γ ^ 2 / 2) := by
  rw [Real.rpow_def_of_pos hε, Real.rpow_def_of_pos (mul_pos hR hε), Real.log_mul hR.ne' hε.ne']
  have hexp : Real.exp (Real.log R) = R := Real.exp_log hR
  have hR2 : (R ^ 2)⁻¹ = Real.exp (-(2 * Real.log R)) := by
    rw [Real.exp_neg, two_mul, Real.exp_add, hexp, sq]
  rw [hR2]
  simp only [← Real.exp_add]
  congr 1
  linear_combination (Real.log R) * gamma_mul_lqgQ hγ

/-- **Section 7.1 (measure identity, gaps note eq. (36)).** For `R > 0`, the regularised measure of the dilated field
`h^{(R)}` at scale `ε` is `e^{-γ c_R}` times the push-forward of the regularised measure of `h` at scale `Rε` under
`w ↦ w / R`, as an identity of integrals of arbitrary test functions `φ`. The only extra hypothesis is the
measurability of the circle averages `H (R ε)` in `z` (the integral form of `withDensity` needs it). -/
lemma integral_lqgApprox_dilate {γ R ε : ℝ} (H : ℝ → ℂ → ℝ) (hγ : 0 < γ) (hR : 0 < R) (hε : 0 < ε)
    (hmeas : Measurable (H (R * ε))) (φ : ℂ → ℝ) :
    ∫ z, φ z ∂(lqgApprox γ (dilatedCircleAverage H R) ε)
      = Real.exp (-(γ * dilationConstant γ H R)) * ∫ w, φ (w / R) ∂(lqgApprox γ H (R * ε)) := by
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hD1 : Measurable (fun z : ℂ => ENNReal.ofReal
      (ε ^ (γ ^ 2 / 2) * Real.exp (γ * (H (R * ε) ((R : ℂ) * z) - H R 0)))) := by
    have hm2 : Measurable (fun z : ℂ => H (R * ε) ((R : ℂ) * z)) :=
      hmeas.comp (measurable_const.mul measurable_id)
    fun_prop
  have hD2 : Measurable (fun w : ℂ => ENNReal.ofReal
      ((R * ε) ^ (γ ^ 2 / 2) * Real.exp (γ * H (R * ε) w))) := by
    fun_prop
  have h1 : ∫ z, φ z ∂(lqgApprox γ (dilatedCircleAverage H R) ε)
      = ∫ z, (ε ^ (γ ^ 2 / 2) * Real.exp (-(γ * H R 0)))
          * (Real.exp (γ * H (R * ε) ((R : ℂ) * z)) * φ z) := by
    unfold lqgApprox dilatedCircleAverage
    rw [integral_withDensity_eq_integral_toReal_smul hD1 (ae_of_all _ fun z => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le)]
    rw [show γ * (H (R * ε) ((R : ℂ) * z) - H R 0)
        = γ * H (R * ε) ((R : ℂ) * z) + -(γ * H R 0) by ring, Real.exp_add]
    ring
  have h2 : ∫ w, φ (w / R) ∂(lqgApprox γ H (R * ε))
      = (R * ε) ^ (γ ^ 2 / 2) * ∫ w, Real.exp (γ * H (R * ε) w) * φ (w / R) := by
    unfold lqgApprox
    rw [integral_withDensity_eq_integral_toReal_smul hD2 (ae_of_all _ fun z => ENNReal.ofReal_lt_top)]
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg (mul_pos hR hε).le _) (Real.exp_pos _).le)]
    ring
  -- change of variables `u = R • z` on the left-hand side
  set G : ℂ → ℝ := fun u => (ε ^ (γ ^ 2 / 2) * Real.exp (-(γ * H R 0)))
      * (Real.exp (γ * H (R * ε) u) * φ (u / R)) with hG
  have hL : ∫ z, φ z ∂(lqgApprox γ (dilatedCircleAverage H R) ε) = ∫ z, G (R • z) := by
    rw [h1]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [hG, Complex.real_smul, mul_div_cancel_left₀ _ hRC]
  have h3 := MeasureTheory.Measure.integral_comp_smul (μ := volume) G R
  have hfinrank : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  rw [hfinrank, abs_of_pos (inv_pos.mpr (pow_pos hR 2)), smul_eq_mul] at h3
  have hGint : ∫ u, G u = (ε ^ (γ ^ 2 / 2) * Real.exp (-(γ * H R 0)))
      * ∫ u, Real.exp (γ * H (R * ε) u) * φ (u / R) := integral_const_mul _ _
  have key := dilate_exponent_identity (h := H R 0) hγ hR hε
  rw [hL, h3, hGint, h2, dilationConstant]
  linear_combination (∫ u, Real.exp (γ * H (R * ε) u) * φ (u / R)) * key

/-- For a dyadic dilation `R = 2^k` the scales shift: `2^k · 2^{-j} = 2^{-(j-k)}` for `j ≥ k`. -/
lemma two_pow_mul_dyadicScale (k j : ℕ) (hkj : k ≤ j) :
    (2 : ℝ) ^ k * dyadicScale j = dyadicScale (j - k) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
  have h2 : (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  unfold dyadicScale
  rw [show k + d - k = d by omega, pow_add, ← mul_assoc, h2, one_mul]

/-- Along the dyadic scales the regularised measures of the dilated field `h^{(2^k)}` converge, to
`e^{-γ c_R} ∫ φ(·/R) dμ`, for every continuous compactly supported test function `φ`. -/
lemma tendsto_lqgApprox_dilate_dyadic {γ : ℝ} {H : ℝ → ℂ → ℝ} {m : Measure ℂ} (hm : IsLQGLimit γ H m)
    (hγ : 0 < γ) (k : ℕ) (hmeas : ∀ r : ℝ, 0 < r → Measurable (H r)) {φ : ℂ → ℝ}
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    Tendsto (fun j : ℕ => ∫ z, φ z ∂(lqgApprox γ (dilatedCircleAverage H ((2 : ℝ) ^ k)) (dyadicScale j)))
      atTop (𝓝 (Real.exp (-(γ * dilationConstant γ H ((2 : ℝ) ^ k))) * ∫ w, φ (w / ((2 : ℝ) ^ k : ℝ)) ∂m)) := by
  have hR : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  set R : ℝ := (2 : ℝ) ^ k with hRdef
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hψc : Continuous (fun w : ℂ => φ (w / R)) := hφc.comp (continuous_id.div_const _)
  have hψs : HasCompactSupport (fun w : ℂ => φ (w / R)) := by
    refine HasCompactSupport.intro
      ((hφs.isCompact.image (continuous_const.mul continuous_id : Continuous fun w : ℂ => (R : ℂ) * w)))
      (fun w hw => ?_)
    by_contra hne
    have hmem : w / R ∈ tsupport φ := subset_tsupport φ hne
    exact hw ⟨w / R, hmem, by show (R : ℂ) * (w / R) = w; field_simp⟩
  have hlimit := hm.tendsto_integral (fun w : ℂ => φ (w / R)) hψc hψs
  have hshift := hlimit.comp (tendsto_sub_atTop_nat k)
  refine Tendsto.congr' ?_ (tendsto_const_nhds.mul hshift)
  filter_upwards [eventually_ge_atTop k] with j hj
  simp only [Function.comp_apply]
  rw [integral_lqgApprox_dilate H hγ hR (dyadicScale_pos j) (hmeas _ (mul_pos hR (dyadicScale_pos j))) φ,
    two_pow_mul_dyadicScale k j hj]

/-- **Section 7.1 (limit form).** For the dyadic dilation `R = 2^k`, the dilated field `h^{(R)}` (circle averages
`dilatedCircleAverage H R`) has LQG limit `e^{-γ c_R} · (μ_h).map (· / R)`. This is the measure
`ENNReal.ofReal (e^{-γ c_R}) • (μ_h).map (w ↦ w/R)` of the gaps note, section 7.1; with `IsLQGLimit.unique` it identifies
the designated LQG measure of `h^{(R)}`. -/
lemma isLQGLimit_dilate_dyadic {γ : ℝ} {H : ℝ → ℂ → ℝ} {m : Measure ℂ} (hm : IsLQGLimit γ H m)
    (hγ : 0 < γ) (k : ℕ) (hmeas : ∀ r : ℝ, 0 < r → Measurable (H r)) :
    IsLQGLimit γ (dilatedCircleAverage H ((2 : ℝ) ^ k))
      (ENNReal.ofReal (Real.exp (-(γ * dilationConstant γ H ((2 : ℝ) ^ k))))
        • m.map (fun w : ℂ => w / (((2 : ℝ) ^ k : ℝ) : ℂ))) := by
  have := hm.isLocallyFiniteMeasure
  have hR : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hRC : (((2 : ℝ) ^ k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hdiv : Measurable (fun w : ℂ => w / (((2 : ℝ) ^ k : ℝ) : ℂ)) := by fun_prop
  let hom : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero ((((2 : ℝ) ^ k : ℝ) : ℂ)⁻¹) (inv_ne_zero hRC)
  have hfun : (fun w : ℂ => w / (((2 : ℝ) ^ k : ℝ) : ℂ)) = ⇑hom := by
    funext w
    show w / (((2 : ℝ) ^ k : ℝ) : ℂ) = (((2 : ℝ) ^ k : ℝ) : ℂ)⁻¹ • w
    rw [smul_eq_mul, div_eq_inv_mul]
  have hfin : IsFiniteMeasureOnCompacts (m.map (fun w : ℂ => w / (((2 : ℝ) ^ k : ℝ) : ℂ))) := by
    rw [hfun]
    exact MeasureTheory.Measure.IsFiniteMeasureOnCompacts.map m hom
  have : IsFiniteMeasureOnCompacts (ENNReal.ofReal (Real.exp (-(γ * dilationConstant γ H ((2 : ℝ) ^ k))))
      • m.map (fun w : ℂ => w / (((2 : ℝ) ^ k : ℝ) : ℂ))) :=
    IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top
  refine ⟨inferInstance, fun f hf hfs => ?_⟩
  rw [integral_smul_measure, integral_map hdiv.aemeasurable hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  exact tendsto_lqgApprox_dilate_dyadic hm hγ k hmeas hf hfs

/-- **Identity (2) of the Step 12 note**: on the same almost-sure event, `μ_{α₀} ≪ μ₀` and `μ₀ ≪ μ_{α₀}`
(the weight `|z|^(-γα₀)` is strictly positive, so the two measures have the same null sets). -/
theorem singular_measure_mutual_ac {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (P : Measure Ω) (hGFF : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hWeyl : LQGMeasureWeylScaling P γ 0 hC hcirc) (hNa0 : LQGMeasureNonatomic P γ 0 hC hcirc)
    (hNa : LQGMeasureNonatomic P γ α₀ hC hcirc)
    {μ₀ μα : Ω → Measure ℂ} (h₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (hμα : IsLQGMeasureOfField P γ α₀ hcirc μα) :
    ∀ᵐ ω ∂P, μα ω ≪ μ₀ ω ∧ μ₀ ω ≪ μα ω := by
  filter_upwards [singular_measure_identity P hGFF hγ0 hγ2 hα hWeyl hNa0 hNa h₀ hμα] with ω hω
  rw [hω]
  refine ⟨withDensity_absolutelyContinuous _ _, ?_⟩
  have hmeas : Measurable (fun x : ℂ => ENNReal.ofReal (LQGSingularWeight γ α₀ x)) := by
    unfold LQGSingularWeight
    fun_prop
  intro s hs
  have h := (withDensity_apply_eq_zero' hmeas.aemeasurable).mp hs
  have heq : {x : ℂ | ENNReal.ofReal (LQGSingularWeight γ α₀ x) ≠ 0} ∩ s = s := by
    refine Set.inter_eq_right.mpr fun x _ => ?_
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  rwa [heq] at h

end HarmonicBalls
