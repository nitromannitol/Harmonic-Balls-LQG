import HarmonicBalls.Proofs.Potential.GreenPotentialHolder
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Diagonal exceptional set for logarithmic potentials

The potential-theoretic infrastructure used here is due to Leonardo Bonanno.
The upper volume-growth estimate excludes atoms on bounded restrictions. Fubini
then removes the atoms of an arbitrary finite measure at almost every point.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- Upper volume growth excludes atoms on the bounded restriction. -/
theorem restrict_ball_singleton_eq_zero_of_upper {μ : Measure ℂ} {R r₀ β : ℝ}
    (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hfin : μ (ball (0 : ℂ) R) ≠ ⊤) (x : ℂ) :
    μ.restrict (ball 0 R) {x} = 0 := by
  by_cases hx : x ∈ closedBall (0 : ℂ) R
  · apply measure_singleton_eq_zero_of_le_rpow hβ
    intro r hr
    exact restrict_ball_closedBall_le hR hr₀ hβ hup hfin hx hr
  · rw [Measure.restrict_apply (measurableSet_singleton x)]
    have : ({x} ∩ ball (0 : ℂ) R) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      have : y = x := hy.1
      subst y
      exact hx (ball_subset_closedBall hy.2)
    rw [this, measure_empty]

/-- A finite measure has no atom at almost every point of an atomless bounded restriction. -/
theorem ae_measure_singleton_eq_zero_of_upper {μ ν : Measure ℂ} [IsFiniteMeasure ν]
    {R r₀ β : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hfin : μ (ball (0 : ℂ) R) ≠ ⊤) :
    ∀ᵐ x ∂μ.restrict (ball 0 R), ν {x} = 0 := by
  let ρ := μ.restrict (ball 0 R)
  have : IsFiniteMeasure ρ := isFiniteMeasure_restrict.2 hfin
  have hd : (ν.prod ρ) (Set.diagonal ℂ) = 0 := by
    apply Measure.measure_prod_null_of_ae_null measurableSet_diagonal
    filter_upwards [] with x
    simpa [Set.diagonal, ρ] using restrict_ball_singleton_eq_zero_of_upper hR hr₀ hβ hup hfin x
  have hd' : (ρ.prod ν) (Set.diagonal ℂ) = 0 := by
    rw [← Measure.prod_swap, Measure.map_apply measurable_swap measurableSet_diagonal]
    simpa [Set.diagonal, eq_comm] using hd
  have h := Measure.measure_ae_null_of_prod_null hd'
  filter_upwards [h] with x hx
  simpa [Set.diagonal] using hx

/-- Uniform integrability and a quantitative bound for the Riesz kernel on a bounded
restriction, uniformly over poles in the corresponding closed ball. -/
theorem riesz_integrable_restrict_ball_of_upper {μ : Measure ℂ} {R r₀ β : ℝ}
    (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hfin : μ (ball (0 : ℂ) R) ≠ ⊤) {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) R) :
    Integrable (fun y => ‖x - y‖ ^ (-greenPotentialHolderExponent β)) (μ.restrict (ball 0 R)) ∧
    (∫ y, ‖x - y‖ ^ (-greenPotentialHolderExponent β) ∂μ.restrict (ball 0 R)) ≤
      greenPotentialRieszBound β r₀ (μ (ball (0 : ℂ) R)).toReal := by
  have hm : 0 ≤ (μ (ball (0 : ℂ) R)).toReal := ENNReal.toReal_nonneg
  have hν : μ.restrict (ball 0 R) univ ≤ ENNReal.ofReal (μ (ball (0 : ℂ) R)).toReal := by
    rw [Measure.restrict_apply_univ, ENNReal.ofReal_toReal hfin]
  apply integrable_norm_sub_rpow_neg (greenPotentialRieszBound_nonneg hβ hr₀ hm)
  exact lintegral_norm_sub_rpow_neg_le (greenPotentialHolderExponent_pos hβ)
    (greenPotentialHolderExponent_lt hβ) hm (volumeGrowthAllScalesConstant_nonneg hr₀ hm) hν
    (fun r hr => restrict_ball_closedBall_le hR hr₀ hβ hup hfin hx hr)

/-- Product integrability of the Riesz kernel for finite measures restricted to a
closed ball and a measure satisfying the upper growth bound on that ball. -/
theorem riesz_integrable_product_of_upper {μ ν : Measure ℂ} [IsFiniteMeasure ν]
    {R r₀ β : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hfin : μ (ball (0 : ℂ) R) ≠ ⊤) :
    Integrable (fun p : ℂ × ℂ => ‖p.1 - p.2‖ ^ (-greenPotentialHolderExponent β))
      ((ν.restrict (closedBall 0 R)).prod (μ.restrict (ball 0 R))) := by
  have : IsFiniteMeasure (μ.restrict (ball 0 R)) := isFiniteMeasure_restrict.2 hfin
  let f : ℂ × ℂ → ℝ := fun p => ‖p.1 - p.2‖ ^ (-greenPotentialHolderExponent β)
  have hf : Measurable f := by fun_prop
  apply (integrable_prod_iff hf.aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    exact (riesz_integrable_restrict_ball_of_upper hR hr₀ hβ hup hfin hx).1
  · apply Integrable.mono' (integrable_const (greenPotentialRieszBound β r₀
        (μ (ball (0 : ℂ) R)).toReal))
      (hf.norm.aestronglyMeasurable.integral_prod_right')
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    have hi := riesz_integrable_restrict_ball_of_upper hR hr₀ hβ hup hfin hx
    have hn : (fun y => ‖f (x, y)‖) = fun y => f (x, y) := by
      funext y
      simp only [f, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    rw [hn, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y =>
      Real.rpow_nonneg (norm_nonneg _) _)]
    exact hi.2

/-- On a bounded interval the absolute logarithm is controlled by a negative power.
The value at zero is the real logarithm's conventional value. -/
theorem abs_log_le_rpow_of_bounded {t B α : ℝ} (ht : 0 ≤ t) (hB : t ≤ B)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    |Real.log t| ≤ α⁻¹ * (B + 1) ^ α * (t ^ (-α) + 1) := by
  have hB0 : 0 ≤ B := ht.trans hB
  have hC : 0 ≤ α⁻¹ * (B + 1) ^ α :=
    mul_nonneg (inv_nonneg.mpr hα.le) (Real.rpow_nonneg (by linarith) _)
  by_cases hz : t = 0
  · subst t
    simp only [Real.log_zero, abs_zero, Real.zero_rpow (neg_ne_zero.mpr hα.ne'), zero_add]
    exact mul_nonneg hC zero_le_one
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
    have hdiff : |t - 1| ≤ B + 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hp := Real.rpow_le_rpow (abs_nonneg (t - 1)) hdiff hα.le
    have htneg : 0 ≤ t ^ (-α) + 1 := by positivity
    calc |Real.log t| = |Real.log t - Real.log 1| := by rw [Real.log_one, sub_zero]
      _ ≤ α⁻¹ * |t - 1| ^ α * (t ^ (-α) + 1 ^ (-α)) :=
        abs_log_sub_log_le htpos zero_lt_one hα hα1
      _ = α⁻¹ * |t - 1| ^ α * (t ^ (-α) + 1) := by rw [Real.one_rpow]
      _ ≤ α⁻¹ * (B + 1) ^ α * (t ^ (-α) + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hα.le)) htneg

/-- The logarithmic kernel is integrable for the two bounded restrictions. -/
theorem log_integrable_product_of_upper {μ ν : Measure ℂ} [IsFiniteMeasure ν]
    {R r₀ β : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hfin : μ (ball (0 : ℂ) R) ≠ ⊤) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖)
      ((ν.restrict (closedBall 0 R)).prod (μ.restrict (ball 0 R))) := by
  have : IsFiniteMeasure (μ.restrict (ball 0 R)) := isFiniteMeasure_restrict.2 hfin
  let α := greenPotentialHolderExponent β
  let C := α⁻¹ * (2 * R + 1) ^ α
  have hα : 0 < α := greenPotentialHolderExponent_pos hβ
  have hriesz := riesz_integrable_product_of_upper (ν := ν) hR hr₀ hβ hup hfin
  have hbound : Integrable (fun p : ℂ × ℂ => C * (‖p.1 - p.2‖ ^ (-α) + 1))
      ((ν.restrict (closedBall 0 R)).prod (μ.restrict (ball 0 R))) :=
    (hriesz.add (integrable_const 1)).const_mul C
  have hmeas : Measurable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) := by fun_prop
  apply hbound.mono' hmeas.aestronglyMeasurable
  have ha : ∀ᵐ p ∂(ν.restrict (closedBall (0 : ℂ) R)).prod (μ.restrict (ball 0 R)),
      p.1 ∈ closedBall (0 : ℂ) R ∧ p.2 ∈ ball (0 : ℂ) R := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_closedBall.prod measurableSet_ball)).2
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact ⟨hx, hy⟩
  filter_upwards [ha] with p hp
  have hx : ‖p.1‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hp.1
  have hy : ‖p.2‖ ≤ R := by
    have := ball_subset_closedBall hp.2
    simpa [mem_closedBall, dist_eq_norm] using this
  have hd : ‖p.1 - p.2‖ ≤ 2 * R := (norm_sub_le _ _).trans (by linarith)
  simpa only [Real.norm_eq_abs] using
    abs_log_le_rpow_of_bounded (norm_nonneg (p.1 - p.2)) hd hα
      (greenPotentialHolderExponent_le_one β)

/-- The real logarithmic kernel is integrable at almost every point of the
bounded restriction, against any finite measure concentrated on the closed ball. -/
theorem ae_integrable_newtonKernel_of_upper {μ ν : Measure ℂ} [IsFiniteMeasure ν]
    {R r₀ β : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hfin : μ (ball (0 : ℂ) R) ≠ ⊤)
    (hν : ∀ᵐ y ∂ν, y ∈ closedBall (0 : ℂ) R) :
    ∀ᵐ x ∂μ.restrict (ball 0 R), Integrable (newtonKernel x) ν := by
  have : IsFiniteMeasure (μ.restrict (ball 0 R)) := isFiniteMeasure_restrict.2 hfin
  have hprod := (log_integrable_product_of_upper (ν := ν) hR hr₀ hβ hup hfin).swap
  have hre : ν.restrict (closedBall (0 : ℂ) R) = ν := Measure.restrict_eq_self_of_ae_mem hν
  rw [hre] at hprod
  filter_upwards [hprod.prod_right_ae] with x hx
  have hx' := hx.const_mul (-(2 * Real.pi)⁻¹)
  convert hx' using 1
  funext y
  simp only [newtonKernel, Function.comp_apply, Prod.swap_prod_mk]
  rw [norm_sub_rev]

/-- The exceptional-set conclusion on a smaller ball, using growth on a ball
large enough to contain both the smaller ball and the support of the measure. -/
theorem ae_newtonKernel_and_atom_of_upper {μ ν : Measure ℂ} [IsFiniteMeasure ν]
    {s R r₀ β : ℝ} (hsR : s ≤ R) (hR : 0 < R) (hr₀ : 0 < r₀) (hβ : 0 < β)
    (hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hfin : μ (ball (0 : ℂ) R) ≠ ⊤)
    (hν : ∀ᵐ y ∂ν, y ∈ closedBall (0 : ℂ) R) :
    ∀ᵐ x ∂μ.restrict (ball 0 s), Integrable (newtonKernel x) ν ∧ ν {x} = 0 := by
  apply Filter.Eventually.filter_mono (ae_mono (Measure.restrict_mono
    (ball_subset_ball hsR) le_rfl))
  filter_upwards [ae_integrable_newtonKernel_of_upper (ν := ν) hR hr₀ hβ hup hfin hν,
    ae_measure_singleton_eq_zero_of_upper (ν := ν) hR hr₀ hβ hup hfin] with x hi hn
  exact ⟨hi, hn⟩

/-- A uniform lower bound for the Newtonian kernel on a bounded product,
off the diagonal. -/
theorem newtonKernel_lower_bound_of_closedBall {R : ℝ} {x y : ℂ}
    (hx : x ∈ closedBall (0 : ℂ) R) (hy : y ∈ closedBall (0 : ℂ) R) (hxy : x ≠ y) :
    -(2 * Real.pi)⁻¹ * Real.log (2 * R) ≤ newtonKernel x y := by
  have hx' : ‖x‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hx
  have hy' : ‖y‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hy
  have hd : ‖x - y‖ ≤ 2 * R := (norm_sub_le x y).trans (by linarith)
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  unfold newtonKernel
  exact mul_le_mul_of_nonpos_left (Real.log_le_log hpos hd)
    (neg_nonpos.mpr (inv_nonneg.mpr (mul_nonneg (by norm_num) Real.pi_pos.le)))

/-- Signed extended-real integral, defined as the difference of the lower integrals
of the positive and negative parts. It is used when both parts are finite. -/
noncomputable def extendedSignedIntegral (f : ℂ → EReal) (ν : Measure ℂ) : EReal :=
  ((∫⁻ y, (f y).toENNReal ∂ν : ℝ≥0∞) : EReal) -
    ((∫⁻ y, (-f y).toENNReal ∂ν : ℝ≥0∞) : EReal)

/-- At a non-atomic pole where the real kernel is integrable, its signed
extended-real integral is finite and agrees with the real Bochner integral. -/
theorem extendedSignedIntegral_newtonKernel_eq {ν : Measure ℂ} {x : ℂ}
    (hatom : ν {x} = 0) (hi : Integrable (newtonKernel x) ν) :
    extendedSignedIntegral (newtonKernelEReal x) ν = (∫ y, newtonKernel x y ∂ν : ℝ) := by
  have hae : ∀ᵐ y ∂ν, y ≠ x := by
    apply ae_iff.mpr
    simpa using hatom
  have hp : (∫⁻ y, (newtonKernelEReal x y).toENNReal ∂ν) =
      ENNReal.ofReal (∫ y, max (newtonKernel x y) 0 ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi.pos_part (ae_of_all _ fun y => le_max_right _ _)]
    apply lintegral_congr_ae
    filter_upwards [hae] with y hy
    simp [newtonKernelEReal, hy, EReal.toENNReal, ENNReal.ofReal_max]
  have hn : (∫⁻ y, (-newtonKernelEReal x y).toENNReal ∂ν) =
      ENNReal.ofReal (∫ y, max (-newtonKernel x y) 0 ∂ν) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi.neg_part (ae_of_all _ fun y => le_max_right _ _)]
    apply lintegral_congr_ae
    filter_upwards [hae] with y hy
    simp [newtonKernelEReal, hy, ← EReal.coe_neg, EReal.toENNReal, ENNReal.ofReal_max]
  rw [extendedSignedIntegral, hp, hn, EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal]
  have hp0 : 0 ≤ ∫ y, max (newtonKernel x y) 0 ∂ν := integral_nonneg fun _ => le_max_right _ _
  have hn0 : 0 ≤ ∫ y, max (-newtonKernel x y) 0 ∂ν := integral_nonneg fun _ => le_max_right _ _
  rw [max_eq_left hp0, max_eq_left hn0, ← EReal.coe_sub,
    integral_eq_integral_pos_part_sub_integral_neg_part hi]
  simp only [Real.coe_toNNReal']

/-- Both parts of the signed extended-real integral are finite at a non-atomic
pole with integrable real kernel. -/
theorem newtonKernelEReal_parts_lt_top {ν : Measure ℂ} {x : ℂ}
    (hatom : ν {x} = 0) (hi : Integrable (newtonKernel x) ν) :
    (∫⁻ y, (newtonKernelEReal x y).toENNReal ∂ν) < ⊤ ∧
    (∫⁻ y, (-newtonKernelEReal x y).toENNReal ∂ν) < ⊤ := by
  have hae : ∀ᵐ y ∂ν, y ≠ x := ae_iff.mpr (by simpa using hatom)
  constructor
  · calc
      (∫⁻ y, (newtonKernelEReal x y).toENNReal ∂ν) =
          ∫⁻ y, ENNReal.ofReal (max (newtonKernel x y) 0) ∂ν := by
            apply lintegral_congr_ae
            filter_upwards [hae] with y hy
            simp [newtonKernelEReal, hy, EReal.toENNReal, ENNReal.ofReal_max]
      _ = ENNReal.ofReal (∫ y, max (newtonKernel x y) 0 ∂ν) :=
        (ofReal_integral_eq_lintegral_ofReal hi.pos_part (ae_of_all _ fun y => le_max_right _ _)).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  · calc
      (∫⁻ y, (-newtonKernelEReal x y).toENNReal ∂ν) =
          ∫⁻ y, ENNReal.ofReal (max (-newtonKernel x y) 0) ∂ν := by
            apply lintegral_congr_ae
            filter_upwards [hae] with y hy
            simp [newtonKernelEReal, hy, ← EReal.coe_neg, EReal.toENNReal, ENNReal.ofReal_max]
      _ = ENNReal.ofReal (∫ y, max (-newtonKernel x y) 0 ∂ν) :=
        (ofReal_integral_eq_lintegral_ofReal hi.neg_part (ae_of_all _ fun y => le_max_right _ _)).symm
      _ < ⊤ := ENNReal.ofReal_lt_top

/-- Local positive-power upper growth removes the logarithmic nonintegrability
and diagonal exceptional sets for a finite measure concentrated on a compact set.
The extended-real signed potential is the finite real Bochner potential there. -/
theorem ae_logPotential_of_local_upper_growth {μ ν : Measure ℂ}
    [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {K : Set ℂ} (hK : IsCompact K) (hν : ν Kᶜ = 0) (s : ℝ) :
    ∀ᵐ x ∂μ.restrict (ball 0 s),
      Integrable (newtonKernel x) ν ∧ ν {x} = 0 ∧
      (∫⁻ y, (newtonKernelEReal x y).toENNReal ∂ν) < ⊤ ∧
      (∫⁻ y, (-newtonKernelEReal x y).toENNReal ∂ν) < ⊤ ∧
      extendedSignedIntegral (newtonKernelEReal x) ν = (∫ y, newtonKernel x y ∂ν : ℝ) := by
  obtain ⟨a, ha⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  let R := max (max s a) 1
  have hsR : s ≤ R := (le_max_left s a).trans (le_max_left _ _)
  have haR : a ≤ R := (le_max_right s a).trans (le_max_left _ _)
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨r₀, β, hr₀, hβ, hg⟩ := hup R hR
  have hνR : ∀ᵐ y ∂ν, y ∈ closedBall (0 : ℂ) R := by
    have hνK : ∀ᵐ y ∂ν, y ∈ K := by
      apply ae_iff.mpr
      exact hν
    filter_upwards [hνK] with y hy
    exact closedBall_subset_closedBall haR (ha hy)
  filter_upwards [ae_newtonKernel_and_atom_of_upper hsR hR hr₀ hβ hg
    (measure_ball_lt_top (μ := μ)).ne hνR] with x hx
  exact ⟨hx.1, hx.2, (newtonKernelEReal_parts_lt_top hx.2 hx.1).1,
    (newtonKernelEReal_parts_lt_top hx.2 hx.1).2, extendedSignedIntegral_newtonKernel_eq hx.2 hx.1⟩

/-- The same exceptional-set result under the repository's volume-growth
condition on every positive-radius ball. -/
theorem ae_logPotential_of_volumeGrowth {μ ν : Measure ℂ}
    [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ R : ℝ, 0 < R → ∃ βminus βplus, VolumeGrowth μ R βminus βplus)
    {K : Set ℂ} (hK : IsCompact K) (hν : ν Kᶜ = 0) (s : ℝ) :
    ∀ᵐ x ∂μ.restrict (ball 0 s),
      Integrable (newtonKernel x) ν ∧ ν {x} = 0 ∧
      (∫⁻ y, (newtonKernelEReal x y).toENNReal ∂ν) < ⊤ ∧
      (∫⁻ y, (-newtonKernelEReal x y).toENNReal ∂ν) < ⊤ ∧
      extendedSignedIntegral (newtonKernelEReal x) ν = (∫ y, newtonKernel x y ∂ν : ℝ) := by
  apply ae_logPotential_of_local_upper_growth ?_ hK hν s
  intro R hR
  obtain ⟨βminus, βplus, _, hβ, r₀, hr₀, hg⟩ := hμ R hR
  exact ⟨r₀, βplus, hr₀, hβ, fun r hr hr₀' z hz => (hg r hr hr₀' z hz).2⟩


end HarmonicBalls
