import HarmonicBalls.Proofs.Sec11.LQGBaseMetricObservable
import HarmonicBalls.Proofs.Sec11.NormalizedBaseMetric
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly
import HarmonicBalls.Proofs.Sec8.ConcentricCircleCovariance
import HarmonicBalls.Proofs.GFF.CoordinateModification
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Fixed distance law and circle fluctuations for the LQG metric

The whole-plane GFF construction used in the intended sign argument is due to
Leonardo Bonanno. These lemmas hold for any realization of that field.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

/-- A fixed evaluation of the base metric has a realization-independent law. -/
theorem IsWholePlaneGFF.identDistrib_baseMetric_value
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P' hC' hcirc')
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (z w : ℂ) :
    IdentDistrib (fun ω => 𝔇 (hC ω) z w) (fun ω => 𝔇 (hC' ω) z w) P P' := by
  obtain ⟨F, hF, hF_eq⟩ :=
    exists_common_observable_of_distribution_measurable (fun T => 𝔇 T z w)
      (h𝔇.measurable_apply z w)
  have hd := (h.identDistrib_observables_across_spaces h').comp hF
  have heq : (F ∘ fun ω o => o.1.eval (hC ω) (hcirc ω)) =
      (fun ω => 𝔇 (hC ω) z w) := funext fun ω => hF_eq _ _
  have heq' : (F ∘ fun ω o => o.1.eval (hC' ω) (hcirc' ω)) =
      (fun ω => 𝔇 (hC' ω) z w) := funext fun ω => hF_eq _ _
  rw [heq, heq'] at hd
  exact hd

/-- Each normalized affine field gives the same distance law as the original field. -/
theorem IsWholePlaneGFF.identDistrib_normalized_affine_baseMetric_value
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {r : ℝ} (hr : 0 < r) (z w : ℂ) :
    IdentDistrib (fun ω => 𝔇 (affinePairing hC hcirc (r : ℂ) 0 ω) z w)
      (fun ω => 𝔇 (hC ω) z w) P P := by
  have hg := (wholePlaneGFFAffineInvariance_proved P hC hcirc) h (r : ℂ)
    (by exact_mod_cast hr.ne') 0
  exact hg.identDistrib_baseMetric_value h 𝔇 h𝔇 z w

/-- A sequence with a fixed real law, divided by `n`, converges to zero in
probability. No independence between the variables is required. -/
theorem tendstoInMeasure_div_nat_of_identDistrib
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : ℕ → Ω → ℝ} {G : Ω → ℝ}
    (hFG : ∀ n, IdentDistrib (F n) G P P) :
    TendstoInMeasure P (fun (n : ℕ) ω => F n ω / (n : ℝ)) atTop (fun _ => 0) := by
  have hg : AEStronglyMeasurable G P := (hFG 0).aemeasurable_snd.aestronglyMeasurable
  have ht : TendstoInMeasure P (fun (n : ℕ) ω => G ω / (n : ℝ)) atTop (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact (hg.aemeasurable.div_const _).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  rw [tendstoInMeasure_iff_dist] at ht ⊢
  intro ε hε
  have heq : (fun n : ℕ => P {ω | ε ≤ dist (F n ω / (n : ℝ)) 0}) =
      (fun n : ℕ => P {ω | ε ≤ dist (G ω / (n : ℝ)) 0}) := by
    funext n
    let S : Set ℝ := {x | ε ≤ dist (x / (n : ℝ)) 0}
    have hS : MeasurableSet S := isClosed_le continuous_const
      ((continuous_id.div_const _).dist continuous_const) |>.measurableSet
    exact (hFG n).measure_mem_eq hS
  rw [heq]
  exact ht ε hε

/-- The logarithm of the normalized affine distance, divided by `n`, tends to
zero in probability by its fixed law. -/
theorem IsWholePlaneGFF.log_normalized_affine_baseMetric_div_nat_tendstoInMeasure_zero
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    TendstoInMeasure P (fun (n : ℕ) ω =>
      Real.log (𝔇 (affinePairing hC hcirc (Real.exp (-(n : ℝ)) : ℂ) 0 ω) 0 1) / (n : ℝ))
      atTop (fun _ => 0) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  apply tendstoInMeasure_div_nat_of_identDistrib
  intro n
  have hd := (h.identDistrib_normalized_affine_baseMetric_value 𝔇 h𝔇
    (Real.exp_pos (-(n : ℝ))) 0 1).comp Real.measurable_log
  exact hd

#print axioms tendstoInMeasure_div_nat_of_identDistrib
#print axioms IsWholePlaneGFF.log_normalized_affine_baseMetric_div_nat_tendstoInMeasure_zero

/-- A fixed law that converges in probability to zero is concentrated at zero. -/
theorem ae_eq_zero_of_identDistrib_tendstoInMeasure_zero
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : ℕ → Ω → ℝ} {G : Ω → ℝ}
    (hFG : ∀ n, IdentDistrib (F n) G P P)
    (hF : TendstoInMeasure P F atTop (fun _ => 0)) : ∀ᵐ ω ∂P, G ω = 0 := by
  have hg : AEStronglyMeasurable G P := (hFG 0).aemeasurable_snd.aestronglyMeasurable
  have hG : TendstoInMeasure P (fun _ : ℕ => G) atTop (fun _ => 0) := by
    rw [tendstoInMeasure_iff_dist] at hF ⊢
    intro ε hε
    have heq : (fun n : ℕ => P {ω | ε ≤ dist (F n ω) 0}) =
        (fun _ : ℕ => P {ω | ε ≤ dist (G ω) 0}) := by
      funext n
      let S : Set ℝ := {x | ε ≤ dist x 0}
      have hS : MeasurableSet S := (isClosed_le continuous_const
        (continuous_id.dist continuous_const)).measurableSet
      exact (hFG n).measure_mem_eq hS
    rw [← heq]
    exact hF ε hε
  have hGG : TendstoInMeasure P (fun _ : ℕ => G) atTop G := by
    apply tendstoInMeasure_of_tendsto_ae (fun _ => hg)
    exact Filter.Eventually.of_forall fun _ => tendsto_const_nhds
  exact tendstoInMeasure_ae_unique hGG hG

#print axioms ae_eq_zero_of_identDistrib_tendstoInMeasure_zero

/-- The circle average at radius `exp (-n)` has second moment `n`. -/
theorem IsWholePlaneGFF.integral_sq_circle_exp_neg_nat
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (n : ℕ) :
    (∫ ω, (hcirc ω (Real.exp (-(n : ℝ))) 0) ^ 2 ∂P) = (n : ℝ) := by
  have heq : (∫ ω, (hcirc ω (Real.exp (-(n : ℝ))) 0) ^ 2 ∂P) =
      ∫ ω, (hcirc ω (Real.exp (-(n : ℝ))) 0 - hcirc ω 1 0) ^ 2 ∂P := by
    apply integral_congr_ae
    filter_upwards [h.ae_circleAverage_one_zero] with ω hω
    rw [hω, sub_zero]
  rw [heq, h.integral_sq_circle_sub_circle (Real.exp_pos _) zero_lt_one]
  simp only [Real.log_exp, Real.log_one, sub_zero, abs_neg, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- Concentric circle averages grow sublinearly in probability. -/
theorem IsWholePlaneGFF.circle_exp_neg_nat_div_nat_tendstoInMeasure_zero
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) :
    TendstoInMeasure P (fun (n : ℕ) ω => hcirc ω (Real.exp (-(n : ℝ))) 0 / (n : ℝ))
      atTop (fun _ => 0) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  let B : ℕ → Ω → ℝ := fun n ω => hcirc ω (Real.exp (-(n : ℝ))) 0
  have hlp (n : ℕ) : MemLp (B n) 2 P :=
    (h.hasGaussianLaw_circle (Real.exp_pos _) 0).memLp (by simp)
  have hmean (n : ℕ) : ∫ ω, B n ω ∂P = 0 := by
    simpa only [B, GFFObservable.eval] using
      h.integral_eq_zero (.circle (Real.exp (-(n : ℝ))) 0) (Real.exp_pos _)
  have hvar (n : ℕ) : variance (B n) P = n := by
    rw [variance_eq_integral (hlp n).aemeasurable, hmean n]
    simpa only [sub_zero, B] using h.integral_sq_circle_exp_neg_nat n
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / ε ^ 2) / n)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal
      (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hCheb := meas_ge_le_variance_div_sq (hlp n) (mul_pos hε hnR)
  rw [hmean n, hvar n] at hCheb
  simp only [sub_zero] at hCheb
  have hsets : {ω | ε ≤ dist (B n ω / (n : ℝ)) 0} =
      {ω | ε * n ≤ |B n ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_div, abs_of_pos hnR]
    exact le_div_iff₀ hnR
  change P {ω | ε ≤ dist (B n ω / (n : ℝ)) 0} ≤ _
  rw [hsets]
  refine hCheb.trans ?_
  apply le_of_eq
  congr 1
  field_simp [hε.ne', hnR.ne']

#print axioms IsWholePlaneGFF.circle_exp_neg_nat_div_nat_tendstoInMeasure_zero

/-- The base metric is strictly positive between distinct points almost surely. -/
theorem IsWholePlaneGFF.ae_baseMetric_value_pos
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {z w : ℂ} (hzw : z ≠ w) : ∀ᵐ ω ∂P, 0 < 𝔇 (hC ω) z w := by
  have hm := (h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) h
    (by intro ω; fun_prop) (by intro x; fun_prop)).ae_isEuclideanLengthMetric
  have hzero (T : (ℂ → ℝ) → ℝ) : addFunPairing T (fun _ => 0) = T := by
    funext φ
    simp [addFunPairing]
  simp only [hzero] at hm
  filter_upwards [hm] with ω hmω
  have hn : 0 ≤ 𝔇 (hC ω) z w := by
    have ht := hmω.triangle z w z
    rw [hmω.self_eq_zero, hmω.symm w z] at ht
    linarith
  exact lt_of_le_of_ne hn (Ne.symm (fun he => hzw (hmω.eq_of_eq_zero z w he)))

/-- At exponentially shrinking Euclidean radii, the base distance tends to zero. -/
theorem IsWholePlaneGFF.ae_baseMetric_exp_neg_nat_tendsto_zero
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => 𝔇 (hC ω) 0 (Real.exp (-(n : ℝ)) : ℂ))
      atTop (𝓝 0) := by
  have hm := (h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) h
    (by intro ω; fun_prop) (by intro x; fun_prop)).ae_isEuclideanLengthMetric
  have hzero (T : (ℂ → ℝ) → ℝ) : addFunPairing T (fun _ => 0) = T := by
    funext φ
    simp [addFunPairing]
  simp only [hzero] at hm
  have hr : Tendsto (fun n : ℕ => (Real.exp (-(n : ℝ)) : ℂ)) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
    exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp ht
  filter_upwards [hm] with ω hmω
  have hc := (hmω.continuous_pair.continuousAt (x := (0, 0))).tendsto
  have ht := hc.comp (tendsto_const_nhds.prodMk_nhds hr)
  simpa only [Function.comp_def, hmω.self_eq_zero] using ht

/-- The shrinking base distances also converge to zero in probability. -/
theorem IsWholePlaneGFF.baseMetric_exp_neg_nat_tendstoInMeasure_zero
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    TendstoInMeasure P (fun (n : ℕ) ω => 𝔇 (hC ω) 0 (Real.exp (-(n : ℝ)) : ℂ))
      atTop (fun _ => 0) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    exact (h.identDistrib_baseMetric_value h 𝔇 h𝔇 0
      (Real.exp (-(n : ℝ)) : ℂ)).aemeasurable_fst.aestronglyMeasurable
  · exact h.ae_baseMetric_exp_neg_nat_tendsto_zero 𝔇 h𝔇

#print axioms IsWholePlaneGFF.baseMetric_exp_neg_nat_tendstoInMeasure_zero

/-- The distance at radius `exp (-n)` in terms of the normalized affine field. -/
theorem IsWholePlaneGFF.ae_baseMetric_exp_neg_nat_eq
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) (n : ℕ) :
    ∀ᵐ ω ∂P,
      𝔇 (hC ω) 0 (Real.exp (-(n : ℝ)) : ℂ) =
        Real.exp (ξ * (hcirc ω (Real.exp (-(n : ℝ))) 0 - lqgQ γ * n)) *
          𝔇 (affinePairing hC hcirc (Real.exp (-(n : ℝ)) : ℂ) 0 ω) 0 1 := by
  have hs := h.ae_normalized_affine_baseMetric
    (wholePlaneGFFAffineInvariance_proved P hC hcirc) 𝔇 h𝔇
    (Real.exp_pos (-(n : ℝ)))
  filter_upwards [hs] with ω hsω
  have hh := hsω 0 1
  simp only [smul_zero, Complex.real_smul, mul_one, Real.log_exp] at hh
  have hh' : 𝔇 (affinePairing hC hcirc (Real.exp (-(n : ℝ)) : ℂ) 0 ω) 0 1 =
      Real.exp (-(ξ * (hcirc ω (Real.exp (-(n : ℝ))) 0 - lqgQ γ * n))) *
        𝔇 (hC ω) 0 (Real.exp (-(n : ℝ)) : ℂ) := by
    convert hh using 1; congr 2; ring
  rw [hh', ← mul_assoc, ← Real.exp_add]
  simp

/-- The Weyl exponent is nonnegative, by the circle-average fluctuations and
the fixed law of the normalized affine metric. -/
theorem IsWholePlaneGFF.metric_weylExponent_nonneg
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) : 0 ≤ ξ := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hQ : 0 < lqgQ γ := by
    unfold lqgQ
    positivity
  let B : ℕ → Ω → ℝ := fun n ω => hcirc ω (Real.exp (-(n : ℝ))) 0
  let X : ℕ → Ω → ℝ := fun n ω => 𝔇 (hC ω) 0 (Real.exp (-(n : ℝ)) : ℂ)
  let Y : ℕ → Ω → ℝ := fun n ω =>
    𝔇 (affinePairing hC hcirc (Real.exp (-(n : ℝ)) : ℂ) 0 ω) 0 1
  obtain ⟨s, hs, hBs⟩ := (h.circle_exp_neg_nat_div_nat_tendstoInMeasure_zero).exists_seq_tendsto_ae'
  obtain ⟨t, ht, hYt⟩ := ((h.log_normalized_affine_baseMetric_div_nat_tendstoInMeasure_zero
    𝔇 h𝔇).comp hs).exists_seq_tendsto_ae'
  have hgood : ∀ᵐ ω ∂P, ∀ n, 0 < Y n ω := by
    apply ae_all_iff.mpr
    intro n
    have hg := (wholePlaneGFFAffineInvariance_proved P hC hcirc) h
      (Real.exp (-(n : ℝ)) : ℂ) (by exact_mod_cast (Real.exp_pos (-(n : ℝ))).ne') 0
    exact hg.ae_baseMetric_value_pos 𝔇 h𝔇 (by norm_num)
  have heq : ∀ᵐ ω ∂P, ∀ n, X n ω =
      Real.exp (ξ * (B n ω - lqgQ γ * n)) * Y n ω := by
    exact ae_all_iff.mpr (fun n => h.ae_baseMetric_exp_neg_nat_eq 𝔇 h𝔇 n)
  have hdist := h.ae_baseMetric_exp_neg_nat_tendsto_zero 𝔇 h𝔇
  have hall : ∀ᵐ ω ∂P, 0 ≤ ξ := by
    filter_upwards [hBs, hYt, hgood, heq, hdist] with ω hB hY hYpos he hX
    let u : ℕ → ℕ := fun n => s (t n)
    have hu : Tendsto u atTop atTop := hs.comp ht
    have hb : Tendsto (fun n => B (u n) ω / (u n : ℝ)) atTop (𝓝 0) := hB.comp ht
    have hy : Tendsto (fun n => Real.log (Y (u n) ω) / (u n : ℝ)) atTop (𝓝 0) := hY
    have hx : Tendsto (fun n => X (u n) ω) atTop (𝓝 0) := hX.comp hu
    have hn : ∀ᶠ n in atTop, (u n : ℝ) ≠ 0 := by
      filter_upwards [hu.eventually (eventually_gt_atTop 0)] with n hn
      exact_mod_cast hn.ne'
    have hlog : ∀ᶠ n in atTop,
        Real.log (X (u n) ω) / (u n : ℝ) =
          ξ * (B (u n) ω / (u n : ℝ) - lqgQ γ) +
            Real.log (Y (u n) ω) / (u n : ℝ) := by
      filter_upwards [hn] with n hn
      rw [he (u n), Real.log_mul (Real.exp_ne_zero _) (hYpos (u n)).ne', Real.log_exp]
      field_simp
    have hlim : Tendsto (fun n => Real.log (X (u n) ω) / (u n : ℝ)) atTop
        (𝓝 (-ξ * lqgQ γ)) := by
      have hh := ((tendsto_const_nhds (x := ξ)).mul (hb.sub (tendsto_const_nhds (x := lqgQ γ)))).add hy
      have hh' : Tendsto (fun n => ξ * (B (u n) ω / (u n : ℝ) - lqgQ γ) +
          Real.log (Y (u n) ω) / (u n : ℝ)) atTop (𝓝 (-ξ * lqgQ γ)) := by
        convert hh using 1; simp
      exact hh'.congr' (hlog.mono fun _ heq => heq.symm)
    have hnonpos : ∀ᶠ n in atTop, Real.log (X (u n) ω) / (u n : ℝ) ≤ 0 := by
      filter_upwards [hx.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
      have hxpos : 0 < X (u n) ω := by rw [he]; exact mul_pos (Real.exp_pos _) (hYpos _)
      exact div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hxpos.le hn.le) (Nat.cast_nonneg _)
    have hle : -ξ * lqgQ γ ≤ 0 := le_of_tendsto hlim hnonpos
    nlinarith
  exact hall.exists.choose_spec

#print axioms IsWholePlaneGFF.metric_weylExponent_nonneg

/-- The Weyl exponent of a whole-plane LQG metric cannot vanish. -/
theorem IsWholePlaneGFF.metric_weylExponent_ne_zero
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) : ξ ≠ 0 := by
  intro hξ
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  let X : ℕ → Ω → ℝ := fun n ω => 𝔇 (hC ω) 0 (Real.exp (-(n : ℝ)) : ℂ)
  let Y : ℕ → Ω → ℝ := fun n ω =>
    𝔇 (affinePairing hC hcirc (Real.exp (-(n : ℝ)) : ℂ) 0 ω) 0 1
  let G : Ω → ℝ := fun ω => 𝔇 (hC ω) 0 1
  have hXY (n : ℕ) : X n =ᵐ[P] Y n := by
    filter_upwards [h.ae_baseMetric_exp_neg_nat_eq 𝔇 h𝔇 n] with ω hω
    simpa only [X, Y, hξ, zero_mul, Real.exp_zero, one_mul] using hω
  have hLaw (n : ℕ) : IdentDistrib (X n) G P P := by
    have hm := (h.identDistrib_baseMetric_value h 𝔇 h𝔇 0
      (Real.exp (-(n : ℝ)) : ℂ)).aemeasurable_fst
    exact (IdentDistrib.of_ae_eq hm (hXY n)).trans
      (h.identDistrib_normalized_affine_baseMetric_value 𝔇 h𝔇 (Real.exp_pos _) 0 1)
  have hzero : ∀ᵐ ω ∂P, G ω = 0 :=
    ae_eq_zero_of_identDistrib_tendstoInMeasure_zero hLaw
      (h.baseMetric_exp_neg_nat_tendstoInMeasure_zero 𝔇 h𝔇)
  have hpos : ∀ᵐ ω ∂P, 0 < G ω :=
    h.ae_baseMetric_value_pos 𝔇 h𝔇 (by norm_num)
  have : ∀ᵐ ω ∂P, False := by
    filter_upwards [hzero, hpos] with ω hz hp
    linarith
  exact this.exists.elim (fun _ hfalse => hfalse)

#print axioms IsWholePlaneGFF.metric_weylExponent_ne_zero

/-- The Weyl exponent in the whole-plane LQG metric axioms is positive when
`γ` is positive. Leonardo Bonanno's GFF construction supplies the realization. -/
theorem IsLQGMetric.weylExponent_pos
    {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hγ : 0 < γ) : 0 < ξ := by
  obtain ⟨Ω, m, P, hP, hC, hcirc, h⟩ := exists_projectWholePlaneGFF
  let : MeasurableSpace Ω := m
  let : IsProbabilityMeasure P := hP
  exact lt_of_le_of_ne (h.metric_weylExponent_nonneg hγ 𝔇 h𝔇)
    (Ne.symm (h.metric_weylExponent_ne_zero 𝔇 h𝔇))

#print axioms IsLQGMetric.weylExponent_pos

#print axioms IsWholePlaneGFF.ae_baseMetric_exp_neg_nat_eq
#print axioms IsWholePlaneGFF.ae_baseMetric_value_pos
#print axioms IsWholePlaneGFF.ae_baseMetric_exp_neg_nat_tendsto_zero
#print axioms IsWholePlaneGFF.integral_sq_circle_exp_neg_nat
#print axioms IsWholePlaneGFF.identDistrib_baseMetric_value
#print axioms IsWholePlaneGFF.identDistrib_normalized_affine_baseMetric_value

end HarmonicBalls
