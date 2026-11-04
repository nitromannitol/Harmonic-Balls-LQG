import HarmonicBalls.Proofs.Sec9.CircleCovarianceDilation

/-! # Affine transformation of circle-average covariances -/

open MeasureTheory ProbabilityTheory Real
open scoped ProbabilityTheory

namespace HarmonicBalls

/-- Complex affine maps transport circle averages, with the radius multiplied
by the norm of the linear coefficient. -/
theorem circleAverage_complex_affine (f : ℂ → ℝ) (a b z : ℂ) (r : ℝ) :
    Real.circleAverage f (a * z + b) (‖a‖ * r) =
      Real.circleAverage (fun x => f (a * x + b)) z r := by
  rw [Real.circleAverage_eq_integral_add (Complex.arg a), Real.circleAverage_def]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  apply congrArg f
  have ha : (‖a‖ : ℂ) * Complex.exp (Complex.arg a * Complex.I) = a :=
    Complex.norm_mul_exp_arg_mul_I a
  simp only [circleMap, Complex.ofReal_mul, Complex.ofReal_add, add_mul, Complex.exp_add]
  calc
    _ = a * z + b + (r : ℂ) * Complex.exp (Complex.I * θ) *
        ((‖a‖ : ℂ) * Complex.exp (Complex.arg a * Complex.I)) := by ring
    _ = _ := by rw [ha]; ring

/-- The logarithmic interaction of two circles transforms by the logarithm
of the norm of the complex affine coefficient. -/
theorem circleLogInteraction_complex_affine {a b z w : ℂ} {r s : ℝ}
    (ha : a ≠ 0) (hr : 0 < r) (hs : 0 < s) :
    Real.circleAverage (fun x => Real.log (max (‖a‖ * s) ‖(a * z + b) - x‖))
      (a * w + b) (‖a‖ * r) =
    Real.log ‖a‖ + Real.circleAverage (fun x => Real.log (max s ‖z - x‖)) w r := by
  rw [circleAverage_complex_affine]
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hf : (fun x : ℂ => Real.log (max (‖a‖ * s) ‖(a * z + b) - (a * x + b)‖)) =
      fun x => Real.log ‖a‖ + Real.log (max s ‖z - x‖) := by
    funext x
    have heq : (a * z + b) - (a * x + b) = a * (z - x) := by ring
    rw [heq, norm_mul, ← mul_max_of_nonneg _ _ ha'.le, Real.log_mul ha'.ne'
      (ne_of_gt (lt_of_lt_of_le hs (le_max_left _ _)))]
  rw [hf]
  have hc : Continuous (fun x : ℂ => Real.log (max s ‖z - x‖)) :=
    (continuous_const.max ((continuous_const.sub continuous_id).norm)).log
      (fun x => ne_of_gt (lt_of_lt_of_le hs (le_max_left _ _)))
  change Real.circleAverage ((fun _ : ℂ => Real.log ‖a‖) +
    (fun x => Real.log (max s ‖z - x‖))) w r = _
  rw [Real.circleAverage_add (circleIntegrable_const _ _ _)
    (hc.continuousOn.circleIntegrable hr.le), Real.circleAverage_const]

/-- Under a complex affine map the covariance of two circle averages changes
by two normalization terms and the logarithm of the scale. -/
theorem wholePlaneGFFCov_circles_complex_affine {a b z w : ℂ} {r s : ℝ}
    (ha : a ≠ 0) (hr : 0 < r) (hs : 0 < s) :
    wholePlaneGFFCov (.circle (‖a‖ * r) (a * w + b)) (.circle (‖a‖ * s) (a * z + b)) =
      wholePlaneGFFCov (.circle r w) (.circle s z) +
      (Real.circleAverage wholePlaneNormalization (a * w + b) (‖a‖ * r) -
        Real.circleAverage wholePlaneNormalization w r) +
      (Real.circleAverage wholePlaneNormalization (a * z + b) (‖a‖ * s) -
        Real.circleAverage wholePlaneNormalization z s) - Real.log ‖a‖ := by
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  rw [wholePlaneGFFCov_circles_normalization (mul_pos ha' hr) (mul_pos ha' hs),
    wholePlaneGFFCov_circles_normalization hr hs, circleLogInteraction_complex_affine ha hr hs]
  ring

/-- The covariance of two recentered circle averages is invariant under a
nonconstant complex affine map. -/
theorem IsWholePlaneGFF.covariance_circle_increments_complex_affine
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {a : ℂ} (ha : a ≠ 0) {r s t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (z w c b : ℂ) :
    cov[fun ω => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω (‖a‖ * t) (a * c + b),
        fun ω => hcirc ω (‖a‖ * s) (a * w + b) - hcirc ω (‖a‖ * t) (a * c + b); P] =
    cov[fun ω => hcirc ω r z - hcirc ω t c, fun ω => hcirc ω s w - hcirc ω t c; P] := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hlp (q : ℝ) (hq : 0 < q) (x : ℂ) : MemLp (fun ω => hcirc ω q x) 2 P :=
    (h.hasGaussianLaw_circle hq x).memLp (by simp)
  have hc (q v : ℝ) (hq : 0 < q) (hv : 0 < v) (x y : ℂ) :
      cov[fun ω => hcirc ω q x, fun ω => hcirc ω v y; P] =
        wholePlaneGFFCov (.circle q x) (.circle v y) := by
    simpa only [GFFObservable.eval] using h.covariance_eq (.circle q x) (.circle v y) hq hv
  rw [covariance_fun_sub_fun_sub (hlp _ (mul_pos ha' hr) _) (hlp _ (mul_pos ha' ht) _)
      (hlp _ (mul_pos ha' hs) _) (hlp _ (mul_pos ha' ht) _),
    covariance_fun_sub_fun_sub (hlp _ hr _) (hlp _ ht _) (hlp _ hs _) (hlp _ ht _),
    hc _ _ (mul_pos ha' hr) (mul_pos ha' hs), hc _ _ (mul_pos ha' hr) (mul_pos ha' ht),
    hc _ _ (mul_pos ha' ht) (mul_pos ha' hs), hc _ _ (mul_pos ha' ht) (mul_pos ha' ht),
    hc _ _ hr hs, hc _ _ hr ht, hc _ _ ht hs, hc _ _ ht ht,
    wholePlaneGFFCov_circles_complex_affine ha hr hs,
    wholePlaneGFFCov_circles_complex_affine ha hr ht,
    wholePlaneGFFCov_circles_complex_affine ha ht hs,
    wholePlaneGFFCov_circles_complex_affine ha ht ht]
  ring

/-- The finite-dimensional distributions of recentered circle averages are
invariant under nonconstant complex affine maps. -/
theorem IsWholePlaneGFF.identDistrib_recentered_circles_complex_affine
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (r : ι → ℝ) (z : ι → ℂ)
    (hr : ∀ i, 0 < r i) {a : ℂ} (ha : a ≠ 0) {t : ℝ} (ht : 0 < t) (c b : ℂ) :
    IdentDistrib
      (fun ω i => hcirc ω (‖a‖ * r i) (a * z i + b) - hcirc ω (‖a‖ * t) (a * c + b))
      (fun ω i => hcirc ω (r i) (z i) - hcirc ω t c) P P := by
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  apply identDistrib_gaussian_vector_of_mean_covariance
    (h.hasGaussianLaw_recentered_circles (fun i => ‖a‖ * r i)
      (fun i => a * z i + b) (fun i => mul_pos ha' (hr i)) (mul_pos ha' ht) _)
    (h.hasGaussianLaw_recentered_circles r z hr ht c)
  · intro i
    have hmean (q : ℝ) (hq : 0 < q) (x : ℂ) : ∫ ω, hcirc ω q x ∂P = 0 :=
      h.integral_eq_zero (.circle q x) hq
    have hint (q : ℝ) (hq : 0 < q) (x : ℂ) : Integrable (fun ω => hcirc ω q x) P :=
      (h.hasGaussianLaw_circle hq x).integrable
    rw [integral_sub (hint _ (mul_pos ha' (hr i)) _) (hint _ (mul_pos ha' ht) _),
      integral_sub (hint _ (hr i) _) (hint _ ht _),
      hmean _ (mul_pos ha' (hr i)), hmean _ (mul_pos ha' ht), hmean _ (hr i), hmean _ ht]
  · intro i j
    exact h.covariance_circle_increments_complex_affine ha (hr i) (hr j) ht (z i) (z j) c b

/-- The complete indexed family of recentered circle averages is invariant in
law under a nonconstant complex affine map. -/
theorem IsWholePlaneGFF.identDistrib_recentered_circle_family_complex_affine
    {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (r : ι → ℝ) (z : ι → ℂ)
    (hr : ∀ i, 0 < r i) {a : ℂ} (ha : a ≠ 0) {t : ℝ} (ht : 0 < t) (c b : ℂ) :
    IdentDistrib
      (fun ω i => hcirc ω (‖a‖ * r i) (a * z i + b) - hcirc ω (‖a‖ * t) (a * c + b))
      (fun ω i => hcirc ω (r i) (z i) - hcirc ω t c) P P := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hm1 : Measurable (fun ω i => hcirc ω (‖a‖ * r i) (a * z i + b) -
      hcirc ω (‖a‖ * t) (a * c + b)) := by
    apply Measurable.of_eval
    intro i
    exact (h.measurable_circle _ _ (mul_pos ha' (hr i))).sub
      (h.measurable_circle _ _ (mul_pos ha' ht))
  have hm2 : Measurable (fun ω i => hcirc ω (r i) (z i) - hcirc ω t c) := by
    apply Measurable.of_eval
    intro i
    exact (h.measurable_circle _ _ (hr i)).sub (h.measurable_circle _ _ ht)
  apply (identDistrib_iff_forall_finset_identDistrib hm1.aemeasurable hm2.aemeasurable).2
  intro I
  exact h.identDistrib_recentered_circles_complex_affine (fun i : I => r i)
    (fun i : I => z i) (fun i => hr i) ha ht c b

/-- The normalized whole-plane GFF circle-average family is affine invariant
in law after subtracting the transformed unit-circle average. -/
theorem IsWholePlaneGFF.identDistrib_circle_family_complex_affine
    {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (r : ι → ℝ) (z : ι → ℂ)
    (hr : ∀ i, 0 < r i) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IdentDistrib
      (fun ω i => hcirc ω (‖a‖ * r i) (a * z i + b) - hcirc ω ‖a‖ b)
      (fun ω i => hcirc ω (r i) (z i)) P P := by
  have hdist := h.identDistrib_recentered_circle_family_complex_affine r z hr ha
    (show (0 : ℝ) < 1 from zero_lt_one) 0 b
  have heq : (fun ω i => hcirc ω (r i) (z i) - hcirc ω 1 0) =ᵐ[P]
      (fun ω i => hcirc ω (r i) (z i)) := by
    filter_upwards [h.ae_circleAverage_one_zero] with ω hω
    funext i
    simp [hω]
  have h' := hdist.trans (IdentDistrib.of_ae_eq hdist.aemeasurable_snd heq)
  simpa only [mul_one, mul_zero, zero_add] using h'

end HarmonicBalls
