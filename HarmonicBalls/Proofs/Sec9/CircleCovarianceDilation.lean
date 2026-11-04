import HarmonicBalls.Proofs.Sec8.CircleDensityDoubleLog
import HarmonicBalls.Proofs.Sec9.ConcentricIncrementCovariance

/-! # Circle-average covariance under dilation and translation

The logarithmic interaction of two circles transforms by an additive
constant. The one-point normalization terms consequently cancel when the
field is recentered by a reference circle average.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ProbabilityTheory

namespace HarmonicBalls

/-- A positive dilation and translation can be moved inside a circle average. -/
theorem circleAverage_dilation_translation (f : ℂ → ℝ) (k r : ℝ) (z b : ℂ) :
    Real.circleAverage f ((k : ℂ) * z + b) (k * r) =
      Real.circleAverage (fun x => f ((k : ℂ) * x + b)) z r := by
  calc
    _ = Real.circleAverage (fun x => f ((k * r : ℝ) * x + ((k : ℂ) * z + b))) 0 1 :=
      Real.circleAverage_eq_circleAverage_zero_one
    _ = Real.circleAverage (fun x => f ((k : ℂ) * ((r : ℂ) * x + z) + b)) 0 1 := by
      congr 1
      funext x
      congr 1
      push_cast
      ring
    _ = _ := (Real.circleAverage_eq_circleAverage_zero_one
      (f := fun x : ℂ => f ((k : ℂ) * x + b)) (c := z) (R := r)).symm

/-- The logarithmic interaction between circles gains the logarithm of the
common dilation factor. -/
theorem circleLogInteraction_dilation_translation {k r s : ℝ}
    (hk : 0 < k) (hr : 0 < r) (hs : 0 < s) (z w b : ℂ) :
    Real.circleAverage
      (fun x => Real.log (max (k * s) ‖((k : ℂ) * z + b) - x‖))
      ((k : ℂ) * w + b) (k * r) =
    Real.log k + Real.circleAverage (fun x => Real.log (max s ‖z - x‖)) w r := by
  rw [circleAverage_dilation_translation]
  have hf : (fun x : ℂ => Real.log (max (k * s)
      ‖((k : ℂ) * z + b) - ((k : ℂ) * x + b)‖)) =
      fun x => Real.log k + Real.log (max s ‖z - x‖) := by
    funext x
    have heq : ((k : ℂ) * z + b) - ((k : ℂ) * x + b) = (k : ℂ) * (z - x) := by ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk,
      ← mul_max_of_nonneg _ _ hk.le, Real.log_mul hk.ne'
        (ne_of_gt (lt_of_lt_of_le hs (le_max_left _ _)))]
  rw [hf]
  have hc : Continuous (fun x : ℂ => Real.log (max s ‖z - x‖)) :=
    (continuous_const.max ((continuous_const.sub continuous_id).norm)).log
      (fun x => ne_of_gt (lt_of_lt_of_le hs (le_max_left _ _)))
  change Real.circleAverage ((fun _ : ℂ => Real.log k) +
    (fun x => Real.log (max s ‖z - x‖))) w r = _
  rw [Real.circleAverage_add (circleIntegrable_const _ _ _)
    (hc.continuousOn.circleIntegrable hr.le), Real.circleAverage_const]

/-- The normalization change for a circle-average covariance. -/
noncomputable def circleNormalizationChange (k r : ℝ) (z b : ℂ) : ℝ :=
  Real.circleAverage wholePlaneNormalization ((k : ℂ) * z + b) (k * r) -
    Real.circleAverage wholePlaneNormalization z r

/-- Dilation and translation change the circle-average covariance by two
one-circle normalization terms and a logarithmic scale term. -/
theorem wholePlaneGFFCov_circles_dilation_translation {k r s : ℝ}
    (hk : 0 < k) (hr : 0 < r) (hs : 0 < s) (z w b : ℂ) :
    wholePlaneGFFCov (.circle (k * r) ((k : ℂ) * w + b))
        (.circle (k * s) ((k : ℂ) * z + b)) =
      wholePlaneGFFCov (.circle r w) (.circle s z) +
        circleNormalizationChange k r w b + circleNormalizationChange k s z b - Real.log k := by
  rw [wholePlaneGFFCov_circles_normalization (mul_pos hk hr) (mul_pos hk hs),
    wholePlaneGFFCov_circles_normalization hr hs,
    circleLogInteraction_dilation_translation hk hr hs]
  unfold circleNormalizationChange
  ring

/-- Recentered circle averages at arbitrary centers have invariant
covariances under a common dilation and translation. -/
theorem IsWholePlaneGFF.covariance_circle_increments_dilation_translation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {k r s t : ℝ}
    (hk : 0 < k) (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (z w a b : ℂ) :
    cov[fun ω => hcirc ω (k * r) ((k : ℂ) * z + b) - hcirc ω (k * t) ((k : ℂ) * a + b),
        fun ω => hcirc ω (k * s) ((k : ℂ) * w + b) - hcirc ω (k * t) ((k : ℂ) * a + b); P] =
    cov[fun ω => hcirc ω r z - hcirc ω t a,
        fun ω => hcirc ω s w - hcirc ω t a; P] := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hlp (q : ℝ) (hq : 0 < q) (x : ℂ) : MemLp (fun ω => hcirc ω q x) 2 P :=
    (h.hasGaussianLaw_circle hq x).memLp (by simp)
  have hc (q v : ℝ) (hq : 0 < q) (hv : 0 < v) (x y : ℂ) :
      cov[fun ω => hcirc ω q x, fun ω => hcirc ω v y; P] =
        wholePlaneGFFCov (.circle q x) (.circle v y) := by
    simpa only [GFFObservable.eval] using h.covariance_eq (.circle q x) (.circle v y) hq hv
  rw [covariance_fun_sub_fun_sub (hlp _ (mul_pos hk hr) _) (hlp _ (mul_pos hk ht) _)
      (hlp _ (mul_pos hk hs) _) (hlp _ (mul_pos hk ht) _),
    covariance_fun_sub_fun_sub (hlp _ hr _) (hlp _ ht _) (hlp _ hs _) (hlp _ ht _),
    hc _ _ (mul_pos hk hr) (mul_pos hk hs), hc _ _ (mul_pos hk hr) (mul_pos hk ht),
    hc _ _ (mul_pos hk ht) (mul_pos hk hs), hc _ _ (mul_pos hk ht) (mul_pos hk ht),
    hc _ _ hr hs, hc _ _ hr ht, hc _ _ ht hs, hc _ _ ht ht,
    wholePlaneGFFCov_circles_dilation_translation hk hr hs,
    wholePlaneGFFCov_circles_dilation_translation hk hr ht,
    wholePlaneGFFCov_circles_dilation_translation hk ht hs,
    wholePlaneGFFCov_circles_dilation_translation hk ht ht]
  ring

/-- A finite family of circle averages recentered by a common circle average
is jointly Gaussian. -/
theorem IsWholePlaneGFF.hasGaussianLaw_recentered_circles
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (r : ι → ℝ) (z : ι → ℂ)
    (hr : ∀ i, 0 < r i) {t : ℝ} (ht : 0 < t) (a : ℂ) :
    HasGaussianLaw (fun ω i => hcirc ω (r i) (z i) - hcirc ω t a) P := by
  classical
  let o : ι × Bool → GFFObservable.Admissible := fun p =>
    if p.2 then ⟨.circle (r p.1) (z p.1), hr p.1⟩ else ⟨.circle t a, ht⟩
  have hg := (h.isGaussianProcess.comp_right o).hasGaussianLaw Finset.univ
  let proj (p : ι × Bool) : (↥(Finset.univ : Finset (ι × Bool)) → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj ⟨p, Finset.mem_univ _⟩
  let L : (↥(Finset.univ : Finset (ι × Bool)) → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi fun i : ι => proj (i, true) - proj (i, false)
  have hl := hg.map L
  convert hl using 1
  funext ω i
  rfl

/-- Finite joint laws of recentered circle averages are invariant under a
common positive dilation and translation. -/
theorem IsWholePlaneGFF.identDistrib_recentered_circles_dilation_translation
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (r : ι → ℝ) (z : ι → ℂ)
    (hr : ∀ i, 0 < r i) {k t : ℝ} (hk : 0 < k) (ht : 0 < t) (a b : ℂ) :
    IdentDistrib
      (fun ω i => hcirc ω (k * r i) ((k : ℂ) * z i + b) - hcirc ω (k * t) ((k : ℂ) * a + b))
      (fun ω i => hcirc ω (r i) (z i) - hcirc ω t a) P P := by
  apply identDistrib_gaussian_vector_of_mean_covariance
    (h.hasGaussianLaw_recentered_circles (fun i => k * r i)
      (fun i => (k : ℂ) * z i + b) (fun i => mul_pos hk (hr i)) (mul_pos hk ht) _)
    (h.hasGaussianLaw_recentered_circles r z hr ht a)
  · intro i
    have hmean (q : ℝ) (hq : 0 < q) (x : ℂ) : ∫ ω, hcirc ω q x ∂P = 0 :=
      h.integral_eq_zero (.circle q x) hq
    have hint (q : ℝ) (hq : 0 < q) (x : ℂ) : Integrable (fun ω => hcirc ω q x) P :=
      (h.hasGaussianLaw_circle hq x).integrable
    rw [integral_sub (hint _ (mul_pos hk (hr i)) _) (hint _ (mul_pos hk ht) _),
      integral_sub (hint _ (hr i) _) (hint _ ht _),
      hmean _ (mul_pos hk (hr i)), hmean _ (mul_pos hk ht), hmean _ (hr i), hmean _ ht]
  · intro i j
    exact h.covariance_circle_increments_dilation_translation hk (hr i) (hr j) ht (z i) (z j) a b

/-- The joint law of an arbitrary indexed family of recentered circle averages
is invariant under common positive dilation and translation. -/
theorem IsWholePlaneGFF.identDistrib_recentered_circle_family_dilation_translation
    {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (r : ι → ℝ) (z : ι → ℂ)
    (hr : ∀ i, 0 < r i) {k t : ℝ} (hk : 0 < k) (ht : 0 < t) (a b : ℂ) :
    IdentDistrib
      (fun ω i => hcirc ω (k * r i) ((k : ℂ) * z i + b) - hcirc ω (k * t) ((k : ℂ) * a + b))
      (fun ω i => hcirc ω (r i) (z i) - hcirc ω t a) P P := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hm1 : Measurable (fun ω i => hcirc ω (k * r i) ((k : ℂ) * z i + b) -
      hcirc ω (k * t) ((k : ℂ) * a + b)) := by
    apply Measurable.of_eval
    intro i
    exact (h.measurable_circle _ _ (mul_pos hk (hr i))).sub
      (h.measurable_circle _ _ (mul_pos hk ht))
  have hm2 : Measurable (fun ω i => hcirc ω (r i) (z i) - hcirc ω t a) := by
    apply Measurable.of_eval
    intro i
    exact (h.measurable_circle _ _ (hr i)).sub (h.measurable_circle _ _ ht)
  apply (identDistrib_iff_forall_finset_identDistrib hm1.aemeasurable hm2.aemeasurable).2
  intro I
  exact h.identDistrib_recentered_circles_dilation_translation (fun i : I => r i)
    (fun i : I => z i) (fun i => hr i) hk ht a b

/-- The normalized whole-plane GFF circle-average family is invariant in law
under positive dilation and translation, with the transformed unit-circle
average subtracted. -/
theorem IsWholePlaneGFF.identDistrib_circle_family_dilation_translation
    {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (r : ι → ℝ) (z : ι → ℂ)
    (hr : ∀ i, 0 < r i) {k : ℝ} (hk : 0 < k) (b : ℂ) :
    IdentDistrib
      (fun ω i => hcirc ω (k * r i) ((k : ℂ) * z i + b) - hcirc ω k b)
      (fun ω i => hcirc ω (r i) (z i)) P P := by
  have hdist := h.identDistrib_recentered_circle_family_dilation_translation r z hr hk
    (show (0 : ℝ) < 1 from zero_lt_one) 0 b
  have heq : (fun ω i => hcirc ω (r i) (z i) - hcirc ω 1 0) =ᵐ[P]
      (fun ω i => hcirc ω (r i) (z i)) := by
    filter_upwards [h.ae_circleAverage_one_zero] with ω hω
    funext i
    simp [hω]
  have h' := hdist.trans (IdentDistrib.of_ae_eq hdist.aemeasurable_snd heq)
  simpa only [mul_one, mul_zero, add_zero, zero_add] using h'

end HarmonicBalls
