import HarmonicBalls.Proofs.Sec8.ConcentricCircleCovariance
import HarmonicBalls.Proofs.Sec5.GaussianProcessLaw

/-! # Covariance of concentric circle-average increments

The covariance of two increments is independent of the center and invariant
under a common positive rescaling of the radii. -/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace HarmonicBalls

/-- The normalization terms cancel from the covariance of two concentric
circle-average increments. -/
theorem IsWholePlaneGFF.covariance_concentric_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {r s u v : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (z : ℂ) :
    cov[fun ω => hcirc ω r z - hcirc ω s z,
        fun ω => hcirc ω u z - hcirc ω v z; P] =
      -Real.log (max r u) + Real.log (max r v) +
        Real.log (max s u) - Real.log (max s v) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hlp (t : ℝ) (ht : 0 < t) : MemLp (fun ω => hcirc ω t z) 2 P :=
    (h.hasGaussianLaw_circle ht z).memLp (by simp)
  have hc (t q : ℝ) (ht : 0 < t) (hq : 0 < q) :
      cov[fun ω => hcirc ω t z, fun ω => hcirc ω q z; P] =
        wholePlaneGFFCov (.circle t z) (.circle q z) := by
    simpa only [GFFObservable.eval] using h.covariance_eq (.circle t z) (.circle q z) ht hq
  rw [covariance_fun_sub_fun_sub (hlp r hr) (hlp s hs) (hlp u hu) (hlp v hv),
    hc r u hr hu, hc r v hr hv, hc s u hs hu, hc s v hs hv,
    wholePlaneGFFCov_concentric_circles_general hr hu,
    wholePlaneGFFCov_concentric_circles_general hr hv,
    wholePlaneGFFCov_concentric_circles_general hs hu,
    wholePlaneGFFCov_concentric_circles_general hs hv]
  ring

/-- Common dilation of the radii and arbitrary change of center preserve the
covariance of concentric circle-average increments. -/
theorem IsWholePlaneGFF.covariance_concentric_increments_dilation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {r s u v k : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hu : 0 < u) (hv : 0 < v) (hk : 0 < k)
    (z w : ℂ) :
    cov[fun ω => hcirc ω (k * r) w - hcirc ω (k * s) w,
        fun ω => hcirc ω (k * u) w - hcirc ω (k * v) w; P] =
    cov[fun ω => hcirc ω r z - hcirc ω s z,
        fun ω => hcirc ω u z - hcirc ω v z; P] := by
  rw [h.covariance_concentric_increments (mul_pos hk hr) (mul_pos hk hs)
      (mul_pos hk hu) (mul_pos hk hv),
    h.covariance_concentric_increments hr hs hu hv]
  have hmax (x y : ℝ) (hx : 0 < x) :
      Real.log (max (k * x) (k * y)) = Real.log k + Real.log (max x y) := by
    rw [← mul_max_of_nonneg _ _ hk.le, Real.log_mul hk.ne'
      (ne_of_gt (lt_of_lt_of_le hx (le_max_left _ _)))]
  rw [hmax r u hr, hmax r v hr, hmax s u hs, hmax s v hs]
  ring

/-- Every finite vector of concentric circle-average increments is jointly
Gaussian. The radii may depend on the coordinate. -/
theorem IsWholePlaneGFF.hasGaussianLaw_concentric_increments
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (r s : ι → ℝ)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i) (z : ℂ) :
    HasGaussianLaw (fun ω i => hcirc ω (r i) z - hcirc ω (s i) z) P := by
  classical
  let o : ι × Bool → GFFObservable.Admissible := fun p =>
    if p.2 then ⟨.circle (r p.1) z, hr p.1⟩ else ⟨.circle (s p.1) z, hs p.1⟩
  have hg := (h.isGaussianProcess.comp_right o).hasGaussianLaw Finset.univ
  let proj (p : ι × Bool) : (↥(Finset.univ : Finset (ι × Bool)) → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj ⟨p, Finset.mem_univ _⟩
  let L : (↥(Finset.univ : Finset (ι × Bool)) → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi fun i : ι => proj (i, true) - proj (i, false)
  have hl := hg.map L
  convert hl using 1
  funext ω i
  rfl

/-- Common positive dilation and a change of center preserve every finite
joint law of concentric circle-average increments. -/
theorem IsWholePlaneGFF.identDistrib_concentric_increments_dilation
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (r s : ι → ℝ)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i) {k : ℝ} (hk : 0 < k) (z w : ℂ) :
    IdentDistrib (fun ω i => hcirc ω (k * r i) w - hcirc ω (k * s i) w)
      (fun ω i => hcirc ω (r i) z - hcirc ω (s i) z) P P := by
  apply identDistrib_gaussian_vector_of_mean_covariance
    (h.hasGaussianLaw_concentric_increments (fun i => k * r i) (fun i => k * s i)
      (fun i => mul_pos hk (hr i)) (fun i => mul_pos hk (hs i)) w)
    (h.hasGaussianLaw_concentric_increments r s hr hs z)
  · intro i
    have hmean (t : ℝ) (ht : 0 < t) (x : ℂ) : ∫ ω, hcirc ω t x ∂P = 0 :=
      h.integral_eq_zero (.circle t x) ht
    have hint (t : ℝ) (ht : 0 < t) (x : ℂ) : Integrable (fun ω => hcirc ω t x) P :=
      (h.hasGaussianLaw_circle ht x).integrable
    rw [integral_sub (hint _ (mul_pos hk (hr i)) _) (hint _ (mul_pos hk (hs i)) _),
      integral_sub (hint _ (hr i) _) (hint _ (hs i) _),
      hmean _ (mul_pos hk (hr i)), hmean _ (mul_pos hk (hs i)),
      hmean _ (hr i), hmean _ (hs i)]
  · intro i j
    exact h.covariance_concentric_increments_dilation (hr i) (hs i) (hr j) (hs j) hk z w

/-- The full indexed family of concentric increments has the same law after
a common positive dilation and a change of center. -/
theorem IsWholePlaneGFF.identDistrib_concentric_increment_family_dilation
    {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (r s : ι → ℝ)
    (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i) {k : ℝ} (hk : 0 < k) (z w : ℂ) :
    IdentDistrib (fun ω i => hcirc ω (k * r i) w - hcirc ω (k * s i) w)
      (fun ω i => hcirc ω (r i) z - hcirc ω (s i) z) P P := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hm1 : Measurable (fun ω i => hcirc ω (k * r i) w - hcirc ω (k * s i) w) := by
    apply Measurable.of_eval
    intro i
    exact (h.measurable_circle _ _ (mul_pos hk (hr i))).sub
      (h.measurable_circle _ _ (mul_pos hk (hs i)))
  have hm2 : Measurable (fun ω i => hcirc ω (r i) z - hcirc ω (s i) z) := by
    apply Measurable.of_eval
    intro i
    exact (h.measurable_circle _ _ (hr i)).sub (h.measurable_circle _ _ (hs i))
  apply (identDistrib_iff_forall_finset_identDistrib hm1.aemeasurable hm2.aemeasurable).2
  intro I
  exact h.identDistrib_concentric_increments_dilation (fun i : I => r i) (fun i : I => s i)
    (fun i => hr i) (fun i => hs i) hk z w

end HarmonicBalls
