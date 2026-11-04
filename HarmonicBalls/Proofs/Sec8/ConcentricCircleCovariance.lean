import HarmonicBalls.Proofs.Sec8.CircleLogPotential

/-! # Concentric circle-average covariance

The normalization terms cancel from increments between concentric circle
averages. The imported Section 8 argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped Topology ProbabilityTheory

namespace HarmonicBalls

/-- The covariance of concentric circle averages at arbitrary positive radii. -/
theorem wholePlaneGFFCov_concentric_circles_general {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (z : ℂ) :
    wholePlaneGFFCov (.circle r z) (.circle s z) =
      Real.circleAverage wholePlaneNormalization z r +
      Real.circleAverage wholePlaneNormalization z s - Real.log (max r s) := by
  change Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) z s) z r = _
  have heq : Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) z s) z r =
      Real.circleAverage (fun x => wholePlaneNormalization x +
        Real.circleAverage wholePlaneNormalization z s - Real.log (max r s)) z r := by
    apply Real.circleAverage_congr_sphere
    intro x hx
    have hx' : ‖z - x‖ = r := by
      simpa [mem_sphere, dist_eq_norm, norm_sub_rev, abs_of_pos hr] using hx
    dsimp only
    rw [circleAverage_wholePlaneCov_eq hs, hx', max_comm s r]
  rw [heq]
  have hn : CircleIntegrable wholePlaneNormalization z r :=
    continuous_wholePlaneNormalization.continuousOn.circleIntegrable hr.le
  change Real.circleAverage ((wholePlaneNormalization +
    (fun _ : ℂ => Real.circleAverage wholePlaneNormalization z s)) -
      (fun _ : ℂ => Real.log (max r s))) z r = _
  rw [Real.circleAverage_sub (hn.add (circleIntegrable_const _ _ _))
      (circleIntegrable_const _ _ _),
    Real.circleAverage_add hn (circleIntegrable_const _ _ _),
    Real.circleAverage_const, Real.circleAverage_const]

/-- The variance of a concentric increment depends only on the ratio of its
radii, for every center. -/
theorem IsWholePlaneGFF.variance_circle_sub_circle_of_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {r s : ℝ}
    (hr : 0 < r) (hrs : r ≤ s) (z : ℂ) :
    variance (fun ω => hcirc ω r z - hcirc ω s z) P = Real.log s - Real.log r := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hs : 0 < s := hr.trans_le hrs
  have hrlp : MemLp (fun ω => hcirc ω r z) 2 P := (h.hasGaussianLaw_circle hr z).memLp (by simp)
  have hslp : MemLp (fun ω => hcirc ω s z) 2 P := (h.hasGaussianLaw_circle hs z).memLp (by simp)
  have hrr := h.covariance_eq (.circle r z) (.circle r z) hr hr
  have hss := h.covariance_eq (.circle s z) (.circle s z) hs hs
  have hrs' := h.covariance_eq (.circle r z) (.circle s z) hr hs
  simp only [GFFObservable.eval] at hrr hss hrs'
  change variance ((fun ω => hcirc ω r z) - (fun ω => hcirc ω s z)) P = _
  rw [variance_sub hrlp hslp, ← covariance_self hrlp.aemeasurable,
    ← covariance_self hslp.aemeasurable, hrr, hss, hrs',
    wholePlaneGFFCov_concentric_circles_general hr hr,
    wholePlaneGFFCov_concentric_circles_general hs hs,
    wholePlaneGFFCov_concentric_circles_general hr hs]
  rw [max_self, max_self, max_eq_right hrs]
  ring

/-- The increment variance is the absolute logarithmic distance between its
positive radii. -/
theorem IsWholePlaneGFF.variance_circle_sub_circle
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z : ℂ) :
    variance (fun ω => hcirc ω r z - hcirc ω s z) P = |Real.log r - Real.log s| := by
  by_cases hrs : r ≤ s
  · rw [h.variance_circle_sub_circle_of_le hr hrs,
      abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hr hrs))]
    ring
  · have hsr : s ≤ r := le_of_not_ge hrs
    have hsymm : variance (fun ω => hcirc ω r z - hcirc ω s z) P =
        variance (fun ω => hcirc ω s z - hcirc ω r z) P := by
      calc
        _ = variance (fun ω => -(hcirc ω s z - hcirc ω r z)) P := by
          congr 1
          funext ω
          ring
        _ = _ := variance_fun_neg
    rw [hsymm, h.variance_circle_sub_circle_of_le hs hsr,
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hs hsr))]

/-- The same formula is the second moment of the centered increment. -/
theorem IsWholePlaneGFF.integral_sq_circle_sub_circle
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z : ℂ) :
    (∫ ω, (hcirc ω r z - hcirc ω s z) ^ 2 ∂P) = |Real.log r - Real.log s| := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hrlp : MemLp (fun ω => hcirc ω r z) 2 P := (h.hasGaussianLaw_circle hr z).memLp (by simp)
  have hslp : MemLp (fun ω => hcirc ω s z) 2 P := (h.hasGaussianLaw_circle hs z).memLp (by simp)
  have hmeanr : ∫ ω, hcirc ω r z ∂P = 0 := by
    simpa only [GFFObservable.eval] using h.integral_eq_zero (.circle r z) hr
  have hmeans : ∫ ω, hcirc ω s z ∂P = 0 := by
    simpa only [GFFObservable.eval] using h.integral_eq_zero (.circle s z) hs
  have hmean : ∫ ω, (hcirc ω r z - hcirc ω s z) ∂P = 0 := by
    rw [integral_sub (hrlp.integrable (by simp)) (hslp.integrable (by simp)), hmeanr, hmeans,
      sub_self]
  have hv := h.variance_circle_sub_circle hr hs z
  have hdiff : AEMeasurable (fun ω => hcirc ω r z - hcirc ω s z) P :=
    (hrlp.sub hslp).aemeasurable
  rw [variance_eq_integral hdiff, hmean] at hv
  simpa only [sub_zero] using hv

/-- Circle averages converge in probability as their positive radii converge,
at every fixed center. -/
theorem IsWholePlaneGFF.tendstoInMeasure_circle_of_tendsto_radius
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ)
    (s : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hst : Tendsto s atTop (𝓝 r)) :
    TendstoInMeasure P (fun n ω => hcirc ω (s n) z) atTop (fun ω => hcirc ω r z) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  apply tendstoInMeasure_of_centered_variance_tendsto_zero P
  · intro n
    exact ((h.hasGaussianLaw_circle (hs n) z).memLp (by simp)).sub
      ((h.hasGaussianLaw_circle hr z).memLp (by simp))
  · intro n
    have hsn : MemLp (fun ω => hcirc ω (s n) z) 2 P :=
      (h.hasGaussianLaw_circle (hs n) z).memLp (by simp)
    have hrn : MemLp (fun ω => hcirc ω r z) 2 P :=
      (h.hasGaussianLaw_circle hr z).memLp (by simp)
    have hm1 : ∫ ω, hcirc ω (s n) z ∂P = 0 := by
      simpa only [GFFObservable.eval] using h.integral_eq_zero (.circle (s n) z) (hs n)
    have hm2 : ∫ ω, hcirc ω r z ∂P = 0 := by
      simpa only [GFFObservable.eval] using h.integral_eq_zero (.circle r z) hr
    rw [integral_sub (hsn.integrable (by simp)) (hrn.integrable (by simp)), hm1, hm2, sub_self]
  · have hlog : Tendsto (fun n => Real.log (s n)) atTop (𝓝 (Real.log r)) :=
      (Real.continuousAt_log hr.ne').tendsto.comp hst
    have hv := (hlog.sub_const (Real.log r)).abs
    simp only [sub_self, abs_zero] at hv
    simpa only [h.variance_circle_sub_circle (hs _) hr z] using hv

/-- The increment variance tends to zero uniformly over sufficiently close
positive radii, independently of the center. -/
theorem IsWholePlaneGFF.exists_uniform_circle_increment_variance_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ s, 0 < s → |s - r| < δ → ∀ z : ℂ,
      variance (fun ω => hcirc ω s z - hcirc ω r z) P < ε := by
  obtain ⟨δ, hδ, hlog⟩ := (Metric.continuousAt_iff.mp (Real.continuousAt_log hr.ne')) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro s hs hsr z
  rw [h.variance_circle_sub_circle hs hr z]
  simpa only [Real.dist_eq] using hlog (by simpa only [Real.dist_eq] using hsr)

end HarmonicBalls
