import HarmonicBalls.Proofs.Sec9.ConcentricIncrementCovariance

/-! # Radial circle-average increments

The covariance computation and joint Gaussianity give independence for any
family of disjoint annuli, including degenerate annuli. The imported Section 8
work uses Leonardo Bonanno's LatticeProb formalization.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory NNReal

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The increment is Gaussian, including when its radii coincide. -/
theorem IsWholePlaneGFF.hasGaussianLaw_circle_increment
    (h : IsWholePlaneGFF P hC hcirc) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    HasGaussianLaw (fun ω => hcirc ω r 0 - hcirc ω s 0) P := by
  let o : Bool → GFFObservable.Admissible := fun b =>
    if b then ⟨.circle r 0, hr⟩ else ⟨.circle s 0, hs⟩
  simpa [o, GFFObservable.eval] using
    ((h.isGaussianProcess.comp_right o).hasGaussianLaw_fun_sub (s := true) (t := false))

/-- The increment is centered. -/
theorem IsWholePlaneGFF.integral_circle_increment
    (h : IsWholePlaneGFF P hC hcirc) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ∫ ω, (hcirc ω r 0 - hcirc ω s 0) ∂P = 0 := by
  rw [integral_sub (h.hasGaussianLaw_circle hr 0).integrable
    (h.hasGaussianLaw_circle hs 0).integrable]
  change (∫ ω, (GFFObservable.circle r 0).eval (hC ω) (hcirc ω) ∂P) -
    (∫ ω, (GFFObservable.circle s 0).eval (hC ω) (hcirc ω) ∂P) = 0
  rw [h.integral_eq_zero (.circle r 0) hr, h.integral_eq_zero (.circle s 0) hs, sub_self]

/-- The variance is the logarithm of the ratio of outer to inner radius. -/
theorem IsWholePlaneGFF.variance_radial_circle_increment
    (h : IsWholePlaneGFF P hC hcirc) {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    variance (fun ω => hcirc ω r 0 - hcirc ω s 0) P = Real.log (s / r) := by
  rw [h.variance_circle_sub_circle_of_le hr hrs, Real.log_div (ne_of_gt (hr.trans_le hrs)) hr.ne']

/-- Ordered disjoint radial intervals have zero cross covariance. -/
theorem IsWholePlaneGFF.covariance_radial_circle_increments_eq_zero
    (h : IsWholePlaneGFF P hC hcirc) {r s u v : ℝ}
    (hr : 0 < r) (hrs : r ≤ s) (hsu : s ≤ u) (huv : u ≤ v) :
    cov[fun ω => hcirc ω r 0 - hcirc ω s 0,
      fun ω => hcirc ω u 0 - hcirc ω v 0; P] = 0 := by
  have hs := hr.trans_le hrs
  have hu := hs.trans_le hsu
  have hv := hu.trans_le huv
  rw [h.covariance_concentric_increments hr hs hu hv,
    max_eq_right (hrs.trans hsu), max_eq_right (hrs.trans (hsu.trans huv)),
    max_eq_right hsu, max_eq_right (hsu.trans huv)]
  ring

/-- Every finite family of pairwise disjoint radial annular increments is
independent. Endpoints may coincide, and degenerate increments are allowed. -/
theorem IsWholePlaneGFF.iIndepFun_finite_radial_circle_increments
    {ι : Type*} [Fintype ι] (h : IsWholePlaneGFF P hC hcirc) (r s : ι → ℝ)
    (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i ≤ s i)
    (hdisj : ∀ i j, i ≠ j → s i ≤ r j ∨ s j ≤ r i) :
    iIndepFun (fun i ω => hcirc ω (r i) 0 - hcirc ω (s i) 0) P := by
  apply (h.hasGaussianLaw_concentric_increments r s hr
    (fun i => (hr i).trans_le (hrs i)) 0).iIndepFun_of_covariance_eq_zero
  intro i j hij
  rcases hdisj i j hij with hij' | hji'
  · exact h.covariance_radial_circle_increments_eq_zero (hr i) (hrs i) hij' (hrs j)
  · rw [covariance_comm]
    exact h.covariance_radial_circle_increments_eq_zero (hr j) (hrs j) hji' (hrs i)

/-- Pairwise disjoint radial increments are independent for arbitrary index
sets; the definition of independence includes all finite subfamilies. -/
theorem IsWholePlaneGFF.iIndepFun_radial_circle_increments
    {ι : Type*} (h : IsWholePlaneGFF P hC hcirc) (r s : ι → ℝ)
    (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i ≤ s i)
    (hdisj : ∀ i j, i ≠ j → s i ≤ r j ∨ s j ≤ r i) :
    iIndepFun (fun i ω => hcirc ω (r i) 0 - hcirc ω (s i) 0) P := by
  classical
  apply iIndepFun_iff_finset.mpr
  intro t
  exact h.iIndepFun_finite_radial_circle_increments (fun i : t => r i) (fun i : t => s i)
    (fun i => hr i) (fun i => hrs i) (fun i j hij => hdisj i j (fun heq => hij (Subtype.ext heq)))

/-- Exact centered Gaussian law, with variance zero allowed. -/
theorem IsWholePlaneGFF.circle_increment_hasLaw
    (h : IsWholePlaneGFF P hC hcirc) {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    HasLaw (fun ω => hcirc ω r 0 - hcirc ω s 0)
      (gaussianReal 0 (Real.log (s / r)).toNNReal) P := by
  have hg := h.hasGaussianLaw_circle_increment hr (hr.trans_le hrs)
  refine ⟨hg.aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal, h.integral_circle_increment hr (hr.trans_le hrs),
    h.variance_radial_circle_increment hr hrs]

/-- Geometric scales give an independent sequence of radial increments. -/
theorem IsWholePlaneGFF.iIndepFun_geometric_circle_increments
    (h : IsWholePlaneGFF P hC hcirc) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    iIndepFun (fun n : ℕ => fun ω => hcirc ω (q ^ (n + 1)) 0 - hcirc ω (q ^ n) 0) P := by
  apply h.iIndepFun_radial_circle_increments (fun n => q ^ (n + 1)) (fun n => q ^ n)
    (fun n => pow_pos hq _) (fun n => pow_le_pow_of_le_one hq.le hq1 (Nat.le_succ n))
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · right
    exact pow_le_pow_of_le_one hq.le hq1 (Nat.succ_le_iff.mpr hij')
  · left
    exact pow_le_pow_of_le_one hq.le hq1 (Nat.succ_le_iff.mpr hji')

/-- Every geometric increment has variance `-log q`. -/
theorem IsWholePlaneGFF.variance_geometric_circle_increment
    (h : IsWholePlaneGFF P hC hcirc) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (n : ℕ) :
    variance (fun ω => hcirc ω (q ^ (n + 1)) 0 - hcirc ω (q ^ n) 0) P = -Real.log q := by
  rw [h.variance_circle_sub_circle_of_le (pow_pos hq _) 
    (pow_le_pow_of_le_one hq.le hq1 (Nat.le_succ n)), Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- Each geometric increment has the same centered Gaussian law. -/
theorem IsWholePlaneGFF.geometric_circle_increment_hasLaw
    (h : IsWholePlaneGFF P hC hcirc) {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) (n : ℕ) :
    HasLaw (fun ω => hcirc ω (q ^ (n + 1)) 0 - hcirc ω (q ^ n) 0)
      (gaussianReal 0 (-Real.log q).toNNReal) P := by
  have hg := h.hasGaussianLaw_circle_increment (pow_pos hq (n + 1)) (pow_pos hq n)
  refine ⟨hg.aemeasurable, ?_⟩
  rw [hg.map_eq_gaussianReal, h.integral_circle_increment (pow_pos hq (n + 1))
    (pow_pos hq n), h.variance_geometric_circle_increment hq hq1 n]


end HarmonicBalls
