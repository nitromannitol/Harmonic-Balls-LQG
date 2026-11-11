import HarmonicBalls.FirstPass.S11s.Uniqueness
import HarmonicBalls.FirstPass.S11s.Inverse
import HarmonicBalls.FirstPass.S11n
import HarmonicBalls.Defs.LQGMetric

/-!
# The measurable covariance event

Ruling section 3, part B (eqs. (12)-(14)). For the measure decoder `Kf` and the metric decoder `dd` on the canonical space,
with the ratios `covA` (measure, at the balls `B_1`, `B_{1/2}`) and `covB` (metric, at the points `(0,1)`, `(0,1/2)`), the
covariance event `covEvent` is the countable intersection over a countable determining family `C` of measurable sets and a
countable dense set `Q` of points of `ℂ × ℂ`. It is measurable (`measurableSet_covEvent`), and on it the covariance holds
for every measurable set and every point (`covariance_of_mem_covEvent`).
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric ProbabilityTheory
open scoped ENNReal

/-- Measure covariance ratio `K(TL)(B_1) / K(L)(B_{1/2})` at a realization (ruling eq. (12)). -/
noncomputable def covA (Kf : S11n.CanonSpace → Measure ℂ) (L : S11n.CanonSpace) : ℝ≥0∞ :=
  Kf (dilOp L) (ball 0 1) / Kf L (ball 0 (1 / 2))

/-- Metric covariance ratio `d(TL)(0,1) / d(L)(0,1/2)` at a realization (ruling eq. (12)). -/
noncomputable def covB (dd : S11n.CanonSpace → ℂ → ℂ → ℝ) (L : S11n.CanonSpace) : ℝ :=
  dd (dilOp L) 0 1 / dd L 0 ((1 / 2 : ℝ) : ℂ)

/-- The covariance event: on the countable family `C` of measurable sets and the countable set `Q`,
the measure covariance `K(TL) S = covA · (K L)(· / (1/2)) S` and the metric covariance
`d(TL)(q) = covB · d(L)((1/2) q)` hold. -/
def covEvent (Kf : S11n.CanonSpace → Measure ℂ) (dd : S11n.CanonSpace → ℂ → ℂ → ℝ) (C : Set (Set ℂ))
    (Q : Set (ℂ × ℂ)) : Set S11n.CanonSpace :=
  (⋂ S ∈ C, {L | Kf (dilOp L) S = covA Kf L * (Kf L).map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) S}) ∩
    (⋂ q ∈ Q, {L | dd (dilOp L) q.1 q.2
      = covB dd L * dd L (((1 / 2 : ℝ) : ℂ) * q.1) (((1 / 2 : ℝ) : ℂ) * q.2)})

theorem mem_covEvent {Kf : S11n.CanonSpace → Measure ℂ} {dd : S11n.CanonSpace → ℂ → ℂ → ℝ}
    {C : Set (Set ℂ)} {Q : Set (ℂ × ℂ)} {L : S11n.CanonSpace} :
    L ∈ covEvent Kf dd C Q ↔
      (∀ S ∈ C, Kf (dilOp L) S = covA Kf L * (Kf L).map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) S) ∧
      (∀ q ∈ Q, dd (dilOp L) q.1 q.2
        = covB dd L * dd L (((1 / 2 : ℝ) : ℂ) * q.1) (((1 / 2 : ℝ) : ℂ) * q.2)) := by
  simp only [covEvent, mem_inter_iff, mem_iInter, mem_ofPred_eq]

/-- Measurability of the covariance event, from the measurability of the kernel and of the metric decoder. -/
theorem measurableSet_covEvent (K : Kernel S11n.CanonSpace ℂ) (dd : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (hdd : ∀ x y : ℂ, Measurable fun L => dd L x y) {C : Set (Set ℂ)} (hC : C.Countable)
    (hCm : ∀ S ∈ C, MeasurableSet S) {Q : Set (ℂ × ℂ)} (hQ : Q.Countable) :
    MeasurableSet (covEvent (fun L => K L) dd C Q) := by
  have hf : Measurable (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) := by fun_prop
  have hcovA : Measurable fun L => covA (fun L => K L) L := by
    unfold covA
    exact Measurable.div ((K.measurable_coe measurableSet_ball).comp measurable_dilOp)
      (K.measurable_coe measurableSet_ball)
  have hcovB : Measurable fun L => covB dd L := by
    unfold covB
    exact ((hdd 0 1).comp measurable_dilOp).div (hdd 0 ((1 / 2 : ℝ) : ℂ))
  refine MeasurableSet.inter ?_ ?_
  · refine MeasurableSet.biInter hC fun S hS => ?_
    apply measurableSet_eq_fun
    · exact (K.measurable_coe (hCm S hS)).comp measurable_dilOp
    · apply Measurable.mul hcovA
      have e : (fun L => (K L).map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) S)
          = fun L => K L ((fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) ⁻¹' S) := by
        funext L
        rw [Measure.map_apply hf (hCm S hS)]
      rw [e]
      exact K.measurable_coe (hf (hCm S hS))
  · refine MeasurableSet.biInter hQ fun q _ => ?_
    apply measurableSet_eq_fun
    · exact (hdd q.1 q.2).comp measurable_dilOp
    · exact hcovB.mul (hdd _ _)

/-- A metric satisfying `IsEuclideanLengthMetric` is nonnegative and positive off the diagonal. -/
theorem euclideanLength_pos {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {z w : ℂ} (hzw : z ≠ w) :
    0 < D z w := by
  have hnn : ∀ x y : ℂ, 0 ≤ D x y := by
    intro x y
    have h1 := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at h1
    linarith
  rcases (hnn z w).lt_or_eq with h | h
  · exact h
  · exact absurd (hD.eq_of_eq_zero z w h.symm) hzw

/-- The metric ratio `covB` is positive when both metrics are Euclidean length metrics. -/
theorem covB_pos {dd : S11n.CanonSpace → ℂ → ℂ → ℝ} {L : S11n.CanonSpace}
    (h1 : IsEuclideanLengthMetric (dd (dilOp L))) (h2 : IsEuclideanLengthMetric (dd L)) : 0 < covB dd L := by
  unfold covB
  apply div_pos
  · exact euclideanLength_pos h1 (by norm_num)
  · exact euclideanLength_pos h2 (by norm_num)

/-- The preimage of the ball of radius `1` under the rescaling `w ↦ w / (1/2)` is the ball of radius `1/2`. -/
theorem preimage_half_ball_eq : (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) ⁻¹' ball 0 1 = ball 0 (1 / 2) := by
  ext w
  simp only [mem_preimage, mem_ball, dist_zero_right, norm_div, Complex.norm_real, Real.norm_eq_abs]
  have h12 : |(1 : ℝ)| / |(2 : ℝ)| = 1 / 2 := by norm_num
  rw [h12, div_lt_one (by norm_num : (0 : ℝ) < 1 / 2)]

/-- Under `IsFiniteMeasureOnCompacts`, the ball has finite mass. -/
theorem measure_ball_lt_top' (μ : Measure ℂ) [IsFiniteMeasureOnCompacts μ] (r : ℝ) :
    μ (ball 0 r) < ∞ :=
  (measure_mono Metric.ball_subset_closedBall).trans_lt (isCompact_closedBall 0 r).measure_lt_top

/-- If the measure `μ = c • ν` with `c` a positive real, `ν (ball 0 (1/2))` finite and positive, then the covariance
ratio is `c`: `(μ (ball 0 1)) / ν' (ball 0 (1/2))` equals `ofReal a` when `μ = ofReal a • (ν.map (· / (1/2)))`. -/
theorem covA_eq_of_smul {Kf : S11n.CanonSpace → Measure ℂ} {L : S11n.CanonSpace} {a : ℝ}
    (hpos : 0 < Kf L (ball 0 (1 / 2))) (hfin : Kf L (ball 0 (1 / 2)) < ∞)
    (hT : Kf (dilOp L) = ENNReal.ofReal a • (Kf L).map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ))) :
    covA Kf L = ENNReal.ofReal a := by
  have hmap : (Kf L).map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) (ball 0 1) = Kf L (ball 0 (1 / 2)) := by
    have hf : Measurable (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) := by fun_prop
    rw [Measure.map_apply hf measurableSet_ball, preimage_half_ball_eq]
  unfold covA
  rw [hT, Measure.smul_apply, smul_eq_mul, hmap]
  exact ENNReal.mul_div_cancel_right hpos.ne' hfin.ne

end HarmonicBalls
