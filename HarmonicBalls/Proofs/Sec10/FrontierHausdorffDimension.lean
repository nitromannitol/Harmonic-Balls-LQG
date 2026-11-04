import HarmonicBalls.Proofs.Sec10.FrontierMinimalSeparation
import HarmonicBalls.Proofs.Sec10.UniqueComplementFrontier
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Hausdorff

/-! # Hausdorff length of a cluster's exterior frontier -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal MeasureTheory

/-- A bounded closed planar set containing a ball has boundary length at least
its diameter. The proof projects the boundary onto the ball's horizontal diameter. -/
theorem hausdorffMeasure_one_frontier_ge_of_ball_subset
    {A : Set ℂ} (hAc : IsClosed A) {p : ℂ} {r R : ℝ} (hr : 0 < r)
    (hball : ball p r ⊆ A) (hbound : A ⊆ ball 0 R) :
    ENNReal.ofReal (2 * r) ≤ μH[1] (frontier A) := by
  have hR : 0 < R := by
    have hp := hbound (hball (mem_ball_self hr))
    exact lt_of_le_of_lt (dist_nonneg : 0 ≤ dist p 0) hp
  have hproj : Ioo (p.re - r) (p.re + r) ⊆ Complex.re '' frontier A := by
    intro t ht
    let x : ℂ := p + ((t - p.re : ℝ) : ℂ)
    let y : ℂ := (t : ℂ) + ((R + 1 : ℝ) : ℂ) * Complex.I
    have hxball : x ∈ ball p r := by
      rw [mem_ball, dist_eq_norm]
      have habs : |t - p.re| < r := by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
      rw [show x - p = ((t - p.re : ℝ) : ℂ) by simp [x], Complex.norm_real]
      exact habs
    have hxA : x ∈ A := hball hxball
    have hxi : x ∈ interior A := isOpen_ball.subset_interior_iff.mpr hball hxball
    have hxfront : x ∉ frontier A := disjoint_left.mp disjoint_interior_frontier hxi
    have hyA : y ∉ A := by
      intro hy
      have hybound : ‖y‖ < R := by simpa [mem_ball, dist_zero_right] using hbound hy
      have him := Complex.abs_im_le_norm y
      have hyim : y.im = R + 1 := by simp [y]
      rw [hyim, abs_of_pos (by linarith)] at him
      linarith
    have hyU : y ∈ Aᶜ := hyA
    have hxU : x ∉ Aᶜ := by simpa using hxA
    have hxf : x ∉ frontier Aᶜ := by simpa only [frontier_compl] using hxfront
    have hmeet : (segment ℝ x y ∩ frontier A).Nonempty := by
      by_contra hn
      have havoid : segment ℝ x y ⊆ (frontier Aᶜ)ᶜ := by
        intro q hq hqf
        apply hn
        exact ⟨q, hq, by simpa only [frontier_compl] using hqf⟩
      have hseg : Convex ℝ (segment ℝ x y) := convex_segment x y
      have hycomp := hseg.isPreconnected.subset_connectedComponentIn
        (left_mem_segment ℝ x y) havoid (right_mem_segment ℝ x y)
      exact not_mem_connectedComponentIn_compl_frontier hAc.isOpen_compl hxU hxf hyU hycomp
    obtain ⟨q, hqseg, hqfront⟩ := hmeet
    refine ⟨q, hqfront, ?_⟩
    obtain ⟨a, b, ha, hb, hab, habq⟩ := hqseg
    have hxre : x.re = t := by simp [x]
    have hyre : y.re = t := by simp [y]
    have hre := congrArg Complex.re habq
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at hre
    rw [hxre, hyre] at hre
    calc
      q.re = a * t + b * t := hre.symm
      _ = (a + b) * t := by ring
      _ = t := by rw [hab]; ring
  have hmeasure := (RCLike.lipschitzWith_re (K := ℂ)).hausdorffMeasure_image_le
    (d := 1) (by norm_num) (frontier A)
  have hmono : (μH[1] : Measure ℝ) (Ioo (p.re - r) (p.re + r)) ≤
      μH[1] (Complex.re '' frontier A) := measure_mono hproj
  rw [hausdorffMeasure_real, Real.volume_Ioo] at hmono
  convert hmono.trans (by simpa using hmeasure) using 1
  congr 1
  ring

/-- A bounded closed planar set with nonempty interior has frontier of
Hausdorff dimension at least one. -/
theorem one_le_dimH_frontier_of_ball_subset
    {A : Set ℂ} (hAc : IsClosed A) {p : ℂ} {r R : ℝ} (hr : 0 < r)
    (hball : ball p r ⊆ A) (hbound : A ⊆ ball 0 R) :
    1 ≤ dimH (frontier A) := by
  apply le_dimH_of_hausdorffMeasure_ne_zero (d := 1)
  have h := hausdorffMeasure_one_frontier_ge_of_ball_subset hAc hr hball hbound
  exact ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by positivity)) h)

universe u

/-- Under the crossing-containment hypothesis, every ball inside a compactly
contained cluster gives a lower bound on its complementary frontier's length. -/
theorem ae_cluster_complement_frontier_length_ge
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        ∀ p : ℂ, ∀ r : ℝ, 0 < r → ball p r ⊆ cluster (μ ω) 1 z t →
          ENNReal.ofReal (2 * r) ≤ μH[1] (frontier U) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_complement_component_eq_and_frontier_of_crossing hI2 h5
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω heq
  intro t ht z hz hcl U hU p r hr hball
  rw [(heq t ht z hz hcl U hU).2]
  exact hausdorffMeasure_one_frontier_ge_of_ball_subset isClosed_closure hr
    (hball.trans subset_closure) hcl

/-- Under the same hypotheses, each complementary frontier has Hausdorff
 dimension at least one. -/
theorem ae_one_le_dimH_cluster_complement_frontier
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        1 ≤ dimH (frontier U) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_complement_component_eq_and_frontier_of_crossing hI2 h5
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
      with ω heq hopen
  intro t ht z hz hcl U hU
  have hG := hopen t 1 ht zero_lt_one z hz
  obtain ⟨p, hp⟩ := hG.2.1.nonempty
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hG.1.mem_nhds hp)
  rw [(heq t ht z hz hcl U hU).2]
  exact one_le_dimH_frontier_of_ball_subset isClosed_closure hr
    (hball.trans subset_closure) hcl

end HarmonicBalls
