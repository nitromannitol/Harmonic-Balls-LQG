import HarmonicBalls.Proofs.Sec6.ScaleUniformCircleCrossing
import HarmonicBalls.Proofs.Sec6.ScaleUniformInteriorNearby

/-! # Scale-uniform good-annulus stability

The Brownian displacement modulus is uniform in the scale and centre. The
collar witness mass estimate remains an explicit, scale-dependent hypothesis.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal NNReal

/-- A uniform Brownian modulus transfers a good annulus to nearby centres
when the enlarged witness has strictly subthreshold mass. -/
theorem exists_scale_uniform_goodAnnulus_of_collar_mass
    {κ : ℝ} (hκ : 0 < κ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (μ : Measure ℂ) (r : ℝ), 0 < r → ∀ z w : ℂ,
      dist w z < δ*r → ∀ a a' b b' : ℝ,
      μ (annulus z (3*r) (5*r)) ≠ ∞ →
      IsGoodAnnulus μ r z a b →
      ENNReal.ofReal b + 2 * ε + ε ≤ ENNReal.ofReal b' →
      (∀ Y : Set ℂ, MeasurableSet Y → Y ⊆ annulus w (3*r) (5*r) →
        μ Y ≤ ENNReal.ofReal a' * μ (annulus w (3*r) (5*r)) →
        μ ((annulus z (3*r) (5*r) ∩ Y) ∪
          (annulus z (3*r) (5*r) \ {q | r*(3+κ) ≤ dist q z ∧
            dist q z ≤ r*(5-κ)})) < ENNReal.ofReal a * μ (annulus z (3*r) (5*r))) →
      IsGoodAnnulus μ r w a' b' := by
  obtain ⟨δc, hδc, hcompare⟩ := exists_scale_uniform_nearby_avoidance_comparison_of_margin hκ hε
  obtain ⟨δs, hδs, hstart⟩ := scale_uniform_goodAnnulus_avoidance_near_circle hε
  let δ := min δc (min δs (1/2))
  refine ⟨δ, lt_min hδc (lt_min hδs (by norm_num)), ?_⟩
  intro μ r hr z w hw a a' b b' hfin hg hbudget hmass Y hY hYsub hYmass u hu
  have hwc : dist w z < δc*r := hw.trans_le (mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le)
  have hws : dist w z < δs*r := hw.trans_le (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) hr.le)
  have hwr : dist w z < r/2 := by
    have := hw.trans_le (mul_le_mul_of_nonneg_right
      ((min_le_right _ _).trans (min_le_right _ _)) hr.le)
    linarith
  let x : ℂ := r⁻¹ • (u-w)
  have hx : x ∈ sphere (0 : ℂ) 4 := by
    rw [mem_sphere, dist_zero_right]
    simp only [x, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    have hu' : dist u w = 4*r := mem_sphere.mp hu
    rw [dist_eq_norm] at hu'
    rw [hu']
    field_simp
  have hxu : r • x + w = u := by
    change r • (r⁻¹ • (u-w)) + w = u
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  let v := u + (z-w)
  have hvdist : dist v z = dist u w := by
    simp only [v, dist_eq_norm]
    exact congrArg norm (show u + (z-w) - z = u-w by abel)
  have hv : v ∈ sphere z (4*r) := by rw [mem_sphere, hvdist]; exact mem_sphere.mp hu
  have huv : dist u v = dist w z := by
    simp only [v, dist_eq_norm]
    exact congrArg norm (show u - (u + (z-w)) = w-z by abel)
  have huA : u ∈ annulus z (3*r) (5*r) := by
    have hu' : dist u w = 4*r := mem_sphere.mp hu
    have h1 := dist_triangle u w z
    have h2 := dist_triangle u z w
    simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le]
    constructor <;> linarith [dist_comm z w]
  let C : Set ℂ := {q | r*(3+κ) ≤ dist q z ∧ dist q z ≤ r*(5-κ)}
  let X := (annulus z (3*r) (5*r) ∩ Y) ∪ (annulus z (3*r) (5*r) \ C)
  have hC : IsClosed C := (isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
    (isClosed_le (continuous_id.dist continuous_const) continuous_const)
  have hA : MeasurableSet (annulus z (3*r) (5*r)) :=
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hX : MeasurableSet X := (hA.inter hY).union (hA.diff hC.measurableSet)
  have hXA : X ⊆ annulus z (3*r) (5*r) := union_subset inter_subset_left sdiff_subset
  have hbound := hstart r hr μ z a b hfin hg u v hv (by rw [huv]; exact hws)
    huA X hX hXA (hmass Y hY hYsub hYmass)
  have hcomp := hcompare r hr z w hwc x hx Y
  rw [hxu] at hcomp
  exact hcomp.trans ((add_le_add hbound le_rfl).trans hbudget)

end HarmonicBalls.Section6
