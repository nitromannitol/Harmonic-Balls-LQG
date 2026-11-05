import HarmonicBalls.Proofs.Sec6.BrownianConeInstantHit
import HarmonicBalls.Proofs.Sec6.BoundaryRegularityRestart
import HarmonicBalls.Proofs.Sec6.CollarReturnAnnulusTranslation

/-! # Brownian regularity at annulus boundaries

Local exterior cones at the two circular boundaries imply instantaneous exit
from the closure of an annulus.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology InnerProductSpace

/-- A nonzero radial vector determines an open cone about its direction. -/
def radialCone (d : ℂ) : Set ℂ := {v | ‖d‖ * ‖v‖ < 2 * ⟪d, v⟫_ℝ}

theorem isOpen_radialCone (d : ℂ) : IsOpen (radialCone d) := by
  apply isOpen_lt <;> fun_prop

theorem radialCone_nonempty {d : ℂ} (hd : d ≠ 0) : (radialCone d).Nonempty := by
  refine ⟨d, ?_⟩
  have hn : 0 < ‖d‖ := norm_pos_iff.mpr hd
  simp only [radialCone, mem_ofPred_eq, real_inner_self_eq_norm_sq]
  nlinarith

theorem smul_mem_radialCone_iff (d v : ℂ) {a : ℝ} (ha : 0 < a) :
    a • v ∈ radialCone d ↔ v ∈ radialCone d := by
  simp only [radialCone, mem_ofPred_eq, norm_smul, Real.norm_eq_abs, abs_of_pos ha,
    real_inner_smul_right]
  constructor <;> intro h <;> nlinarith

/-- At a point of a positive-radius sphere, there is a local open cone pointing
into the ball. -/
theorem radialCone_inside_ball {z y : ℂ} {r : ℝ} (hr : 0 < r)
    (hy : dist y z = r) {w : ℂ}
    (hw : w - y ∈ radialCone (z - y)) (hsmall : dist w y < r) :
    dist w z < r := by
  have hd : ‖z - y‖ = r := by simpa [dist_eq_norm, norm_sub_rev] using hy
  have hv : ‖w - y‖ < r := by simpa [dist_eq_norm] using hsmall
  have hc : ‖z - y‖ * ‖w - y‖ < 2 * ⟪z - y, w - y⟫_ℝ := hw
  have heq : w - z = (w - y) - (z - y) := by abel
  have hs := norm_sub_sq_real (w - y) (z - y)
  rw [real_inner_comm] at hs
  rw [hd] at hc hs
  have hn := norm_nonneg (w - y)
  have hz := norm_nonneg (w - z)
  rw [heq] at hz
  rw [dist_eq_norm, heq]
  nlinarith [sq_nonneg (r - ‖w - y‖)]

/-- At a point of a positive-radius sphere, an outward radial cone stays
outside the closed ball. -/
theorem radialCone_outside_closedBall {z y : ℂ} {r : ℝ} (hr : 0 < r)
    (hy : dist y z = r) {w : ℂ}
    (hw : w - y ∈ radialCone (y - z)) :
    r < dist w z := by
  have hd : ‖y - z‖ = r := by simpa [dist_eq_norm] using hy
  have hc : ‖y - z‖ * ‖w - y‖ < 2 * ⟪y - z, w - y⟫_ℝ := hw
  have heq : w - z = (y - z) + (w - y) := by abel
  have hs := norm_add_sq_real (y - z) (w - y)
  rw [hd] at hc hs
  have hn := norm_nonneg (w - y)
  have hz := norm_nonneg (w - z)
  rw [heq] at hz
  have hp : 0 ≤ r * ‖w - y‖ := mul_nonneg hr.le hn
  rw [dist_eq_norm, heq]
  nlinarith [sq_nonneg ‖w - y‖]

/-- Every point of the annulus closure lies between its two circles. -/
theorem closure_annulus_subset_radial_bounds (z : ℂ) (r R : ℝ) :
    closure (annulus z r R) ⊆ {w : ℂ | r ≤ dist w z ∧ dist w z ≤ R} := by
  apply closure_minimal
  · intro w hw
    simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] at hw
    exact ⟨hw.2.le, hw.1.le⟩
  · exact (isClosed_le continuous_const ((continuous_id.dist continuous_const))).inter
      (isClosed_le ((continuous_id.dist continuous_const)) continuous_const)

/-- Brownian motion started on either circle exits the closed annulus instantly. -/
theorem ae_planarBrownian_exit_closure_annulus_of_boundary
    {z y : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hy : dist y z = r ∨ dist y z = R) :
    ∀ᵐ ω ∂planarBrownianMotion y,
      ContinuousPath.exitTime (closure (annulus z r R)) ω = 0 := by
  rcases hy with hi | ho
  · have hd : z - y ≠ 0 := by
      intro h
      have : dist y z = 0 := by rw [dist_eq_zero]; exact (sub_eq_zero.mp h).symm
      linarith
    apply ae_planarBrownian_exitTime_eq_zero_of_local_exterior_cone y
      (closure (annulus z r R)) (radialCone (z - y)) (isOpen_radialCone _) (radialCone_nonempty hd)
      (fun a ha v => smul_mem_radialCone_iff _ _ ha) hr
    intro w hw hsmall hmem
    have hb := (closure_annulus_subset_radial_bounds z r R) hmem
    change r ≤ dist w z ∧ dist w z ≤ R at hb
    have hh := radialCone_inside_ball hr hi hw hsmall
    linarith
  · have hR : 0 < R := lt_trans hr hrR
    have hd : y - z ≠ 0 := by
      intro h
      have : dist y z = 0 := by rw [dist_eq_zero]; exact sub_eq_zero.mp h
      linarith
    apply ae_planarBrownian_exitTime_closed_eq_zero_of_exterior_cone y
      (closure (annulus z r R)) (radialCone (y - z)) (isOpen_radialCone _) (radialCone_nonempty hd)
      (fun a ha v => smul_mem_radialCone_iff _ _ ha)
    intro w hw hmem
    have hb := (closure_annulus_subset_radial_bounds z r R) hmem
    change r ≤ dist w z ∧ dist w z ≤ R at hb
    have hh := radialCone_outside_closedBall hR ho hw
    linarith

/-- The exit times from an annulus and its closure agree almost surely for a
planar Brownian motion started in the annulus. -/
theorem ae_planarBrownian_exitTime_closure_annulus_eq
    {z x : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hx : x ∈ annulus z r R) :
    ∀ᵐ ω ∂planarBrownianMotion x,
      ContinuousPath.exitTime (closure (annulus z r R)) ω =
        ContinuousPath.exitTime (annulus z r R) ω := by
  have hopen : IsOpen (annulus z r R) := isOpen_ball.sdiff isClosed_closedBall
  apply ae_exitTime_closure_eq_of_boundary_instant_exit hopen
    (isBounded_ball.subset sdiff_subset) hx
  intro y hy
  have hbounds := (closure_annulus_subset_radial_bounds z r R) (frontier_subset_closure hy)
  have hnot : y ∉ annulus z r R := by
    rw [hopen.frontier_eq] at hy
    exact hy.2
  have hcircles : dist y z = r ∨ dist y z = R := by
    by_contra hh
    have hneq : dist y z ≠ r ∧ dist y z ≠ R := not_or.mp hh
    apply hnot
    simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
    exact ⟨lt_of_le_of_ne hbounds.2 hneq.2, lt_of_le_of_ne hbounds.1 (Ne.symm hneq.1)⟩
  exact ae_planarBrownian_exit_closure_annulus_of_boundary hr hrR hcircles

/-- Collar-return probabilities vanish for an open exhaustion and a decreasing
outer approximation of a positive-radius annulus. -/
theorem tendsto_annulus_core_return_probability
    {z x : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {D A : ℕ → Set ℂ} (hDopen : ∀ n, IsOpen (D n)) (hDmono : Monotone D)
    (hDunion : (⋃ n, D n) = annulus z r R)
    (hAopen : ∀ n, IsOpen (A n)) (hAanti : Antitone A)
    (hAinter : (⋂ n, A n) = closure (annulus z r R))
    {C : Set ℂ} (hC : IsClosed C) (hCA : C ⊆ annulus z r R)
    (hx : x ∈ annulus z r R) :
    Tendsto (fun n => planarBrownianMotion x {ω | ∃ t : ℝ≥0,
      ContinuousPath.exitTime (D n) ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (A n) ω ∧ ω t ∈ C}) atTop (𝓝 0) := by
  apply tendsto_core_return_probability_of_regular_boundary hDopen hDmono hAopen hAanti
  · simpa only [hDunion] using hAinter
  · rw [hDunion]
    exact isBounded_ball.subset sdiff_subset
  · exact hC
  · simpa only [hDunion] using hCA
  · simpa only [hDunion] using hx
  · simpa only [hDunion] using ae_planarBrownian_exitTime_closure_annulus_eq hr hrR hx

end HarmonicBalls.Section6
