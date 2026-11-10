import HarmonicBalls.FirstPass.S11r.InternalDeletion
import HarmonicBalls.Steps.Sec11.MetricConstantScaling

/-!
# First pass, rooted gluing across the root (fp-S11r part (b), owner n2)

Deterministic step from the local identities (26) to the rooted identity (20) of `LocalMetricReplacementStmt`
(CHATGPT-n3-B1-B2.md sections 4.2-4.3). Let `d` be the decoder output and `e` the physical metric of the rooted field,
both length metrics on an open disk `D` containing the root `z`. If, on every open `V ⊆ D` whose closure avoids `z`,
the internal metric of `d` is the constant `c > 0` times the internal metric of `e`, and both `d` and `e` tend to `0`
at `z` within `D`, then `d = c · e` on `D`. The constant `c = c(z, ω)` is the scalar `b` of (20).

The decoder's continuity at `z` is part of its statement (continuous on `D × D`). The continuity of the physical metric
at the insertion, `he_cont`, is the external input DFGPS arXiv:1905.00380v2 Prop 3.17 (pending; not staged here).
-/

namespace HarmonicBalls

open Set Filter Topology Metric
open scoped ENNReal

/-- **Rooted gluing** (CHATGPT-n3-B1-B2.md section 4.3): two length metrics on an open `D` which agree up to the
constant `c > 0` on every open disk of `D` avoiding the root `z`, and tend to `0` at `z`, agree up to `c` on `D`. -/
theorem eq_const_mul_of_disk_agreement {D : Set ℂ} (hD : IsOpen D) {z : ℂ} (hz : z ∈ D)
    {d e : ℂ → ℂ → ℝ} {c : ℝ} (hc : 0 < c)
    (hd_symm : ∀ x y, d x y = d y x) (he_symm : ∀ x y, e x y = e y x)
    (hd_tri : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, d x w ≤ d x y + d y w)
    (he_tri : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, e x w ≤ e x y + e y w)
    (hd_len : ∀ x ∈ D, ∀ y ∈ D, ENNReal.ofReal (d x y) = internalMetric d D x y)
    (he_len : ∀ x ∈ D, ∀ y ∈ D, ENNReal.ofReal (e x y) = internalMetric e D x y)
    (hd_cont : Tendsto (fun x => d x z) (𝓝[D] z) (𝓝 0))
    (he_cont : Tendsto (fun x => e x z) (𝓝[D] z) (𝓝 0))
    (hdisk : ∀ V : Set ℂ, IsOpen V → V ⊆ D → z ∉ closure V → ∀ x ∈ V, ∀ y ∈ V,
      internalMetric d V x y = internalMetric (fun a b => c * e a b) V x y) :
    ∀ x ∈ D, ∀ y ∈ D, d x y = c * e x y := by
  have he_c_symm : ∀ x y, c * e x y = c * e y x := fun x y => by rw [he_symm x y]
  have he_c_tri : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, c * e x w ≤ c * e x y + c * e y w := by
    intro x hx y hy w hw
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (he_tri x hx y hy w hw) hc.le
  have he_c_len : ∀ x ∈ D, ∀ y ∈ D,
      ENNReal.ofReal (c * e x y) = internalMetric (fun a b => c * e a b) D x y := by
    intro x hx y hy
    rw [internalMetric_const_mul e hc D x y, ENNReal.ofReal_mul hc.le, he_len x hx y hy]
  have he_c_cont : Tendsto (fun x => c * e x z) (𝓝[D] z) (𝓝 0) := by
    simpa using he_cont.const_mul c
  have hloc : ∀ q ∈ D, q ≠ z → ∃ V : Set ℂ, IsOpen V ∧ q ∈ V ∧ V ⊆ D ∧
      ∀ x ∈ V, ∀ y ∈ V, internalMetric d V x y = internalMetric (fun a b => c * e a b) V x y := by
    intro q hq hqz
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hD q hq
    have hdist : 0 < dist q z := dist_pos.mpr hqz
    have hρ : 0 < min ε (dist q z / 2) := lt_min hε (half_pos hdist)
    have hsub : ball q (min ε (dist q z / 2)) ⊆ D := (ball_subset_ball (min_le_left _ _)).trans hball
    refine ⟨ball q (min ε (dist q z / 2)), isOpen_ball, mem_ball_self hρ, hsub, ?_⟩
    have hzV : z ∉ closure (ball q (min ε (dist q z / 2))) := by
      intro hz'
      have h1 : z ∈ closedBall q (min ε (dist q z / 2)) := closure_ball_subset_closedBall hz'
      rw [mem_closedBall, dist_comm] at h1
      have h2 := min_le_right ε (dist q z / 2)
      linarith
    intro x hx y hy
    exact hdisk _ isOpen_ball hsub hzV x hx y hy
  exact eq_of_local_internalMetric_agreement_off_point hD hz hd_symm he_c_symm hd_tri he_c_tri hd_len he_c_len
    hd_cont he_c_cont hloc

end HarmonicBalls
