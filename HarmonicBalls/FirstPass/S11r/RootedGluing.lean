import HarmonicBalls.FirstPass.S11r.InternalDeletion
import HarmonicBalls.Steps.Sec11.MetricConstantScaling

/-!
# rooted gluing across the root

Deterministic step from the local identities (26) to the rooted identity (20) of `LocalMetricReplacementStmt`
. Let `d` be the decoder output and `e` the physical metric of the rooted field,
both length metrics on an open disk `D` containing the root `z`. If the internal metric of `d` is the constant `c > 0`
times the internal metric of `e` on each member of a cover of `D ∖ {z}` by open sets, and both `d` and `e` tend to `0`
at `z` within `D`, then `d = c · e` on `D`. The constant `c = c(z, ω)` is the scalar `b` of (20).

The cover can be taken to be rational disks (`eq_const_mul_of_rat_disk_agreement`), which is the countable family on
which (22) and (26) are checked. The decoder's continuity at `z` is part of its statement (continuous on `D × D`). The
continuity of the physical metric at the insertion, `he_cont`, is the external input DFGPS arXiv:1905.00380v2 Prop 3.17
(pending; not staged here).
-/

namespace HarmonicBalls

open Set Filter Topology Metric
open scoped ENNReal

/-- **Rooted gluing, local form**: two length metrics on an open `D ∋ z`, which are
`c`-proportional on a neighbourhood of each point of `D ∖ {z}`, and tend to `0` at `z`, are `c`-proportional on `D`. -/
theorem eq_const_mul_of_local_agreement {D : Set ℂ} (hD : IsOpen D) {z : ℂ} (hz : z ∈ D)
    {d e : ℂ → ℂ → ℝ} {c : ℝ} (hc : 0 < c)
    (hd_symm : ∀ x y, d x y = d y x) (he_symm : ∀ x y, e x y = e y x)
    (hd_tri : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, d x w ≤ d x y + d y w)
    (he_tri : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, e x w ≤ e x y + e y w)
    (hd_len : ∀ x ∈ D, ∀ y ∈ D, ENNReal.ofReal (d x y) = internalMetric d D x y)
    (he_len : ∀ x ∈ D, ∀ y ∈ D, ENNReal.ofReal (e x y) = internalMetric e D x y)
    (hd_cont : Tendsto (fun x => d x z) (𝓝[D] z) (𝓝 0))
    (he_cont : Tendsto (fun x => e x z) (𝓝[D] z) (𝓝 0))
    (hloc : ∀ q ∈ D, q ≠ z → ∃ V : Set ℂ, IsOpen V ∧ q ∈ V ∧ V ⊆ D ∧
      ∀ x ∈ V, ∀ y ∈ V, internalMetric d V x y = internalMetric (fun a b => c * e a b) V x y) :
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
  exact eq_of_local_internalMetric_agreement_off_point hD hz hd_symm he_c_symm hd_tri he_c_tri hd_len he_c_len
    hd_cont he_c_cont hloc

/-- **Rooted gluing, disk form**: agreement up to `c` on every open disk of `D` whose closure avoids the root. -/
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
  refine eq_const_mul_of_local_agreement hD hz hc hd_symm he_symm hd_tri he_tri hd_len he_len hd_cont he_cont ?_
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

/-- A rational disk around `q` inside `D` whose closure avoids `z`: the centre is `m + n i` and the radius `s`, with
`m, n, s ∈ ℚ`. -/
theorem exists_rat_ball_avoid {D : Set ℂ} (hD : IsOpen D) {z q : ℂ} (hq : q ∈ D) (hqz : q ≠ z) :
    ∃ m n s : ℚ, 0 < s ∧ ball ((m : ℝ) + (n : ℝ) * Complex.I) (s : ℝ) ⊆ D ∧
      z ∉ closure (ball ((m : ℝ) + (n : ℝ) * Complex.I) (s : ℝ)) ∧
      q ∈ ball ((m : ℝ) + (n : ℝ) * Complex.I) (s : ℝ) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hD q hq
  have hdist : 0 < dist q z := dist_pos.mpr hqz
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (ε / 4) (dist q z / 4) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; exact lt_min (by linarith) (by linarith)
  have hδε : δ ≤ ε / 4 := by rw [hδ]; exact min_le_left _ _
  have hδz : 4 * δ ≤ dist q z := by
    rw [hδ]; have := min_le_right (ε / 4) (dist q z / 4); linarith
  obtain ⟨m, hm1, hm2⟩ := exists_rat_btwn (show q.re - δ / 4 < q.re + δ / 4 by linarith)
  obtain ⟨n, hn1, hn2⟩ := exists_rat_btwn (show q.im - δ / 4 < q.im + δ / 4 by linarith)
  set w : ℂ := (m : ℝ) + (n : ℝ) * Complex.I with hw
  have hwq : dist w q < δ / 2 := by
    have hre : |(w - q).re| < δ / 4 := by
      have : (w - q).re = (m : ℝ) - q.re := by simp [hw]
      rw [this, abs_lt]; constructor <;> linarith
    have him : |(w - q).im| < δ / 4 := by
      have : (w - q).im = (n : ℝ) - q.im := by simp [hw]
      rw [this, abs_lt]; constructor <;> linarith
    rw [dist_eq_norm]
    have h := Complex.norm_le_abs_re_add_abs_im (w - q)
    linarith
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn (show dist w q < δ by linarith)
  have hspos : (0 : ℝ) < s := lt_of_le_of_lt dist_nonneg hs1
  refine ⟨m, n, s, by exact_mod_cast hspos, ?_, ?_, ?_⟩
  · intro x hx
    apply hball
    rw [mem_ball] at hx ⊢
    have := dist_triangle x w q
    linarith
  · intro hz'
    have h1 : z ∈ closedBall w s := closure_ball_subset_closedBall hz'
    rw [mem_closedBall] at h1
    have h3 := dist_triangle z w q
    have h4 := dist_comm q z
    linarith
  · rw [mem_ball, dist_comm]
    exact hs1

/-- **Rooted gluing, rational-disk form**: the hypothesis (26) is needed only on the countable family of rational disks
`ball (m + n i) s` (`m, n, s ∈ ℚ`) that avoid the root. -/
theorem eq_const_mul_of_rat_disk_agreement {D : Set ℂ} (hD : IsOpen D) {z : ℂ} (hz : z ∈ D)
    {d e : ℂ → ℂ → ℝ} {c : ℝ} (hc : 0 < c)
    (hd_symm : ∀ x y, d x y = d y x) (he_symm : ∀ x y, e x y = e y x)
    (hd_tri : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, d x w ≤ d x y + d y w)
    (he_tri : ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, e x w ≤ e x y + e y w)
    (hd_len : ∀ x ∈ D, ∀ y ∈ D, ENNReal.ofReal (d x y) = internalMetric d D x y)
    (he_len : ∀ x ∈ D, ∀ y ∈ D, ENNReal.ofReal (e x y) = internalMetric e D x y)
    (hd_cont : Tendsto (fun x => d x z) (𝓝[D] z) (𝓝 0))
    (he_cont : Tendsto (fun x => e x z) (𝓝[D] z) (𝓝 0))
    (hdisk : ∀ m n s : ℚ, 0 < s → ball ((m : ℝ) + (n : ℝ) * Complex.I) (s : ℝ) ⊆ D →
      z ∉ closure (ball ((m : ℝ) + (n : ℝ) * Complex.I) (s : ℝ)) →
      ∀ x ∈ ball ((m : ℝ) + (n : ℝ) * Complex.I) (s : ℝ), ∀ y ∈ ball ((m : ℝ) + (n : ℝ) * Complex.I) (s : ℝ),
        internalMetric d (ball ((m : ℝ) + (n : ℝ) * Complex.I) (s : ℝ)) x y =
          internalMetric (fun a b => c * e a b) (ball ((m : ℝ) + (n : ℝ) * Complex.I) (s : ℝ)) x y) :
    ∀ x ∈ D, ∀ y ∈ D, d x y = c * e x y := by
  refine eq_const_mul_of_local_agreement hD hz hc hd_symm he_symm hd_tri he_tri hd_len he_len hd_cont he_cont ?_
  intro q hq hqz
  obtain ⟨m, n, s, hs, hsub, hzc, hqb⟩ := exists_rat_ball_avoid hD hq hqz
  exact ⟨_, isOpen_ball, hqb, hsub, hdisk m n s hs hsub hzc⟩

end HarmonicBalls
