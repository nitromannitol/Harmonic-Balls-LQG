import HarmonicBalls.Draft.Section11

/-! # Crossings of a domain boundary by a continuous path -/

namespace HarmonicBalls

open Set Metric Topology

/-- If a path is outside an open set and later ends inside it, it meets the
frontier at an intermediate time. -/
theorem path_meets_frontier_after {w a : ℂ} (p : Path w a) {A : Set ℂ}
    (hA : IsOpen A) (ha : a ∈ A) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hout : p.extend s ∉ A) :
    ∃ t ∈ Icc s 1, p.extend t ∈ frontier A := by
  let S := p.extend '' Icc s 1
  have hconn : IsPreconnected S := isPreconnected_Icc.image p.extend p.continuous_extend.continuousOn
  have haS : a ∈ S := ⟨1, ⟨hs.2, le_rfl⟩, p.extend_one⟩
  have hsS : p.extend s ∈ S := ⟨s, ⟨le_rfl, hs.2⟩, rfl⟩
  by_contra hn
  push Not at hn
  have hsubset : closure A ∩ S ⊆ A := by
    intro x hx
    by_contra hxA
    have hfront : x ∈ frontier A := by
      rw [hA.frontier_eq]
      exact ⟨hx.1, hxA⟩
    obtain ⟨t, ht, rfl⟩ := hx.2
    exact hn t ht hfront
  have hSA : S ⊆ A := hconn.subset_of_closure_inter_subset hA ⟨a, haS, ha⟩ hsubset
  exact hout (hSA hsS)

/-- A nonzero rescaling and translation takes open sets to open sets. -/
theorem isOpen_rescaledSet {A : Set ℂ} (hA : IsOpen A) {r : ℝ} (hr : r ≠ 0) (z : ℂ) :
    IsOpen (rescaledSet A r z) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  let e : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ (r : ℂ) hr').trans (Homeomorph.addRight z)
  exact e.isOpenMap A hA

/-- Scaling a set inside the radius-five ball puts it in the corresponding
translated ball. -/
theorem rescaledSet_subset_ball {A : Set ℂ} (hA : A ⊆ ball 0 5)
    {r : ℝ} (hr : 0 < r) (z : ℂ) : rescaledSet A r z ⊆ ball z (5 * r) := by
  rintro q ⟨a, ha, rfl⟩
  have ha' : ‖a‖ < 5 := by simpa [Metric.mem_ball, dist_zero_right] using hA ha
  rw [Metric.mem_ball, dist_eq_norm]
  simp only [add_sub_cancel_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  nlinarith

/-- A path whose endpoints lie on opposite sides of a Euclidean sphere meets
that sphere. -/
theorem path_meets_sphere_between {w a z : ℂ} (p : Path w a) {ρ : ℝ}
    (hw : ρ ≤ dist w z) (ha : dist a z ≤ ρ) :
    ∃ t ∈ Icc (0 : ℝ) 1, p.extend t ∈ sphere z ρ := by
  have hc : Continuous fun t : ℝ => dist (p.extend t) z :=
    p.continuous_extend.dist continuous_const
  have hm := intermediate_value_Icc' (zero_le_one' ℝ) hc.continuousOn
  have hmem : ρ ∈ Icc (dist (p.extend 1) z) (dist (p.extend 0) z) := by
    simpa only [p.extend_one, p.extend_zero] using ⟨ha, hw⟩
  obtain ⟨t, ht, heq⟩ := hm hmem
  exact ⟨t, ht, heq⟩

/-- Positive rescaling takes an annulus to the corresponding translated annulus. -/
theorem rescaledSet_annulus_subset (a b : ℝ) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    rescaledSet (annulus 0 a b) r z ⊆ annulus z (a * r) (b * r) := by
  rintro q ⟨x, hx, rfl⟩
  have hdist : dist ((r : ℂ) * x + z) z = r * ‖x‖ := by
    simp only [dist_eq_norm, add_sub_cancel_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
  have hx' : ‖x‖ < b ∧ ¬ ‖x‖ ≤ a := by
    simpa only [annulus, mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, dist_zero_right] using hx
  change dist ((r : ℂ) * x + z) z < b * r ∧ ¬ dist ((r : ℂ) * x + z) z ≤ a * r
  rw [hdist]
  constructor <;> nlinarith

end HarmonicBalls
