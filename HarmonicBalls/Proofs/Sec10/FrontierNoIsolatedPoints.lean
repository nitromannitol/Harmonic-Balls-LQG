import HarmonicBalls.Proofs.Sec10.FrontierMinimalSeparation

/-!
# Complementary frontiers have no isolated points

A punctured disk is connected. A common boundary point of two disjoint open
sets is therefore an accumulation point of their common frontier.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- A punctured planar ball is preconnected, as the exponential image of a
half-plane. -/
theorem isPreconnected_punctured_complex_ball (p : ℂ) {r : ℝ} (hr : 0 < r) :
    IsPreconnected (ball p r \ {p}) := by
  have hS : IsPreconnected {c : ℂ | c.re < Real.log r} :=
    (convex_halfSpace_re_lt (Real.log r)).isPreconnected
  have heq : (fun c : ℂ => p + Complex.exp c) '' {c : ℂ | c.re < Real.log r} =
      ball p r \ {p} := by
    ext w
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
        exact (Real.exp_lt_exp.mpr hc).trans_eq (Real.exp_log hr)
      · simp [Complex.exp_ne_zero]
    · rintro ⟨hw, hwp⟩
      have hne : w - p ≠ 0 := sub_ne_zero.mpr (by simpa using hwp)
      rw [mem_ball, dist_eq_norm] at hw
      refine ⟨Complex.log (w - p), ?_, ?_⟩
      · change (Complex.log (w - p)).re < Real.log r
        rw [Complex.log_re]
        exact Real.log_lt_log (norm_pos_iff.mpr hne) hw
      · change p + Complex.exp (Complex.log (w - p)) = w
        rw [Complex.exp_log hne, add_sub_cancel]
  rw [← heq]
  exact hS.image _ (continuous_const.add Complex.continuous_exp).continuousOn

/-- Every common frontier point of two disjoint open sets is an accumulation
point of the frontier of the second, when that frontier lies in the frontier
of the first. -/
theorem frontier_no_isolated_points_of_subset_frontier
    {G U : Set ℂ} (hGo : IsOpen G) (hUo : IsOpen U)
    (hdis : Disjoint G U) (hfront : frontier U ⊆ frontier G)
    {p : ℂ} (hp : p ∈ frontier U) {r : ℝ} (hr : 0 < r) :
    ∃ q ∈ frontier U, q ∈ ball p r ∧ q ≠ p := by
  classical
  by_contra h
  have hball : ball p r \ {p} ⊆ (frontier U)ᶜ := by
    intro q hq hqf
    apply h
    exact ⟨q, hqf, hq.1, by simpa using hq.2⟩
  have hpG : p ∈ closure G := frontier_subset_closure (hfront hp)
  have hpU : p ∈ closure U := frontier_subset_closure hp
  obtain ⟨x, hxb, hxG⟩ := mem_closure_iff.mp hpG _ isOpen_ball (mem_ball_self hr)
  obtain ⟨y, hyb, hyU⟩ := mem_closure_iff.mp hpU _ isOpen_ball (mem_ball_self hr)
  have hpGn : p ∉ G := by
    have h := hfront hp
    rw [hGo.frontier_eq] at h
    exact h.2
  have hpUn : p ∉ U := by
    rw [hUo.frontier_eq] at hp
    exact hp.2
  have hxne : x ≠ p := by rintro rfl; exact hpGn hxG
  have hyne : y ≠ p := by rintro rfl; exact hpUn hyU
  have hxball : x ∈ ball p r \ {p} := ⟨hxb, by simpa using hxne⟩
  have hyball : y ∈ ball p r \ {p} := ⟨hyb, by simpa using hyne⟩
  have hycomp := (isPreconnected_punctured_complex_ball p hr).subset_connectedComponentIn
    hxball hball hyball
  have hxU : x ∉ U := fun hxU => disjoint_left.mp hdis hxG hxU
  exact not_mem_connectedComponentIn_compl_frontier hUo hxU (hball hxball) hyU hycomp

/-- Almost surely, complementary frontiers of compactly contained clusters
have no isolated points. Only the volume-growth input is used. -/
theorem ae_cluster_frontier_no_isolated_points
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      ∀ p ∈ frontier U, ∀ r : ℝ, 0 < r →
        ∃ q ∈ frontier U, q ∈ ball p r ∧ q ≠ p := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterComplementComponent_geometry_of_volumeGrowth P γ α₀ hγ hγ2 hα
      hC hcirc μ hGFF hμ hI2,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hgeom hcluster
  intro t ht z hz hcl U hU p hp r hr
  have hg := hgeom t 1 ht zero_lt_one z hz hcl U hU
  have hc := hcluster t 1 ht zero_lt_one z hz
  obtain ⟨v, hv, hUeq⟩ := hU
  have hUs : U ⊆ (closure (cluster (μ ω) 1 z t))ᶜ := by
    rw [← hUeq]
    exact connectedComponentIn_subset _ _
  have hdis : Disjoint (cluster (μ ω) 1 z t) U := by
    rw [disjoint_left]
    intro w hw hwU
    exact hUs hwU (subset_closure hw)
  exact frontier_no_isolated_points_of_subset_frontier hc.1 hg.1 hdis hg.2.2.2.1 hp hr

end HarmonicBalls
