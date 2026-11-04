import HarmonicBalls.Proofs.Sec10.CrossingImpliesNoHoles
import HarmonicBalls.Proofs.Sec10.FrontierNoIsolatedPoints

/-! # The exterior component and bounded holes

The complement of a compactly contained cluster has a distinguished exterior
component; every other complementary component is bounded. -/

namespace HarmonicBalls

open Set Metric Topology MeasureTheory Filter

universe u

/-- The exterior of a closed planar disk is preconnected. -/
theorem isPreconnected_compl_closedBall_complex (p : ℂ) {r : ℝ} (hr : 0 < r) :
    IsPreconnected (closedBall p r)ᶜ := by
  have hS : IsPreconnected {c : ℂ | Real.log r < c.re} :=
    (convex_halfSpace_re_gt (Real.log r)).isPreconnected
  have heq : (fun c : ℂ => p + Complex.exp c) '' {c : ℂ | Real.log r < c.re} =
      (closedBall p r)ᶜ := by
    ext w
    constructor
    · rintro ⟨c, hc, rfl⟩
      rw [mem_compl_iff, mem_closedBall, not_le, dist_eq_norm,
        add_sub_cancel_left, Complex.norm_exp]
      exact (Real.exp_lt_exp.mpr hc).trans_eq' (Real.exp_log hr)
    · intro hw
      have hw' : r < ‖w - p‖ := by
        simpa [mem_closedBall, dist_eq_norm, not_le] using hw
      have hne : w - p ≠ 0 := norm_pos_iff.mp (hr.trans hw')
      refine ⟨Complex.log (w - p), ?_, ?_⟩
      · change Real.log r < (Complex.log (w - p)).re
        rw [Complex.log_re]
        exact Real.log_lt_log hr hw'
      · change p + Complex.exp (Complex.log (w - p)) = w
        rw [Complex.exp_log hne, add_sub_cancel]
  rw [← heq]
  exact hS.image _ (continuous_const.add Complex.continuous_exp).continuousOn

/-- If a closed set is contained in a disk, every complementary component
other than the component containing the disk exterior is contained in the
closed disk. -/
theorem component_compl_subset_closedBall_of_ne_exterior
    {K : Set ℂ} {r : ℝ} (hr : 0 < r) (hK : K ⊆ closedBall 0 r)
    {p : ℂ} (hp : p ∈ (closedBall (0 : ℂ) r)ᶜ)
    {U : Set ℂ} (hU : U ∈ connectedComponentsIn Kᶜ)
    (hne : U ≠ connectedComponentIn Kᶜ p) : U ⊆ closedBall 0 r := by
  obtain ⟨q, hq, rfl⟩ := hU
  have hext : (closedBall (0 : ℂ) r)ᶜ ⊆ Kᶜ := compl_subset_compl.mpr hK
  intro x hx
  by_contra hxball
  have hxext : x ∈ (closedBall (0 : ℂ) r)ᶜ := hxball
  have hxcomp := (isPreconnected_compl_closedBall_complex 0 hr).subset_connectedComponentIn
    hp hext hxext
  exact hne ((connectedComponentIn_eq hx).trans (connectedComponentIn_eq hxcomp).symm)

/-- The component containing the disk exterior is unbounded. -/
theorem not_isBounded_exterior_component
    {K : Set ℂ} {r : ℝ} (hr : 0 < r) (hK : K ⊆ closedBall 0 r)
    {p : ℂ} (hp : p ∈ (closedBall (0 : ℂ) r)ᶜ) :
    ¬ Bornology.IsBounded (connectedComponentIn Kᶜ p) := by
  have hext : (closedBall (0 : ℂ) r)ᶜ ⊆ Kᶜ := compl_subset_compl.mpr hK
  have hsub := (isPreconnected_compl_closedBall_complex 0 hr).subset_connectedComponentIn
    hp hext
  intro hb
  have huniv : Bornology.IsBounded (univ : Set ℂ) := by
    simpa using (isCompact_closedBall (0 : ℂ) r).isBounded.union (hb.subset hsub)
  exact NormedSpace.unbounded_univ ℝ ℂ huniv

/-- For a set contained in a disk, disconnectedness of its complement is
exactly the existence of a bounded complementary component. -/
theorem not_isConnected_compl_iff_exists_bounded_component
    {K : Set ℂ} {r : ℝ} (hr : 0 < r) (hK : K ⊆ closedBall 0 r)
    {p : ℂ} (hp : p ∈ (closedBall (0 : ℂ) r)ᶜ) :
    ¬ IsConnected Kᶜ ↔ ∃ U ∈ connectedComponentsIn Kᶜ, Bornology.IsBounded U := by
  have hpK : p ∈ Kᶜ := (compl_subset_compl.mpr hK) hp
  have hne := not_isBounded_exterior_component hr hK hp
  constructor
  · intro hn
    by_contra h
    have hsub : Kᶜ ⊆ connectedComponentIn Kᶜ p := by
      intro x hx
      by_contra hxp
      have hU : connectedComponentIn Kᶜ x ∈ connectedComponentsIn Kᶜ := ⟨x, hx, rfl⟩
      have hUneq : connectedComponentIn Kᶜ x ≠ connectedComponentIn Kᶜ p := by
        intro heq
        exact hxp (heq ▸ mem_connectedComponentIn hx)
      have hb := component_compl_subset_closedBall_of_ne_exterior hr hK hp hU hUneq
      exact h ⟨_, hU, (isCompact_closedBall (0 : ℂ) r).isBounded.subset hb⟩
    have heq : Kᶜ = connectedComponentIn Kᶜ p :=
      Subset.antisymm hsub (connectedComponentIn_subset _ _)
    exact hn (heq ▸ (isConnected_connectedComponentIn_iff.mpr hpK))
  · rintro ⟨U, ⟨q, hq, rfl⟩, hb⟩ hc
    have hsub := hc.isPreconnected.subset_connectedComponentIn hpK (Subset.rfl)
    have hqext := hsub hq
    exact hne ((connectedComponentIn_eq hqext) ▸ hb)

/-- All components of the complement of a compactly contained unit-disc
cluster other than its exterior component are bounded. -/
theorem cluster_complement_component_bounded_of_ne_exterior
    {μ : Measure ℂ} {t : ℝ} {z : ℂ}
    (hcl : closure (cluster μ 1 z t) ⊆ ball 0 1)
    {U : Set ℂ} (hU : U ∈ connectedComponentsIn (closure (cluster μ 1 z t))ᶜ)
    (hne : U ≠ connectedComponentIn (closure (cluster μ 1 z t))ᶜ (2 : ℂ)) :
    Bornology.IsBounded U := by
  apply (isCompact_closedBall (0 : ℂ) 1).isBounded.subset
  apply component_compl_subset_closedBall_of_ne_exterior zero_lt_one
    (hcl.trans ball_subset_closedBall) ?_ hU hne
  norm_num [mem_closedBall, dist_eq_norm]

/-- Lemma 10.5 would rule out every bounded complementary component of a
compactly contained cluster. This is a consequence of the lemma, not an
independent assertion that clusters have no holes. -/
theorem ae_no_bounded_cluster_complement_component_of_crossing_containment
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h5 : CrossingComponentContainsClusterCrossingStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        ¬ Bornology.IsBounded U := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_compl_closure_connected_of_crossing_containment hI2 h5
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hω
  intro t ht z hz hcl U hU hb
  have hp : (2 : ℂ) ∈ (closedBall (0 : ℂ) 1)ᶜ := by
    norm_num [mem_closedBall, dist_eq_norm]
  have hn := (not_isConnected_compl_iff_exists_bounded_component zero_lt_one
    (hcl.trans ball_subset_closedBall) hp).mpr ⟨U, hU, hb⟩
  exact hn (hω t ht z hz hcl)

end HarmonicBalls
