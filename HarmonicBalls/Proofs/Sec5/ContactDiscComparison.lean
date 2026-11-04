import HarmonicBalls.Proofs.Sec5.GeneralDomainDiscLocality
import HarmonicBalls.Proofs.Sec5.CountableTimeMeasurability
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility
import HarmonicBalls.Proofs.Sec3.Basic

/-!
# Comparing disc clusters at first boundary contact

The clusters in a smaller and a larger disc agree at a positive time if
all earlier clusters agree and both families are increasing. This applies
at first boundary contact, since earlier compact clusters are compatible.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Pointwise

universe u

/-- Disc clusters are monotone in the radius for any measure at nonnegative
mass, by comparison with the harmonic Green-function difference. -/
theorem cluster_subset_cluster_larger_disc
    {μ : Measure ℂ} {r R t : ℝ} {z : ℂ}
    (hrR : r < R) (hz : z ∈ ball (0 : ℂ) r) (ht : 0 ≤ t) :
    cluster μ r z t ⊆ cluster μ R z t := by
  have hr : 0 < r := pos_of_mem_ball hz
  have hh := harmonicOnNhd_greenBallDifference hrR.le hz
  have hc : ContinuousOn (greenBallDifference r R z) (closure (ball 0 r)) := by
    intro x hx
    exact (hh x (by simpa [closure_ball _ hr.ne'] using hx)).1.continuousAt.continuousWithinAt
  have hG : ∀ x ∈ closure (ball (0 : ℂ) r), x ≠ z →
      greenFunction (ball 0 r) z x - greenFunction (ball 0 R) z x =
        greenBallDifference r R z x := by
    intro x hx hxz
    exact greenFunction_sub_eq_greenBallDifference hrR hz
      (by simpa [closure_ball _ hr.ne'] using hx) hxz
  have h := clusterOn_subset_cluster_of_green_difference_of_nonneg (μ := μ)
    isOpen_ball (ball_subset_ball hrR.le) ht hc (hh.mono ball_subset_closedBall) hG
  rwa [clusterOn_ball μ hr.ne' z t] at h

/-- Increasing disc clusters that agree at every earlier positive time also
agree at the limiting positive time. -/
theorem cluster_eq_of_eq_at_earlier_times
    {μ : Measure ℂ} {r R t : ℝ} {z : ℂ} (ht : 0 < t)
    (hsmall : ∀ s ∈ Ioo (0 : ℝ) t, cluster μ r z s ⊆ cluster μ r z t)
    (hlarge : ∀ s ∈ Ioo (0 : ℝ) t, cluster μ R z s ⊆ cluster μ R z t)
    (heq : ∀ s ∈ Ioo (0 : ℝ) t, cluster μ r z s = cluster μ R z s) :
    cluster μ r z t = cluster μ R z t := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨q, hq0, hqt, hqx⟩ := mem_cluster_exists_earlier_rat ht hx
    exact hlarge q ⟨hq0, hqt⟩ ((heq q ⟨hq0, hqt⟩) ▸ hqx)
  · intro x hx
    obtain ⟨q, hq0, hqt, hqx⟩ := mem_cluster_exists_earlier_rat ht hx
    exact hsmall q ⟨hq0, hqt⟩ ((heq q ⟨hq0, hqt⟩).symm ▸ hqx)

/-- An LQG disc cluster at its first boundary contact agrees with the cluster
in any fixed larger centred disc. The event may depend on that larger radius. -/
theorem ae_cluster_eq_larger_disc_at_first_contact
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {R : ℝ} (hR : 1 < R) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      (∀ s ∈ Ioo (0 : ℝ) t, closure (cluster (μ ω) 1 z s) ⊆ ball 0 1) →
      cluster (μ ω) 1 z t = cluster (μ ω) R z t := by
  filter_upwards [clusterCompatibility_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ R
      (by linarith), clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hcompat hmono
  intro z hz t ht hcl
  apply cluster_eq_of_eq_at_earlier_times ht
  · intro s hs
    exact hmono s t 1 hs.1 hs.2.le (by norm_num) z hz
  · intro s hs
    exact hmono s t R hs.1 hs.2.le (by linarith) z (ball_subset_ball hR.le hz)
  · intro s hs
    exact (hcompat s hs.1 1 hR.le z hz 1 ⟨le_rfl, hR.le⟩ (hcl s hs)
      R ⟨hR.le, le_rfl⟩).symm

/-- Right continuity in a larger disc transfers to the smaller disc at a time
when their clusters agree. -/
theorem cluster_right_continuity_of_larger_disc
    {μ : Measure ℂ} {r R t : ℝ} {z : ℂ} (hrR : r < R)
    (hz : z ∈ ball (0 : ℂ) r) (ht : 0 ≤ t)
    (heq : cluster μ r z t = cluster μ R z t)
    (hright : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (cluster μ R z s) ⊆ cluster μ R z t + ball (0 : ℂ) ε) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (cluster μ r z s) ⊆ cluster μ r z t + ball (0 : ℂ) ε := by
  intro ε hε
  obtain ⟨δ, hδ, hδbound⟩ := hright ε hε
  refine ⟨δ, hδ, fun s hs => ?_⟩
  rw [heq]
  exact (closure_mono (cluster_subset_cluster_larger_disc hrR hz (ht.trans hs.1))).trans
    (hδbound s hs)

/-- The larger-disc cluster is compactly contained there at first contact. -/
theorem cluster_closure_subset_larger_disc_of_eq
    {μ : Measure ℂ} {r R t : ℝ} {z : ℂ} (hrR : r < R)
    (heq : cluster μ r z t = cluster μ R z t) :
    closure (cluster μ R z t) ⊆ ball 0 R := by
  rw [← heq]
  exact (closure_minimal (cluster_subset_ball.trans ball_subset_closedBall)
    isClosed_closedBall).trans (closedBall_subset_ball hrR)

end HarmonicBalls
