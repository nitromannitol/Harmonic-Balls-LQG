import HarmonicBalls.Proofs.Sec5.LocalOdometerIncrement
import HarmonicBalls.Proofs.Sec3.ConservationOfMassStep3

/-! # Quantitative local mass growth

A compact ball separated from a cluster can acquire at most linear mass in a
time increment. The estimate is valid regardless of boundary contact.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology ENNReal

/-- A ball whose twice-radius closed ball lies in a pole-avoiding region
separated from the current cluster acquires mass at most linearly in time. -/
theorem cluster_closedBall_mass_le_time_increment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R \ {z})
    (hdis : Disjoint U (cluster μ R z t)) {w : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hball : closedBall w (2 * ρ) ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, t ≤ s →
      μ (closedBall w ρ ∩ cluster μ R z s) ≤ ENNReal.ofReal (C * (s - t)) := by
  let : IsLocallyFiniteMeasure μ := hμ
  let φ : ContDiffBump w := ⟨ρ, 2 * ρ, hρ, by linarith⟩
  have hφ : IsTestFunction U φ := by
    refine ⟨φ.contDiff, φ.hasCompactSupport, ?_⟩
    rw [φ.tsupport_eq]
    exact hball
  have hφ0 : 0 ≤ (φ : ℂ → ℝ) := fun _ => φ.nonneg
  obtain ⟨C, hC, hbound⟩ := cluster_test_mass_le_time_increment hμ hR hV hz ht
    hU hUsub hdis hφ hφ0
  refine ⟨C, hC, ?_⟩
  intro s hs
  let ν := μ.restrict (U ∩ cluster μ R z s)
  have hi : Integrable (φ : ℂ → ℝ) ν :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).mono_measure Measure.restrict_le_self
  have hballsub : closedBall w ρ ⊆ U := (closedBall_subset_closedBall (by linarith)).trans hball
  have hmeasure := measure_le_ofReal_integral (σ := ν) measurableSet_closedBall hi hφ0
    (fun x hx => by rw [φ.one_of_mem_closedBall hx])
  have heq : ν (closedBall w ρ) = μ (closedBall w ρ ∩ cluster μ R z s) := by
    rw [show ν = μ.restrict (U ∩ cluster μ R z s) from rfl,
      Measure.restrict_apply measurableSet_closedBall]
    congr 1
    ext x
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨hx, _, hxs⟩
      exact ⟨hx, hxs⟩
    · rintro ⟨hx, hxs⟩
      exact ⟨hx, hballsub hx, hxs⟩
  rw [heq] at hmeasure
  exact hmeasure.trans (ENNReal.ofReal_le_ofReal (hbound s hs))

/-- A compact subset of a pole-avoiding region separated from the current
cluster acquires mass at most linearly in time. -/
theorem cluster_compact_mass_le_time_increment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U K : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R \ {z})
    (hdis : Disjoint U (cluster μ R z t)) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, t ≤ s →
      μ (K ∩ cluster μ R z s) ≤ ENNReal.ofReal (C * (s - t)) := by
  classical
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  let ρ : ℝ := δ / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hball (x : K) : closedBall (x : ℂ) (2 * ρ) ⊆ U := by
    apply (closedBall_subset_closedBall (show 2 * ρ ≤ δ by dsimp [ρ]; linarith)).trans
    exact (closedBall_subset_cthickening x.property δ).trans hδU
  have hcover : K ⊆ ⋃ x : K, ball (x : ℂ) ρ := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self hρ⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun x : K => ball (x : ℂ) ρ)
    (fun _ => isOpen_ball) hcover
  have hex (x : K) := cluster_closedBall_mass_le_time_increment hμ hR hV hz ht
    hU hUsub hdis hρ (hball x)
  let C : K → ℝ := fun x => Classical.choose (hex x)
  have hC (x : K) : 0 ≤ C x := (Classical.choose_spec (hex x)).1
  have hbound (x : K) := (Classical.choose_spec (hex x)).2
  refine ⟨∑ x ∈ F, C x, Finset.sum_nonneg (fun x _ => hC x), ?_⟩
  intro s hs
  have hsub : K ∩ cluster μ R z s ⊆
      ⋃ x ∈ F, (closedBall (x : ℂ) ρ ∩ cluster μ R z s) := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hF hx.1)
    obtain ⟨hiF, hxi⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hiF, ball_subset_closedBall hxi, hx.2⟩⟩
  calc
    μ (K ∩ cluster μ R z s) ≤
        μ (⋃ x ∈ F, (closedBall (x : ℂ) ρ ∩ cluster μ R z s)) := measure_mono hsub
    _ ≤ ∑ x ∈ F, μ (closedBall (x : ℂ) ρ ∩ cluster μ R z s) :=
      measure_biUnion_finset_le F _
    _ ≤ ∑ x ∈ F, ENNReal.ofReal (C x * (s - t)) :=
      Finset.sum_le_sum fun x _ => hbound x s hs
    _ = ENNReal.ofReal ((∑ x ∈ F, C x) * (s - t)) := by
      rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg]
      intro x hx
      exact mul_nonneg (hC x) (sub_nonneg.mpr hs)

/-- A compact set in the disc, separated from the closure of the current
cluster, acquires mass at most linearly in time. -/
theorem cluster_compact_separated_mass_le_time_increment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {K : Set ℂ} (hK : IsCompact K)
    (hKsub : K ⊆ ball (0 : ℂ) R \ closure (cluster μ R z t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, t ≤ s →
      μ (K ∩ cluster μ R z s) ≤ ENNReal.ofReal (C * (s - t)) := by
  apply cluster_compact_mass_le_time_increment hμ hR hV hz ht
    (isOpen_ball.sdiff isClosed_closure) _ _ hK hKsub
  · intro x hx
    refine ⟨hx.1, ?_⟩
    intro hxz
    apply hx.2
    rw [Set.mem_singleton_iff] at hxz
    subst x
    exact subset_closure (mem_cluster_iff.mpr ⟨hz, Or.inl rfl⟩)
  · exact disjoint_left.mpr (fun x hx hxcluster => hx.2 (subset_closure hxcluster))

end HarmonicBalls
