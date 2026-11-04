import HarmonicBalls.Proofs.Sec5.ObstacleCentreContinuity
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Large-time exhaustion of the disc

The nonnegative shifted least supersolution and positivity of the Green
function imply that every point of the disc enters the cluster at a finite
time. Openness, monotonicity, and compactness make the entry time uniform on
compact subsets of the disc. This gives no right-continuity assertion at a
finite boundary-contact time.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Pointwise

/-- Each point in the disc eventually belongs to the cluster. -/
theorem exists_mem_cluster_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {z x : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) (hx : x ∈ ball (0 : ℂ) R) :
    ∃ t : ℝ, 0 < t ∧ x ∈ cluster μ R z t := by
  by_cases hxz : x = z
  · exact ⟨1, zero_lt_one, hx, Or.inl hxz⟩
  · have hg := greenFunction_ball_pos hz hx (Ne.symm hxz)
    let t : ℝ := max 1 (greenPotentialBall μ R x / greenFunction (ball 0 R) z x + 1)
    have ht : 0 < t := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hbig : greenPotentialBall μ R x < t * greenFunction (ball 0 R) z x := by
      have hle : greenPotentialBall μ R x / greenFunction (ball 0 R) z x + 1 ≤ t :=
        le_max_right _ _
      have := (div_lt_iff₀ hg).mp (show greenPotentialBall μ R x /
        greenFunction (ball 0 R) z x < t by linarith)
      exact this
    have hnonneg := (obstacleLeastSuperharmonicMajorantGeneral_holds μ hμ R βm βp
      hR hV z hz t ht).2.2.2.1 x (ball_subset_closedBall hx)
    have hmem : x ∈ nonCoincidenceSet μ R z t := by
      refine ⟨hx, Or.inr ?_⟩
      change -t * greenFunction (ball 0 R) z x + greenPotentialBall μ R x < _
      linarith
    refine ⟨t, ht, ?_⟩
    rwa [(obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z hz t ht).2.2.1]

/-- Every compact subset of the disc enters the cluster by one common time. -/
theorem exists_cluster_contains_compact_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) {K : Set ℂ} (hK : IsCompact K)
    (hKsub : K ⊆ ball (0 : ℂ) R) :
    ∃ t : ℝ, 0 < t ∧ ∀ s : ℝ, t ≤ s → K ⊆ cluster μ R z s := by
  let F : Ioi (0 : ℝ) → Set ℂ := fun t => cluster μ R z t
  have hopen : ∀ t, IsOpen (F t) := by
    intro t
    change IsOpen (cluster μ R z t)
    rw [(obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z hz t t.property).2.2.1]
    exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds hμ hR hV hz t.property
  have hmono : ∀ s t : Ioi (0 : ℝ), s ≤ t → F s ⊆ F t := by
    intro s t hst
    change cluster μ R z s ⊆ cluster μ R z t
    rw [(obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z hz s s.property).2.2.1,
      (obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z hz t t.property).2.2.1]
    exact (obstacleMonotoneGeneral_holds μ hμ R βm βp hR hV z hz s t s.property hst).2
  have hcover : K ⊆ ⋃ t, F t := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := exists_mem_cluster_of_volumeGrowth hμ hR hV hz (hKsub hx)
    exact mem_iUnion.mpr ⟨⟨t, ht⟩, hxt⟩
  have hdirected : Directed (· ⊆ ·) F := by
    intro s t
    let u : Ioi (0 : ℝ) := ⟨max (s : ℝ) (t : ℝ), by
      change 0 < max (s : ℝ) (t : ℝ)
      exact lt_of_lt_of_le s.property (le_max_left _ _)⟩
    exact ⟨u, hmono s u (le_max_left _ _), hmono t u (le_max_right _ _)⟩
  let _ : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
  obtain ⟨t, ht⟩ := hK.elim_directed_cover F hopen hcover hdirected
  refine ⟨t, t.property, ?_⟩
  intro s hts
  exact ht.trans (hmono t ⟨s, lt_of_lt_of_le t.property hts⟩ hts)

/-- The union over positive times is the entire disc. -/
theorem iUnion_cluster_eq_ball_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) :
    (⋃ t > (0 : ℝ), cluster μ R z t) = ball (0 : ℂ) R := by
  apply Set.Subset.antisymm
  · intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨t, ht, hx⟩ := hx
    exact cluster_subset_ball hx
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := exists_mem_cluster_of_volumeGrowth hμ hR hV hz hx
    exact mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨ht, hxt⟩⟩

/-- At sufficiently large times, all later closed clusters stay within any
prescribed distance of the current cluster, uniformly in the later time. -/
theorem cluster_large_time_uniform_containment_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t → ∀ s : ℝ,
      closure (cluster μ R z s) ⊆ cluster μ R z t + ball (0 : ℂ) ε := by
  let F : Ioi (0 : ℝ) → Set ℂ := fun t => cluster μ R z t
  have hmono : ∀ s t : Ioi (0 : ℝ), s ≤ t → F s ⊆ F t := by
    intro s t hst
    change cluster μ R z s ⊆ cluster μ R z t
    rw [(obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z hz s s.property).2.2.1,
      (obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z hz t t.property).2.2.1]
    exact (obstacleMonotoneGeneral_holds μ hμ R βm βp hR hV z hz s t s.property hst).2
  let U : Ioi (0 : ℝ) → Set ℂ := fun t => thickening ε (F t)
  have hopen : ∀ t, IsOpen (U t) := fun _ => isOpen_thickening
  have hcover : closedBall (0 : ℂ) R ⊆ ⋃ t, U t := by
    intro x hx
    rw [← closure_ball (0 : ℂ) hR.ne'] at hx
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx ε hε
    obtain ⟨t, ht, hyt⟩ := exists_mem_cluster_of_volumeGrowth hμ hR hV hz hy
    apply mem_iUnion.mpr
    refine ⟨⟨t, ht⟩, mem_thickening_iff.mpr ⟨y, hyt, ?_⟩⟩
    exact hxy
  have hdirected : Directed (· ⊆ ·) U := by
    intro s t
    let v : Ioi (0 : ℝ) := ⟨max (s : ℝ) (t : ℝ), by
      change 0 < max (s : ℝ) (t : ℝ)
      exact lt_of_lt_of_le s.property (le_max_left _ _)⟩
    refine ⟨v, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
      exact mem_thickening_iff.mpr ⟨y, hmono s v (le_max_left _ _) hy, hxy⟩
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
      exact mem_thickening_iff.mpr ⟨y, hmono t v (le_max_right _ _) hy, hxy⟩
  let _ : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
  obtain ⟨T, hT⟩ := (isCompact_closedBall (0 : ℂ) R).elim_directed_cover U hopen hcover hdirected
  refine ⟨T, T.property, ?_⟩
  intro t hTt s x hx
  have hxball : x ∈ closedBall (0 : ℂ) R :=
    closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall hx
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp (hT hxball)
  have hyt : y ∈ cluster μ R z t := hmono T ⟨t, lt_of_lt_of_le T.property hTt⟩ hTt hy
  refine ⟨y, hyt, x - y, ?_, by abel⟩
  simpa [mem_ball, dist_eq_norm] using hxy

universe u

/-- Almost surely, compact subsets of every disc are eventually contained in
all later clusters, simultaneously for every radius and centre. -/
theorem ae_cluster_contains_compact_eventually
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ z ∈ ball (0 : ℂ) R,
      ∀ K : Set ℂ, IsCompact K → K ⊆ ball 0 R →
        ∃ t : ℝ, 0 < t ∧ ∀ s : ℝ, t ≤ s → K ⊆ cluster (μ ω) R z s := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hω
  intro R hR z hz K hK hKsub
  exact exists_cluster_contains_compact_of_volumeGrowth hω.1 hR (hω.2 R hR) hz hK hKsub

/-- The large-time uniform containment estimate holds almost surely for all
disc radii, centres and positive tolerances at once. -/
theorem ae_cluster_large_time_uniform_containment
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ z ∈ ball (0 : ℂ) R,
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t → ∀ s : ℝ,
        closure (cluster (μ ω) R z s) ⊆ cluster (μ ω) R z t + ball (0 : ℂ) ε := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hω
  intro R hR z hz ε hε
  exact cluster_large_time_uniform_containment_of_volumeGrowth hω.1 hR (hω.2 R hR) hz hε

end HarmonicBalls
