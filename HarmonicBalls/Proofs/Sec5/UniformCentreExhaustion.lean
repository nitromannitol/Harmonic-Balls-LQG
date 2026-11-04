import HarmonicBalls.Proofs.Sec5.DiscClusterExhaustion

/-! # Late-time exhaustion uniformly over compact sets of centres

Centre-section openness and compactness give a common entry time for each
fixed interior point. A second compactness argument yields a common spatial
approximation time for the whole closed disc.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Pointwise

/-- An interior point enters every cluster centred in a compact subset of the
open disc by one common time. -/
theorem exists_uniform_centre_entry_time_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {K : Set (ball (0 : ℂ) R)} (hK : IsCompact K)
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) R) :
    ∃ T : ℝ, 0 < T ∧ ∀ z ∈ K, ∀ t : ℝ, T ≤ t → x ∈ cluster μ R z t := by
  let F : Ioi (0 : ℝ) → Set (ball (0 : ℂ) R) :=
    fun t => {z | x ∈ cluster μ R z t}
  have hopen : ∀ t, IsOpen (F t) := fun t =>
    isOpen_cluster_centre_section hμ hR hV t.property x
  have hmono : ∀ s t : Ioi (0 : ℝ), s ≤ t → F s ⊆ F t := by
    intro s t hst z hz
    have hs := (obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z z.property s s.property).2.2.1
    have ht := (obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z z.property t t.property).2.2.1
    change x ∈ cluster μ R z t
    change x ∈ cluster μ R z s at hz
    rw [hs] at hz
    rw [ht]
    exact (obstacleMonotoneGeneral_holds μ hμ R βm βp hR hV z z.property s t s.property hst).2 hz
  have hcover : K ⊆ ⋃ t, F t := by
    intro z hz
    obtain ⟨t, ht, hxt⟩ := exists_mem_cluster_of_volumeGrowth hμ hR hV z.property hx
    exact mem_iUnion.mpr ⟨⟨t, ht⟩, hxt⟩
  have hdirected : Directed (· ⊆ ·) F := by
    intro s t
    let u : Ioi (0 : ℝ) := ⟨max (s : ℝ) (t : ℝ), by
      change 0 < max (s : ℝ) (t : ℝ)
      exact lt_of_lt_of_le s.property (le_max_left _ _)⟩
    exact ⟨u, hmono s u (le_max_left _ _), hmono t u (le_max_right _ _)⟩
  let _ : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
  obtain ⟨T, hT⟩ := hK.elim_directed_cover F hopen hcover hdirected
  refine ⟨T, T.property, ?_⟩
  intro z hz t hTt
  exact hmono T ⟨t, lt_of_lt_of_le T.property hTt⟩ hTt (hT hz)

/-- For centres in a compact subset of the disc, the clusters become
uniformly dense in the closed disc as time tends to infinity. -/
theorem uniform_centre_large_time_exhaustion_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {K : Set (ball (0 : ℂ) R)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ z ∈ K, ∀ t : ℝ, T ≤ t →
      closedBall (0 : ℂ) R ⊆ cluster μ R z t + ball (0 : ℂ) ε := by
  let U : Ioi (0 : ℝ) → Set ℂ := fun t =>
    ⋃ x ∈ {x : ℂ | ∀ z ∈ K, x ∈ cluster μ R z t}, ball x ε
  have hopen : ∀ t, IsOpen (U t) := fun t => isOpen_iUnion fun x => isOpen_iUnion fun _ => isOpen_ball
  have hmono : ∀ s t : Ioi (0 : ℝ), s ≤ t → U s ⊆ U t := by
    intro s t hst y hy
    simp only [U, mem_iUnion] at hy ⊢
    obtain ⟨x, hx, hy⟩ := hy
    refine ⟨x, ?_, hy⟩
    intro z hz
    have hs := (obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z z.property s s.property).2.2.1
    have ht := (obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z z.property t t.property).2.2.1
    rw [ht]
    have hxz := hx z hz
    rw [hs] at hxz
    exact (obstacleMonotoneGeneral_holds μ hμ R βm βp hR hV z z.property s t s.property hst).2 hxz
  have hcover : closedBall (0 : ℂ) R ⊆ ⋃ t, U t := by
    intro y hy
    rw [← closure_ball (0 : ℂ) hR.ne'] at hy
    obtain ⟨x, hx, hyx⟩ := Metric.mem_closure_iff.mp hy ε hε
    obtain ⟨T, hT, hentry⟩ := exists_uniform_centre_entry_time_of_volumeGrowth hμ hR hV hK hx
    refine mem_iUnion.mpr ⟨⟨T, hT⟩, ?_⟩
    simp only [U, mem_iUnion]
    exact ⟨x, fun z hz => hentry z hz T le_rfl, hyx⟩
  have hdirected : Directed (· ⊆ ·) U := by
    intro s t
    let u : Ioi (0 : ℝ) := ⟨max (s : ℝ) (t : ℝ), by
      change 0 < max (s : ℝ) (t : ℝ)
      exact lt_of_lt_of_le s.property (le_max_left _ _)⟩
    exact ⟨u, hmono s u (le_max_left _ _), hmono t u (le_max_right _ _)⟩
  let _ : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
  obtain ⟨T, hT⟩ := (isCompact_closedBall (0 : ℂ) R).elim_directed_cover U hopen hcover hdirected
  refine ⟨T, T.property, ?_⟩
  intro z hz t hTt y hy
  have hy' := hmono T ⟨t, lt_of_lt_of_le T.property hTt⟩ hTt (hT hy)
  simp only [U, mem_iUnion] at hy'
  obtain ⟨x, hx, hyx⟩ := hy'
  refine ⟨x, hx z hz, y - x, ?_, by abel⟩
  simpa [mem_ball, dist_eq_norm] using hyx

universe u

/-- Almost surely, one time suffices for all centres in each compact subset
of any disc, for each positive spatial tolerance. -/
theorem ae_uniform_centre_large_time_exhaustion
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ K : Set (ball (0 : ℂ) R), IsCompact K →
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ z ∈ K, ∀ t : ℝ, T ≤ t →
        closedBall (0 : ℂ) R ⊆ cluster (μ ω) R z t + ball (0 : ℂ) ε := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hω
  intro R hR K hK ε hε
  exact uniform_centre_large_time_exhaustion_of_volumeGrowth hω.1 hR (hω.2 R hR) hK hε


end HarmonicBalls
