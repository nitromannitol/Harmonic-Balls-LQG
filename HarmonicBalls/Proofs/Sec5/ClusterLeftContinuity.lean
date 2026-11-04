import HarmonicBalls.Proofs.Sec5.OdometerTimeContinuity
import HarmonicBalls.Proofs.Sec5.LeftContinuity
import HarmonicBalls.Proofs.Sec5.CountableContinuityExceptions

/-!
# Left continuity of disc clusters

Each point of a positive-time cluster appears at an earlier rational time.
Together with monotonicity and compactness, this gives left Hausdorff
continuity even when the cluster meets the boundary of the disc. It does not
establish the right-continuity assertion at boundary-touching times.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology Pointwise

/-- An increasing family whose points already appear at earlier positive
 times is uniformly approximated from the left when its current closure is
 compact. -/
theorem exists_earlier_uniform_approximation_of_pointwise
    {A : ℝ → Set ℂ} {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε)
    (hcompact : IsCompact (closure (A t)))
    (hmono : ∀ s s', 0 < s → s ≤ s' → A s ⊆ A s')
    (hearlier : ∀ x ∈ A t, ∃ s ∈ Ioo (0 : ℝ) t, x ∈ A s) :
    ∃ s ∈ Ioo (0 : ℝ) t, closure (A t) ⊆ ⋃ y ∈ A s, ball y ε := by
  let U : Ioo (0 : ℝ) t → Set ℂ := fun s => ⋃ y ∈ A s, ball y ε
  have hsubset : A t ⊆ ⋃ s ∈ Ioo (0 : ℝ) t, A s := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := hearlier x hx
    simp only [mem_iUnion]
    exact ⟨s, hs, hxs⟩
  have hclosure : closure (A t) ⊆ closure (⋃ s ∈ Ioo (0 : ℝ) t, A s) :=
    closure_mono hsubset
  have hopenU : ∀ s, IsOpen (U s) := by
    intro s
    exact isOpen_iUnion fun y => isOpen_iUnion fun _ => isOpen_ball
  have hcover : closure (A t) ⊆ ⋃ s, U s := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 (hclosure hx) ε hε
    change x ∈ ⋃ s : Ioo (0 : ℝ) t, ⋃ y ∈ A s, ball y ε
    simp only [mem_iUnion] at hy ⊢
    obtain ⟨s, hs, hys⟩ := hy
    exact ⟨⟨s, hs⟩, y, hys, hxy⟩
  have hdirected : Directed (· ⊆ ·) U := by
    intro s₁ s₂
    let s₃ : Ioo (0 : ℝ) t := ⟨max s₁ s₂,
      ⟨lt_of_lt_of_le s₁.property.1 (le_max_left _ _), max_lt s₁.property.2 s₂.property.2⟩⟩
    refine ⟨s₃, ?_, ?_⟩
    · intro x hx
      simp only [U, mem_iUnion] at hx ⊢
      obtain ⟨y, hy, hxy⟩ := hx
      exact ⟨y, hmono _ _ s₁.property.1 (le_max_left _ _) hy, hxy⟩
    · intro x hx
      simp only [U, mem_iUnion] at hx ⊢
      obtain ⟨y, hy, hxy⟩ := hx
      exact ⟨y, hmono _ _ s₂.property.1 (le_max_right _ _) hy, hxy⟩
  let _ : Nonempty (Ioo (0 : ℝ) t) := ⟨⟨t / 2, half_pos ht, half_lt_self ht⟩⟩
  obtain ⟨s, hs⟩ := hcompact.elim_directed_cover U hopenU hcover hdirected
  exact ⟨s, s.property, hs⟩

/-- Every monotone disc-cluster family is left-continuous in Hausdorff
edistance at positive times, including boundary-touching times. -/
theorem cluster_exists_earlier_hausdorff_bound
    {μ : Measure ℂ} {r t ε : ℝ} {z : ℂ} (ht : 0 < t) (hε : 0 < ε)
    (hmono : ∀ s s', 0 < s → s ≤ s' → cluster μ r z s ⊆ cluster μ r z s') :
    ∃ s ∈ Ioo (0 : ℝ) t, ∀ s' ∈ Icc s t,
      hausdorffEDist (cluster μ r z s') (cluster μ r z t) ≤ ENNReal.ofReal ε := by
  have hcompact : IsCompact (closure (cluster μ r z t)) :=
    (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset isClosed_closure
      (closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall)
  have hearlier : ∀ x ∈ cluster μ r z t,
      ∃ s ∈ Ioo (0 : ℝ) t, x ∈ cluster μ r z s := by
    intro x hx
    obtain ⟨q, hq0, hqt, hqx⟩ := mem_cluster_exists_earlier_rat ht hx
    exact ⟨q, ⟨hq0, hqt⟩, hqx⟩
  obtain ⟨s, hs, hcover⟩ := exists_earlier_uniform_approximation_of_pointwise
    ht hε hcompact hmono hearlier
  refine ⟨s, hs, ?_⟩
  intro s' hs'
  have hss := hmono s s' hs.1 hs'.1
  have hst := hmono s' t (lt_of_lt_of_le hs.1 hs'.1) hs'.2
  apply hausdorffEDist_le_of_mem_edist
  · intro x hx
    exact ⟨x, hst hx, by simp⟩
  · intro x hx
    have hxcover := hcover (subset_closure hx)
    simp only [mem_iUnion] at hxcover
    obtain ⟨y, hy, hxy⟩ := hxcover
    refine ⟨y, hss hy, ?_⟩
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (le_of_lt hxy)

/-- At a positive time, the one-sided right-continuity bound combines with
left continuity to give Hausdorff continuity of the disc cluster. -/
theorem cluster_hausdorffContinuousWithinAt_of_right_continuity
    {μ : Measure ℂ} {z : ℂ} {t : ℝ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → cluster μ 1 z s ⊆ cluster μ 1 z s')
    (hright : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (cluster μ 1 z s) ⊆ cluster μ 1 z t + ball (0 : ℂ) ε) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ s in 𝓝[Ioi (0 : ℝ)] t,
      hausdorffEDist (cluster μ 1 z s) (cluster μ 1 z t) < ε := by
  intro ε hε
  let e : ℝ≥0∞ := min ε 1
  have hepos : 0 < e := lt_min hε (by norm_num)
  have hefin : e ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  let η : ℝ := e.toReal / 2
  have hη : 0 < η := half_pos (ENNReal.toReal_pos hepos.ne' hefin)
  have hηε : ENNReal.ofReal η < ε := by
    calc
      ENNReal.ofReal η < ENNReal.ofReal e.toReal :=
        (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos hepos.ne' hefin)).2
          (by dsimp [η]; linarith [ENNReal.toReal_pos hepos.ne' hefin])
      _ = e := ENNReal.ofReal_toReal hefin
      _ ≤ ε := min_le_left _ _
  obtain ⟨s₀, hs₀, hleft⟩ := cluster_exists_earlier_hausdorff_bound ht hη hmono
  obtain ⟨δ, hδ, hright'⟩ := hright η hη
  have hneigh : Ioo s₀ (t + δ) ∈ 𝓝 t := Ioo_mem_nhds hs₀.2 (lt_add_of_pos_right _ hδ)
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hneigh] with s hs
  by_cases hst : s ≤ t
  · exact (hleft s ⟨hs.1.le, hst⟩).trans_lt hηε
  · have hts : t ≤ s := (not_le.mp hst).le
    have hbound : hausdorffEDist (cluster μ 1 z s) (cluster μ 1 z t) ≤
        ENNReal.ofReal η := by
      apply hausdorffEDist_le_of_mem_edist
      · intro x hx
        have hx' := hright' s ⟨hts, hs.2.le⟩ (subset_closure hx)
        obtain ⟨y, hy, v, hv, rfl⟩ := hx'
        refine ⟨y, hy, ?_⟩
        rw [edist_dist]
        apply ENNReal.ofReal_le_ofReal
        have hv' : ‖v‖ < η := by simpa [mem_ball, dist_eq_norm] using hv
        simpa [dist_eq_norm] using le_of_lt hv'
      · intro x hx
        exact ⟨x, hmono t s ht hts hx, by simp⟩
    exact hbound.trans_lt hηε

/-- For a fixed centre, Hausdorff continuity of the disc cluster can fail
at only countably many positive times, including after boundary contact. -/
theorem countable_not_cluster_hausdorffContinuousWithinAt
    {μ : Measure ℂ} {z : ℂ}
    (hmono : ∀ s s', 0 < s → s ≤ s' → cluster μ 1 z s ⊆ cluster μ 1 z s') :
    {t : ℝ | 0 < t ∧ ¬ ∀ ε : ℝ≥0∞, 0 < ε →
      ∀ᶠ s in 𝓝[Ioi (0 : ℝ)] t,
        hausdorffEDist (cluster μ 1 z s) (cluster μ 1 z t) < ε}.Countable := by
  apply (countable_not_rightContinuous_of_monotone hmono (fun _ _ => cluster_subset_ball)).mono
  intro t ht
  exact ⟨ht.1, fun hr => ht.2 (cluster_hausdorffContinuousWithinAt_of_right_continuity ht.1 hmono hr)⟩

universe u

/-- The left-continuity bound holds simultaneously for all disc radii,
centres and positive times for an LQG measure satisfying input I2. -/
theorem ae_cluster_left_hausdorff_bound
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∀ z ∈ ball (0 : ℂ) r, ∀ t : ℝ, 0 < t →
      ∀ ε : ℝ, 0 < ε → ∃ s ∈ Ioo (0 : ℝ) t, ∀ s' ∈ Icc s t,
        hausdorffEDist (cluster (μ ω) r z s') (cluster (μ ω) r z t) ≤ ENNReal.ofReal ε := by
  filter_upwards [clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hmono
  intro r hr z hz t ht ε hε
  exact cluster_exists_earlier_hausdorff_bound ht hε
    (fun s s' hs hss' => hmono s s' r hs hss' hr z hz)

/-- For all centres simultaneously, disc-cluster Hausdorff continuity can
fail at only countably many positive times. -/
theorem ae_countable_cluster_hausdorffContinuousWithinAt_exceptions
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      {t : ℝ | 0 < t ∧ ¬ ∀ ε : ℝ≥0∞, 0 < ε →
        ∀ᶠ s in 𝓝[Ioi (0 : ℝ)] t,
          hausdorffEDist (cluster (μ ω) 1 z s) (cluster (μ ω) 1 z t) < ε}.Countable := by
  filter_upwards [clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hmono
  intro z hz
  exact countable_not_cluster_hausdorffContinuousWithinAt
    (fun s s' hs hss' => hmono s s' 1 hs hss' zero_lt_one z hz)

end HarmonicBalls
