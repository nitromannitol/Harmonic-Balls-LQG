import HarmonicBalls.Proofs.Sec5.JointTimeMeasurableDecoder
import HarmonicBalls.Proofs.Sec5.RightContinuousEnvelope

/-! # Joint measurability of the closed right envelope -/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- The closed right envelope admits a jointly measurable set-valued decoder,
valid for every positive time and every locally finite volume-growth measure. -/
theorem exists_measurable_rightClosedEnvelope_joint_time_of_volumeGrowth
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ∃ F : Measure ℂ × ℝ → Set ℂ, Measurable F ∧ ∀ ν : Measure ℂ,
      IsLocallyFiniteMeasure ν → (∃ βminus βplus, VolumeGrowth ν 1 βminus βplus) →
      ∀ t : ℝ, 0 < t → F (ν, t) = rightClosedEnvelope (cluster ν 1 z) t := by
  obtain ⟨G, hG, hcorrect⟩ :=
    exists_measurable_closedCluster_joint_time_of_volumeGrowth (R := 1) zero_lt_one hz
  let F : Measure ℂ × ℝ → Set ℂ := fun p =>
    ⋂ n : ℕ, G (p.1, p.2 + (2 : ℝ)⁻¹ ^ n)
  refine ⟨F, ?_, ?_⟩
  · apply Measurable.of_eval
    intro x
    change Measurable (fun p : Measure ℂ × ℝ =>
      x ∈ ⋂ n : ℕ, G (p.1, p.2 + (2 : ℝ)⁻¹ ^ n))
    simp only [Set.mem_iInter]
    apply Measurable.forall
    intro n
    exact (measurable_pi_apply x).comp (hG.comp
      (measurable_fst.prodMk (measurable_snd.add_const _)))
  · intro ν hloc hvol t ht
    dsimp only [F, rightClosedEnvelope]
    congr 1
    funext n
    exact hcorrect ν hloc hvol _ (by positivity)

/-- Membership of any fixed point in the closed right envelope is represented
by a jointly Borel event on the same class of measures and times. -/
theorem exists_measurableSet_mem_rightClosedEnvelope_joint_time_of_volumeGrowth
    {z x : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ∃ E : Set (Measure ℂ × ℝ), MeasurableSet E ∧ ∀ ν : Measure ℂ,
      IsLocallyFiniteMeasure ν → (∃ βminus βplus, VolumeGrowth ν 1 βminus βplus) →
      ∀ t : ℝ, 0 < t → ((ν, t) ∈ E ↔ x ∈ rightClosedEnvelope (cluster ν 1 z) t) := by
  obtain ⟨F, hF, hcorrect⟩ := exists_measurable_rightClosedEnvelope_joint_time_of_volumeGrowth hz
  refine ⟨{p | x ∈ F p}, ((measurable_pi_apply x).comp hF).setOf, ?_⟩
  intro ν hloc hvol t ht
  change x ∈ F (ν, t) ↔ _
  rw [hcorrect ν hloc hvol t ht]

/-- The event that a fixed point is added by the right envelope is jointly
Borel representable on locally finite volume-growth measures. -/
theorem exists_measurableSet_mem_rightClosedEnvelope_diff_joint_time_of_volumeGrowth
    {z x : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ∃ E : Set (Measure ℂ × ℝ), MeasurableSet E ∧ ∀ ν : Measure ℂ,
      IsLocallyFiniteMeasure ν → (∃ βminus βplus, VolumeGrowth ν 1 βminus βplus) →
      ∀ t : ℝ, 0 < t → ((ν, t) ∈ E ↔
        x ∈ rightClosedEnvelope (cluster ν 1 z) t \ closure (cluster ν 1 z t)) := by
  obtain ⟨A, hA, hAeq⟩ :=
    exists_measurableSet_mem_rightClosedEnvelope_joint_time_of_volumeGrowth (x := x) hz
  obtain ⟨G, hG, hGeq⟩ :=
    exists_measurable_closedCluster_joint_time_of_volumeGrowth (R := 1) zero_lt_one hz
  refine ⟨A \ {p | x ∈ G p}, hA.diff ((measurable_pi_apply x).comp hG).setOf, ?_⟩
  intro ν hloc hvol t ht
  change ((ν, t) ∈ A ∧ x ∉ G (ν, t)) ↔ _
  rw [hAeq ν hloc hvol t ht, hGeq ν hloc hvol t ht]
  rfl

/-- A fixed point can be added by the right envelope at only countably many
positive times of an increasing family contained in the unit disc. -/
theorem countable_mem_rightClosedEnvelope_diff
    {F : ℝ → Set ℂ} (x : ℂ)
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s')
    (hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1) :
    {t : ℝ | 0 < t ∧ x ∈ rightClosedEnvelope F t \ closure (F t)}.Countable := by
  apply (countable_not_rightContinuous_of_monotone hmono hbound).mono
  intro t ht
  refine ⟨ht.1, ?_⟩
  intro hcont
  have hsub := (closure_dyadic_iInter_subset_iff_right_continuous ht.1 hmono hbound).mpr hcont
  exact ht.2.2 (hsub ht.2.1)

#print axioms exists_measurable_rightClosedEnvelope_joint_time_of_volumeGrowth
#print axioms exists_measurableSet_mem_rightClosedEnvelope_joint_time_of_volumeGrowth
#print axioms exists_measurableSet_mem_rightClosedEnvelope_diff_joint_time_of_volumeGrowth
#print axioms countable_mem_rightClosedEnvelope_diff

end HarmonicBalls
