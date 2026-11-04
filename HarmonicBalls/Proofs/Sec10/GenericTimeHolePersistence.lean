import HarmonicBalls.Proofs.Sec5.CountableContinuityExceptions
import HarmonicBalls.Proofs.Sec10.HoleExtinctionMass

/-!
# Complementary components at generic times

Right continuity of an increasing family of closed clusters keeps any chosen
point of a complementary component outside the later closed sets for a
positive time interval. I2 supplies this continuity outside a countable set
of times for each pole.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped Pointwise

/-- A complementary component persists for a right interval at every time
where an increasing family is right-continuous in the one-sided Hausdorff
sense. -/
theorem complement_component_persists_of_right_continuity
    {F : ℝ → Set ℂ} {t : ℝ}
    (hmono : ∀ s, t ≤ s → F t ⊆ F s)
    (hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Icc t (t + δ), closure (F s) ⊆ F t + ball (0 : ℂ) ε)
    {U : Set ℂ} (hU : U ∈ connectedComponentsIn (closure (F t))ᶜ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      ∃ V ∈ connectedComponentsIn (closure (F s))ᶜ, V ⊆ U := by
  obtain ⟨p, hp, hUp⟩ := hU
  have hpU : p ∈ U := hUp ▸ mem_connectedComponentIn hp
  have hopen : IsOpen U := by
    rw [← hUp]
    exact isClosed_closure.isOpen_compl.connectedComponentIn
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen p hpU
  obtain ⟨δ, hδ, hnear⟩ := hcont ε hε
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  have hpnot : p ∉ closure (F s) := by
    intro hpcl
    have hpsum : p ∈ F t + ball (0 : ℂ) ε := hnear s hs hpcl
    obtain ⟨a, ha, b, hb, hab⟩ := hpsum
    have hba : a ∈ ball p ε := by
      rw [mem_ball, dist_comm, dist_eq_norm]
      have heq : p - a = b := by rw [← hab]; simp
      rw [heq]
      simpa only [mem_ball, dist_zero_right] using hb
    have hUsub : U ⊆ (closure (F t))ᶜ := by
      rw [← hUp]
      exact connectedComponentIn_subset _ _
    exact hUsub (hball hba) (subset_closure ha)
  let V := connectedComponentIn (closure (F s))ᶜ p
  have hpV : p ∈ V := mem_connectedComponentIn hpnot
  have hVcomp : V ∈ connectedComponentsIn (closure (F s))ᶜ := ⟨p, hpnot, rfl⟩
  have hVU : V ⊆ U := by
    rw [← hUp]
    exact connectedComponentIn_mono p
      (compl_subset_compl.mpr (closure_mono (hmono s hs.1)))
  exact ⟨V, hVcomp, hVU⟩

universe u

/-- Under I2, for every pole simultaneously, only countably many positive
unit-disc times can have a complementary component that fails to persist for
some right interval. The exceptional set may depend on the pole. -/
theorem ae_countable_times_with_nonpersistent_component
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      {t : ℝ | 0 < t ∧ ∃ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
          ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ, V ⊆ U}.Countable := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_countable_cluster_rightContinuity_exceptions hI2 hγ hγ2 hα hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hcount hmono
  intro z hz
  apply (hcount z hz).mono
  intro t ⟨ht, U, hU, hnot⟩
  refine ⟨ht, ?_⟩
  intro hcont
  exact hnot (complement_component_persists_of_right_continuity
    (fun s hts => hmono t s 1 ht hts zero_lt_one z hz) hcont hU)

/-- If there are no bounded complementary components at positive rational
times, then I2 implies at most countably many positive times with bounded
components, for each pole. This does not establish the rational-time premise. -/
theorem ae_countable_hole_times_of_no_rational_holes
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      (∀ q : ℚ, 0 < (q : ℝ) → ∀ V ∈ connectedComponentsIn
        (closure (cluster (μ ω) 1 z q))ᶜ, ¬ Bornology.IsBounded V) →
      {t : ℝ | 0 < t ∧ ∃ U ∈ connectedComponentsIn
        (closure (cluster (μ ω) 1 z t))ᶜ, Bornology.IsBounded U}.Countable := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_countable_times_with_nonpersistent_component hI2
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hcount
  intro z hz hrat
  apply (hcount z hz).mono
  intro t ⟨ht, U, hU, hb⟩
  refine ⟨ht, U, hU, ?_⟩
  rintro ⟨δ, hδ, hpersist⟩
  obtain ⟨q, htq, hq⟩ := exists_rat_btwn (lt_add_of_pos_right t hδ)
  obtain ⟨V, hV, hVU⟩ := hpersist q ⟨htq.le, hq.le⟩
  exact hrat q (ht.trans htq) V hV (hb.subset hVU)

/-- If compactly contained rational-time clusters have no bounded holes,
then at most countably many positive times have both a bounded hole and a
later compactly contained cluster. The rational-time premise is explicit. -/
theorem ae_countable_hole_times_before_compact_containment
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      (∀ q : ℚ, 0 < (q : ℝ) → closure (cluster (μ ω) 1 z q) ⊆ ball 0 1 →
        ∀ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z q))ᶜ,
          ¬ Bornology.IsBounded V) →
      {t : ℝ | 0 < t ∧ (∃ T : ℝ, t < T ∧
          closure (cluster (μ ω) 1 z T) ⊆ ball 0 1) ∧
        ∃ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
          Bornology.IsBounded U}.Countable := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_countable_times_with_nonpersistent_component hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hcount hmono
  intro z hz hrat
  apply (hcount z hz).mono
  intro t ⟨ht, ⟨T, htT, hT⟩, U, hU, hb⟩
  refine ⟨ht, U, hU, ?_⟩
  rintro ⟨δ, hδ, hpersist⟩
  have hmin : 0 < min δ (T - t) := lt_min hδ (sub_pos.mpr htT)
  obtain ⟨q, htq, hq⟩ := exists_rat_btwn (lt_add_of_pos_right t hmin)
  have hqδ : (q : ℝ) ≤ t + δ :=
    (hq.trans_le (add_le_add le_rfl (min_le_left _ _))).le
  have hqT : (q : ℝ) ≤ T := by
    have h := hq.trans_le (add_le_add le_rfl (min_le_right δ (T - t)))
    linarith
  have hqpos : 0 < (q : ℝ) := ht.trans htq
  have hqcl : closure (cluster (μ ω) 1 z q) ⊆ ball 0 1 :=
    (closure_mono (hmono q T 1 hqpos hqT zero_lt_one z hz)).trans hT
  obtain ⟨V, hV, hVU⟩ := hpersist q ⟨htq.le, hqδ⟩
  exact hrat q hqpos hqcl V hV (hb.subset hVU)

end HarmonicBalls
