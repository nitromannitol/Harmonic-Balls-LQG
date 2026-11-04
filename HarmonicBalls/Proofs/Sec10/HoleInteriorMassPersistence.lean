import HarmonicBalls.Proofs.Sec5.InteriorTimeContinuity
import HarmonicBalls.Proofs.Sec10.HoleExtinctionMass

/-! # Local mass persistence near complementary components

The local odometer estimate prevents an open region away from the pole from
being immediately absorbed in mass. If a complementary component disappears
immediately, some of this mass must instead lie on the later frontier.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- An open finite positive-mass region disjoint from the present cluster and
pole retains positive mass outside the open cluster for a right interval. -/
theorem local_mass_persists_outside_cluster
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R \ {z})
    (hdis : Disjoint U (cluster μ R z t)) (hpos : 0 < μ U) (hfin : μ U ≠ ∞)
    (hmono : ∀ s v : ℝ, t ≤ s → s ≤ v → cluster μ R z s ⊆ cluster μ R z v)
    (hopen : ∀ s : ℝ, t ≤ s → IsOpen (cluster μ R z s)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ), 0 < μ (U \ cluster μ R z s) := by
  have hzero := measure_future_cluster_inter_eq_zero hμ hR hV hz ht hU hUsub hdis
    (tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds)
    (fun n => (dyadicScale_pos n).le)
  let A : ℕ → Set ℂ := fun n => U ∩ cluster μ R z (t + dyadicScale n)
  have ha : Antitone A := by
    intro n m hnm
    apply inter_subset_inter_right
    apply hmono _ _ (le_add_of_nonneg_right (dyadicScale_pos m).le)
    apply add_le_add_right
    exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ ≤ 1) hnm
  have hmeas : ∀ n, NullMeasurableSet (A n) μ := fun n =>
    (hU.measurableSet.inter (hopen _ (le_add_of_nonneg_right (dyadicScale_pos n).le)).measurableSet).nullMeasurableSet
  have hlim := tendsto_measure_iInter_atTop hmeas ha ⟨0, (measure_mono inter_subset_left).trans_lt (lt_top_iff_ne_top.mpr hfin) |>.ne⟩
  have heq : (⋂ n, A n) = U ∩ ⋂ n, cluster μ R z (t + dyadicScale n) := by
    ext x
    simp only [A, mem_iInter, mem_inter_iff]
    constructor
    · intro h; exact ⟨(h 0).1, fun n => (h n).2⟩
    · rintro ⟨hu, h⟩ n; exact ⟨hu, h n⟩
  rw [heq, hzero] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const hpos).exists
  refine ⟨dyadicScale n, dyadicScale_pos n, ?_⟩
  intro s hs
  have hsmall : μ (U ∩ cluster μ R z s) < μ U :=
    (measure_mono (inter_subset_inter_right U (hmono s _ hs.1 hs.2))).trans_lt hn
  by_contra hnot
  have hz' : μ (U \ cluster μ R z s) = 0 := le_antisymm (not_lt.mp hnot) bot_le
  have hcover : U ⊆ (U ∩ cluster μ R z s) ∪ (U \ cluster μ R z s) := by
    intro x hx
    by_cases hxc : x ∈ cluster μ R z s
    · exact Or.inl ⟨hx, hxc⟩
    · exact Or.inr ⟨hx, hxc⟩
  have hbound := (measure_mono (μ := μ) hcover).trans (measure_union_le _ _)
  rw [hz', add_zero] at hbound
  exact (not_le_of_gt hsmall) hbound

/-- A complementary component meeting the disc either has a later descendant
or carries positive mass on the later frontier, throughout a right interval. -/
theorem cluster_component_descendant_or_frontier_mass_for_interval
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (hfull : ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ U)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    (hmono : ∀ s v : ℝ, t ≤ s → s ≤ v → cluster μ R z s ⊆ cluster μ R z v)
    (hopen : ∀ s : ℝ, t ≤ s → IsOpen (cluster μ R z s))
    {U : Set ℂ} (hU : U ∈ connectedComponentsIn (closure (cluster μ R z t))ᶜ)
    (hmeet : (U ∩ ball (0 : ℂ) R).Nonempty) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      (∃ V ∈ connectedComponentsIn (closure (cluster μ R z s))ᶜ, V ⊆ U) ∨
      0 < μ (frontier (cluster μ R z s) ∩ U) := by
  let : IsLocallyFiniteMeasure μ := hμ
  have hU' := hU
  obtain ⟨x, hx, hUeq⟩ := hU'
  have hUopen : IsOpen U := by
    rw [← hUeq]
    exact isClosed_closure.isOpen_compl.connectedComponentIn
  have hUsub : U ⊆ (closure (cluster μ R z t))ᶜ := by
    rw [← hUeq]
    exact connectedComponentIn_subset _ _
  obtain ⟨p, hpU, hpball⟩ := hmeet
  have hpne : p ≠ z := by
    intro heq
    apply hUsub hpU
    simpa [heq] using (subset_closure (self_mem_cluster hz))
  have hO : IsOpen (U ∩ (ball (0 : ℂ) R \ {z})) :=
    hUopen.inter (isOpen_ball.sdiff isClosed_singleton)
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hO p ⟨hpU, hpball, by simpa using hpne⟩
  have hdis : Disjoint (ball p r) (cluster μ R z t) := disjoint_left.mpr
    (fun y hy hyC => hUsub (hrsub hy).1 (subset_closure hyC))
  have hpos : 0 < μ (ball p r) := hfull _ isOpen_ball ⟨p, mem_ball_self hr⟩
  have hfin : μ (ball p r) ≠ ∞ := (measure_ball_lt_top (μ := μ)).ne
  obtain ⟨δ, hδ, hpersist⟩ := local_mass_persists_outside_cluster hμ hR hV hz ht
    isOpen_ball (fun y hy => (hrsub hy).2) hdis hpos hfin hmono hopen
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  by_cases hdesc : ∃ V ∈ connectedComponentsIn (closure (cluster μ R z s))ᶜ, V ⊆ U
  · exact Or.inl hdesc
  · right
    have hcover := complement_component_subset_of_no_descendant
      (closure_mono (hmono t s le_rfl hs.1)) hU hdesc
    apply (hpersist s hs).trans_le
    apply measure_mono
    intro y hy
    have hyU : y ∈ U := (hrsub hy.1).1
    refine ⟨?_, hyU⟩
    rw [(hopen s hs.1).frontier_eq]
    exact ⟨hcover hyU, hy.2⟩

universe u

/-- I2 gives the local descendant-or-frontier-mass alternative simultaneously
for all discs, poles, positive times and complementary components. -/
theorem ae_cluster_component_descendant_or_frontier_mass_for_interval
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ R t : ℝ, 0 < R → 0 < t → ∀ z ∈ ball (0 : ℂ) R,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) R z t))ᶜ,
      (U ∩ ball (0 : ℂ) R).Nonempty →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        (∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) R z s))ᶜ, V ⊆ U) ∨
        0 < μ ω (frontier (cluster (μ ω) R z s) ∩ U) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV,
    lqgMeasureFullSupportStmt_of_volumeGrowth hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hV hfull hopen hmono
  intro R t hR ht z hz U hU hmeet
  exact cluster_component_descendant_or_frontier_mass_for_interval hV.1 hR (hV.2 R hR)
    hfull hz ht (fun s v hts hsv => hmono s v R (ht.trans_le hts) hsv hR z hz)
    (fun s hts => (hopen s R (ht.trans_le hts) hR z hz).1) hU hmeet

/-- Under I2, every bounded complementary component of a unit-disc cluster
has the descendant-or-frontier-mass alternative on a right interval. -/
theorem ae_cluster_bounded_hole_descendant_or_frontier_mass_for_interval
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        (∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ,
          Bornology.IsBounded V ∧ V ⊆ U) ∨
        0 < μ ω (frontier (cluster (μ ω) 1 z s) ∩ U) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_component_descendant_or_frontier_mass_for_interval hI2
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hlocal
  intro t ht z hz U hU hbounded
  have hcl : closure (cluster (μ ω) 1 z t) ⊆ closedBall 0 1 :=
    closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
  have hUball := bounded_complement_component_subset_unit_ball isClosed_closure hcl hU hbounded
  have hUne : U.Nonempty := by
    obtain ⟨p, hp, heq⟩ := hU
    exact ⟨p, heq ▸ mem_connectedComponentIn hp⟩
  obtain ⟨δ, hδ, hδprop⟩ := hlocal 1 t zero_lt_one ht z hz U hU
    (hUne.mono (fun x hx => ⟨hx, hUball hx⟩))
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  rcases hδprop s hs with ⟨V, hV, hVU⟩ | hfront
  · exact Or.inl ⟨V, hV, hbounded.subset hVU, hVU⟩
  · exact Or.inr hfront

end HarmonicBalls
