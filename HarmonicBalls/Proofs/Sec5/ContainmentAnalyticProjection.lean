import HarmonicBalls.Proofs.Sec5.OdometerCentreLowerStability

/-! # Analytic projection of boundary contact -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped Topology

/-- Fixed-point cluster membership is represented by a Borel set in the
continuous Green-potential and centre variables. -/
theorem exists_measurableSet_joint_cluster_potential
    {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (x : ℂ)
    (Q : Measure ℂ → C(closedBall (0 : ℂ) R, ℝ))
    (hQeq : ∀ ν, ContinuousOn (greenPotentialBall ν R) (closedBall 0 R) →
      ∀ y, Q ν y = greenPotentialBall ν R y) :
    ∃ E : Set (C(closedBall (0 : ℂ) R, ℝ) × ball (0 : ℂ) R), MeasurableSet E ∧
      ∀ ν : Measure ℂ, IsLocallyFiniteMeasure ν →
        (∃ βm βp, VolumeGrowth ν R βm βp) → ∀ z : ball (0 : ℂ) R,
          ((Q ν, z) ∈ E ↔ x ∈ cluster ν R z t) := by
  classical
  by_cases hx : x ∈ ball (0 : ℂ) R
  swap
  · refine ⟨∅, MeasurableSet.empty, ?_⟩
    intro ν _ _ z
    simp only [mem_empty_iff_false, false_iff]
    intro h
    exact hx (mem_cluster_iff.mp h).1
  let A := {ν : Measure ℂ // IsLocallyFiniteMeasure ν ∧
    ∃ βm βp, VolumeGrowth ν R βm βp}
  let Z := ball (0 : ℂ) R
  let q : A → C(closedBall (0 : ℂ) R, ℝ) := fun a => Q a.1
  let f : A → Z → ℝ := fun a z =>
    if x = (z : ℂ) then 0 else shiftedOdometer a.1 R z t x
  have hcont : ∀ a : A, ContinuousOn (greenPotentialBall a.1 R) (closedBall 0 R) := by
    intro a
    obtain ⟨βm, βp, hv⟩ := a.2.2
    exact greenPotentialBallContinuousStep_holds a.1 a.2.1 R βm βp hR hv
  have hclass : ∀ (a : A) (z : Z), (shiftedSupersolutions a.1 R z t).Nonempty := by
    intro a z
    obtain ⟨βm, βp, hv⟩ := a.2.2
    exact ⟨greenPotentialBall a.1 R, greenPotentialBall_mem_shiftedSupersolutions ht.le
      (hcont a) (greenPotentialBallLaplacianStep_holds a.1 a.2.1 R βm βp hR hv).laplacianLE⟩
  have hnonneg : ∀ a z, 0 ≤ f a z := by
    intro a z
    by_cases h : x = (z : ℂ)
    · simp [f, h]
    · simp only [f, ite_eq_right h]
      exact shiftedOdometer_nonneg (hclass a z) (ball_subset_closedBall hx) h
  have hf : ∀ a r, IsOpen {z : Z | r < f a z} := by
    intro a r
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    change r < f a z at hz
    by_cases heq : x = (z : ℂ)
    · have hr : r < 0 := by simpa only [f, heq, ite_true] using hz
      exact Filter.Eventually.of_forall (fun z' => lt_of_lt_of_le hr (hnonneg a z'))
    · obtain ⟨βm, βp, hv⟩ := a.2.2
      have hr : r < shiftedOdometer a.1 R z t x := by simpa only [f, ite_eq_right heq] using hz
      have heps : 0 < shiftedOdometer a.1 R z t x - r := sub_pos.mpr hr
      have hev := eventually_shiftedOdometer_gt_sub_of_centre a.2.1 hR hv z.property hx heq ht heps
      have hval : Continuous (fun z : Z => (z : ℂ)) := continuous_subtype_val
      have hn : ∀ᶠ z' : Z in 𝓝 z, shiftedOdometer a.1 R z t x -
          (shiftedOdometer a.1 R z t x - r) < shiftedOdometer a.1 R z' t x :=
        hval.continuousAt.eventually hev
      have hnz : ∀ᶠ z' : Z in 𝓝 z, x ≠ (z' : ℂ) := by
        have htne : ∀ᶠ z' : Z in 𝓝 z, (z' : ℂ) ≠ x :=
          hval.continuousAt.eventually (isOpen_compl_singleton.mem_nhds
            (show (z : ℂ) ∈ ({x} : Set ℂ)ᶜ from Ne.symm heq))
        filter_upwards [htne] with z' hz'
        exact Ne.symm hz'
      filter_upwards [hn, hnz] with z' hz' hz'ne
      simp only [f, ite_eq_right hz'ne]
      linarith
  have hlip : ∀ a b z, |f a z - f b z| ≤ 2 * dist (q a) (q b) := by
    intro a b z
    by_cases heq : x = (z : ℂ)
    · simp only [f, heq, ite_true, sub_self, abs_zero]
      positivity
    · simp only [f, ite_eq_right heq]
      apply abs_shiftedOdometer_sub_le_of_greenPotentialBall (hclass a z) (hclass b z) ?_
        (ball_subset_closedBall hx) heq
      intro y hy
      have hb := ContinuousMap.dist_apply_le_dist (f := q a) (g := q b) ⟨y, hy⟩
      simpa only [Real.dist_eq, q, hQeq _ (hcont a), hQeq _ (hcont b)] using hb
  obtain ⟨O, hO, hOeq⟩ := exists_isOpen_positivity_factor q f hf hlip
  let E : Set (C(closedBall (0 : ℂ) R, ℝ) × Z) :=
    {p | x = (p.2 : ℂ) ∨ p ∈ O}
  have hE : MeasurableSet E := by
    exact (measurableSet_eq_fun measurable_const
      (continuous_subtype_val.measurable.comp measurable_snd)).union hO.measurableSet
  refine ⟨E, hE, ?_⟩
  intro ν hloc hvol z
  let a : A := ⟨ν, hloc, hvol⟩
  obtain ⟨βm, βp, hv⟩ := hvol
  have hcompat := (obstacleCompatibilityShiftStep_holds ν hloc R βm βp hR hv
    z z.property t ht).2.2.1
  change (x = (z : ℂ) ∨ (Q ν, z) ∈ O) ↔ x ∈ cluster ν R z t
  rw [hcompat, mem_nonCoincidenceSet_iff]
  have heq : (Q ν, z) ∈ O ↔ 0 < f a z := hOeq a z
  rw [heq]
  by_cases hxz : x = (z : ℂ)
  · simp [hxz]
  · simp [f, hxz, hx, a]

/-- Fixed-buffer failure is a Borel relation in the continuous potential and
centre variables. -/
theorem exists_measurableSet_clusterBufferFailure_potential
    {t ρ : ℝ} (ht : 0 < t)
    (Q : Measure ℂ → C(closedBall (0 : ℂ) 1, ℝ))
    (hQeq : ∀ ν, ContinuousOn (greenPotentialBall ν 1) (closedBall 0 1) →
      ∀ y, Q ν y = greenPotentialBall ν 1 y) :
    ∃ E : Set (C(closedBall (0 : ℂ) 1, ℝ) × ball (0 : ℂ) (1 / 2)),
      MeasurableSet E ∧ ∀ ν : Measure ℂ, IsLocallyFiniteMeasure ν →
        (∃ βm βp, VolumeGrowth ν 1 βm βp) →
        ∀ z : ball (0 : ℂ) (1 / 2),
          ((Q ν, z) ∈ E ↔ z ∈ clusterBufferFailure ν t ρ) := by
  classical
  choose A hA hAgood using fun k : ℕ =>
    exists_measurableSet_joint_cluster_potential zero_lt_one ht (denseSeq ℂ k) Q hQeq
  let J := ball (0 : ℂ) (1 / 2)
  let e : J → ball (0 : ℂ) 1 := fun z =>
    ⟨z, ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) z.property⟩
  have he : Measurable e := (continuous_subtype_val.subtype_mk _).measurable
  let g : C(closedBall (0 : ℂ) 1, ℝ) × J →
      C(closedBall (0 : ℂ) 1, ℝ) × ball (0 : ℂ) 1 := fun p => (p.1, e p.2)
  have hg : Measurable g := measurable_fst.prodMk (he.comp measurable_snd)
  let E : Set (C(closedBall (0 : ℂ) 1, ℝ) × J) := ⋃ k,
    if denseSeq ℂ k ∉ closedBall (0 : ℂ) ρ then g ⁻¹' A k else ∅
  have hE : MeasurableSet E := by
    apply MeasurableSet.iUnion
    intro k
    split_ifs
    · exact MeasurableSet.empty
    · exact (hA k).preimage hg
  refine ⟨E, hE, ?_⟩
  intro ν hloc hvol z
  constructor
  · intro h
    simp only [E, mem_iUnion] at h
    obtain ⟨k, hk⟩ := h
    split_ifs at hk with hρ
    · simp at hk
    · exact ⟨denseSeq ℂ k, (hAgood k ν hloc hvol (e z)).mp hk, hρ⟩
  · rintro ⟨x, hx, hxρ⟩
    obtain ⟨βm, βp, hv⟩ := hvol
    have hopen : IsOpen (cluster ν 1 z t) :=
      (cluster_open_laplacian_of_general greenFunctionBall
        obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
        obstacleCompatibilityShiftStep_holds hloc zero_lt_one hv
        (ball_subset_ball (by norm_num) z.property) ht).1
    obtain ⟨k, hk⟩ := (denseRange_denseSeq ℂ).exists_mem_open
      (hopen.inter isClosed_closedBall.isOpen_compl) ⟨x, hx, hxρ⟩
    change (Q ν, z) ∈ E
    simp only [E, mem_iUnion]
    refine ⟨k, ?_⟩
    have hkρ : denseSeq ℂ k ∉ closedBall (0 : ℂ) ρ := hk.2
    simp only [hkρ]
    exact (hAgood k ν hloc ⟨βm, βp, hv⟩ (e z)).mpr hk.1

/-- The boundary-contact relation is Borel in the potential and centre. -/
theorem exists_measurableSet_cluster_boundary_contact_potential
    {t : ℝ} (ht : 0 < t)
    (Q : Measure ℂ → C(closedBall (0 : ℂ) 1, ℝ))
    (hQeq : ∀ ν, ContinuousOn (greenPotentialBall ν 1) (closedBall 0 1) →
      ∀ y, Q ν y = greenPotentialBall ν 1 y) :
    ∃ E : Set (C(closedBall (0 : ℂ) 1, ℝ) × ball (0 : ℂ) (1 / 2)),
      MeasurableSet E ∧ ∀ ν : Measure ℂ, IsLocallyFiniteMeasure ν →
        (∃ βm βp, VolumeGrowth ν 1 βm βp) →
        ∀ z : ball (0 : ℂ) (1 / 2),
          ((Q ν, z) ∈ E ↔ ¬ closure (cluster ν 1 z t) ⊆ ball 0 1) := by
  choose E hE hgood using fun n : ℕ =>
    exists_measurableSet_clusterBufferFailure_potential
      (ρ := 1 - 1 / ((n : ℝ) + 1)) ht Q hQeq
  refine ⟨⋂ n, E n, MeasurableSet.iInter hE, ?_⟩
  intro ν hloc hvol z
  simp only [mem_iInter, hgood _ ν hloc hvol z]
  exact (not_cluster_closure_subset_ball_iff ν t z).symm

/-- At a fixed positive time, the potentials of measures with a boundary
contact centre are represented by an analytic subset of the Polish space of
continuous potentials. -/
theorem exists_analyticSet_cluster_boundary_contact_potential
    {t : ℝ} (ht : 0 < t)
    (Q : Measure ℂ → C(closedBall (0 : ℂ) 1, ℝ))
    (hQeq : ∀ ν, ContinuousOn (greenPotentialBall ν 1) (closedBall 0 1) →
      ∀ y, Q ν y = greenPotentialBall ν 1 y) :
    ∃ S : Set C(closedBall (0 : ℂ) 1, ℝ), AnalyticSet S ∧
      ∀ ν : Measure ℂ, IsLocallyFiniteMeasure ν →
        (∃ βm βp, VolumeGrowth ν 1 βm βp) →
        (Q ν ∈ S ↔ ∃ z : ball (0 : ℂ) (1 / 2),
          ¬ closure (cluster ν 1 z t) ⊆ ball 0 1) := by
  let J := ball (0 : ℂ) (1 / 2)
  let : PolishSpace J := isOpen_ball.polishSpace
  obtain ⟨E, hE, hgood⟩ := exists_measurableSet_cluster_boundary_contact_potential ht Q hQeq
  refine ⟨Prod.fst '' E, hE.analyticSet_image measurable_fst, ?_⟩
  intro ν hloc hvol
  constructor
  · rintro ⟨⟨v, z⟩, hz, hv⟩
    change v = Q ν at hv
    subst v
    exact ⟨z, (hgood ν hloc hvol z).mp hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨(Q ν, z), (hgood ν hloc hvol z).mpr hz, rfl⟩

/-- The failure of each all-centre unit-containment event is represented on
volume-growth measures by an analytic set of continuous Green potentials. -/
theorem exists_analyticSet_unitClusterContainmentEvent_compl :
    ∃ Q : Measure ℂ → C(closedBall (0 : ℂ) 1, ℝ), Measurable Q ∧
      ∀ m : ℕ, ∃ S : Set C(closedBall (0 : ℂ) 1, ℝ), AnalyticSet S ∧
        ∀ ν : Measure ℂ, IsLocallyFiniteMeasure ν →
          (∃ βm βp, VolumeGrowth ν 1 βm βp) →
          (Q ν ∈ S ↔ ν ∉ unitClusterContainmentEvent m) := by
  obtain ⟨Q, hQ, hQeq⟩ := exists_measurable_greenPotentialBall_decoder zero_lt_one
  refine ⟨Q, hQ, ?_⟩
  intro m
  let T := {q : ℚ // (q : ℝ) ∈ Ioo (0 : ℝ) ((2 : ℝ)⁻¹ ^ m)}
  choose S hS hgood using fun q : T =>
    exists_analyticSet_cluster_boundary_contact_potential q.property.1 Q hQeq
  refine ⟨⋃ q : T, S q, AnalyticSet.iUnion hS, ?_⟩
  intro ν hloc hvol
  have hmono : ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ s t : ℝ, 0 < s → s ≤ t →
      cluster ν 1 z s ⊆ cluster ν 1 z t := by
    intro z hz s t hs hst
    obtain ⟨βm, βp, hv⟩ := hvol
    exact cluster_subset_of_general obstacleMonotoneGeneral_holds obstacleCompatibilityShiftStep_holds
      hloc zero_lt_one hv (ball_subset_ball (by norm_num) hz) hs hst
  rw [not_mem_unitClusterContainmentEvent_iff ν m hmono]
  simp only [mem_iUnion]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨z, hz⟩ := (hgood q ν hloc hvol).mp hq
    exact ⟨q, q.property, z, (not_cluster_closure_subset_ball_iff ν q z).mp hz⟩
  · rintro ⟨q, hq, z, hz⟩
    let q' : T := ⟨q, hq⟩
    exact ⟨q', (hgood q' ν hloc hvol).mpr
      ⟨z, (not_cluster_closure_subset_ball_iff ν q z).mpr hz⟩⟩

end HarmonicBalls
