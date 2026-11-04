import HarmonicBalls.Proofs.Sec5.ObstacleCentreContinuity
import HarmonicBalls.Proofs.Sec5.ContainmentFailureSections

/-! # Lower stability of the shifted odometer as the pole moves -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped Topology

/-- Away from the evaluation point, the shifted odometer can decrease by at
most an arbitrarily small amount when its pole moves sufficiently little. -/
theorem eventually_shiftedOdometer_gt_sub_of_centre
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βminus βplus : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z x : ℂ} (hz : z ∈ ball (0 : ℂ) R) (hx : x ∈ ball (0 : ℂ) R)
    (hxz : x ≠ z) {t : ℝ} (ht : 0 < t) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z' in 𝓝 z, shiftedOdometer μ R z t x - ε < shiftedOdometer μ R z' t x := by
  let δ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hq := greenPotentialBallContinuousStep_holds μ hμ R βminus βplus hR hV
  have hq' : ∀ z', (shiftedSupersolutions μ R z' t).Nonempty := by
    intro z'
    exact ⟨greenPotentialBall μ R, greenPotentialBall_mem_shiftedSupersolutions ht.le hq
      (greenPotentialBallLaplacianStep_holds μ hμ R βminus βplus hR hV).laplacianLE⟩
  have hgreen : ContinuousAt (fun z' => greenFunction (ball 0 R) z' x) z := by
    have hc := (continuousOn_greenFunction_ball hx).continuousAt
      (isOpen_compl_singleton.mem_nhds (show z ∈ ({x} : Set ℂ)ᶜ from Ne.symm hxz))
    have heq : (fun z' => greenFunction (ball 0 R) z' x) = greenFunction (ball 0 R) x := by
      funext z'
      exact greenFunction_ball_comm R z' x
    rw [heq]
    exact hc
  have hpoint : ContinuousAt (fun z' => obstacle μ R z' t x) z := by
    unfold obstacle
    exact (continuousAt_const.mul hgreen).add continuousAt_const
  have hp : ∀ᶠ z' in 𝓝 z, obstacle μ R z' t x < obstacle μ R z t x + δ :=
    hpoint.eventually (isOpen_Iio.mem_nhds (by linarith :
      obstacle μ R z t x < obstacle μ R z t x + δ))
  have htr := eventually_truncatedShiftedObstacle_le_add hR hz ht hq hδ
  filter_upwards [htr, hp, isOpen_ball.mem_nhds hz] with z' htr hp hz'
  have hnonneg : ∀ w ∈ shiftedSupersolutions μ R z' t,
      ∀ y ∈ closedBall (0 : ℂ) R, 0 ≤ w y := by
    intro w hw y hy
    exact shiftedSupersolution_nonneg_on_closedBall hμ hR hV hz' ht hw hy
  have hle := shiftedLeastSupersolution_le_of_truncatedShiftedObstacle_le_add
    (c := δ) (hq' z') hnonneg htr (ball_subset_closedBall hx) hxz
  simp only [shiftedOdometer]
  dsimp [δ] at hle hp
  linarith

/-- A family that is uniformly Lipschitz in a metric parameter and lower
semicontinuous in a topological parameter has a jointly open positivity
representative on its parameter image. -/
theorem exists_isOpen_positivity_factor
    {A X Z : Type*} [PseudoMetricSpace X] [TopologicalSpace Z]
    (q : A → X) (f : A → Z → ℝ)
    (hf : ∀ a r, IsOpen {z | r < f a z})
    (hlip : ∀ a b z, |f a z - f b z| ≤ 2 * dist (q a) (q b)) :
    ∃ O : Set (X × Z), IsOpen O ∧ ∀ a z, (q a, z) ∈ O ↔ 0 < f a z := by
  let O : Set (X × Z) := ⋃ a : A, ⋃ r : ℝ, ⋃ (_ : 0 < r),
    ball (q a) (r / 4) ×ˢ {z | r < f a z}
  have hO : IsOpen O := by
    apply isOpen_iUnion
    intro a
    apply isOpen_iUnion
    intro r
    apply isOpen_iUnion
    intro _
    exact isOpen_ball.prod (hf a r)
  refine ⟨O, hO, ?_⟩
  intro a z
  constructor
  · intro hz
    simp only [O, mem_iUnion, mem_prod, mem_ball] at hz
    obtain ⟨b, r, hr, hd, hfz⟩ := hz
    change r < f b z at hfz
    have hbound := (abs_le.mp (hlip a b z)).1
    nlinarith
  · intro hfz
    have hr : 0 < f a z / 2 := by linarith
    simp only [O, mem_iUnion, mem_prod, mem_ball]
    refine ⟨a, f a z / 2, hr, ?_, ?_⟩
    · simp only [dist_self]
      linarith
    · change f a z / 2 < f a z
      linarith

/-- For a fixed point and time, cluster membership has a jointly measurable
representative in the measure and centre on all locally finite measures with
volume growth. -/
theorem exists_measurableSet_joint_cluster_of_volumeGrowth
    {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (x : ℂ) :
    ∃ E : Set (Measure ℂ × ball (0 : ℂ) R), MeasurableSet E ∧
      ∀ ν : Measure ℂ, IsLocallyFiniteMeasure ν →
        (∃ βm βp, VolumeGrowth ν R βm βp) → ∀ z : ball (0 : ℂ) R,
          ((ν, z) ∈ E ↔ x ∈ cluster ν R z t) := by
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
  obtain ⟨Q, hQ, hQeq⟩ := exists_measurable_greenPotentialBall_decoder hR
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
  let E : Set (Measure ℂ × Z) :=
    {p | x = (p.2 : ℂ) ∨ (Q p.1, p.2) ∈ O}
  have hE : MeasurableSet E := by
    have hpair : Measurable (fun p : Measure ℂ × Z => (Q p.1, p.2)) :=
      (hQ.comp measurable_fst).prodMk measurable_snd
    exact (measurableSet_eq_fun measurable_const
      (continuous_subtype_val.measurable.comp measurable_snd)).union (hO.measurableSet.preimage hpair)
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

/-- The fixed-buffer failure relation has a jointly Borel representative in
the measure and centre on locally finite volume-growth measures. -/
theorem exists_measurableSet_joint_clusterBufferFailure
    {t ρ : ℝ} (ht : 0 < t) :
    ∃ E : Set (Measure ℂ × ball (0 : ℂ) (1 / 2)), MeasurableSet E ∧
      ∀ ν : Measure ℂ, IsLocallyFiniteMeasure ν →
        (∃ βm βp, VolumeGrowth ν 1 βm βp) →
        ∀ z : ball (0 : ℂ) (1 / 2),
          ((ν, z) ∈ E ↔ z ∈ clusterBufferFailure ν t ρ) := by
  classical
  choose A hA hAgood using fun k : ℕ =>
    exists_measurableSet_joint_cluster_of_volumeGrowth zero_lt_one ht (denseSeq ℂ k)
  let J := ball (0 : ℂ) (1 / 2)
  let e : J → ball (0 : ℂ) 1 := fun z =>
    ⟨z, ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) z.property⟩
  have he : Measurable e := (continuous_subtype_val.subtype_mk _).measurable
  let g : Measure ℂ × J → Measure ℂ × ball (0 : ℂ) 1 := fun p => (p.1, e p.2)
  have hg : Measurable g := measurable_fst.prodMk (he.comp measurable_snd)
  let E : Set (Measure ℂ × J) := ⋃ k, if denseSeq ℂ k ∉ closedBall (0 : ℂ) ρ
    then g ⁻¹' A k else ∅
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
    change (ν, z) ∈ E
    simp only [E, mem_iUnion]
    refine ⟨k, ?_⟩
    have hkρ : denseSeq ℂ k ∉ closedBall (0 : ℂ) ρ := hk.2
    simp only [hkρ]
    exact (hAgood k ν hloc ⟨βm, βp, hv⟩ (e z)).mpr hk.1

/-- The fixed-time boundary-contact relation has a jointly Borel
representative. The existential projection to measures is a separate step. -/
theorem exists_measurableSet_joint_cluster_boundary_contact
    {t : ℝ} (ht : 0 < t) :
    ∃ E : Set (Measure ℂ × ball (0 : ℂ) (1 / 2)), MeasurableSet E ∧
      ∀ ν : Measure ℂ, IsLocallyFiniteMeasure ν →
        (∃ βm βp, VolumeGrowth ν 1 βm βp) →
        ∀ z : ball (0 : ℂ) (1 / 2),
          ((ν, z) ∈ E ↔ ¬ closure (cluster ν 1 z t) ⊆ ball 0 1) := by
  choose E hE hgood using fun n : ℕ =>
    exists_measurableSet_joint_clusterBufferFailure
      (ρ := 1 - 1 / ((n : ℝ) + 1)) ht
  refine ⟨⋂ n, E n, MeasurableSet.iInter hE, ?_⟩
  intro ν hloc hvol z
  simp only [mem_iInter, hgood _ ν hloc hvol z]
  exact (not_cluster_closure_subset_ball_iff ν t z).symm

end HarmonicBalls
