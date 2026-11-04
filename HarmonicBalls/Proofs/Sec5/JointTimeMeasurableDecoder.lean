import HarmonicBalls.Proofs.Sec5.PotentialMeasurableDecoder
import HarmonicBalls.Proofs.Sec5.CountableTimeMeasurability

/-! # Joint measure and time decoders for clusters -/

namespace HarmonicBalls

open MeasureTheory Metric Set TopologicalSpace

/-- A Borel set represents membership in a cluster jointly in the measure
and positive time, on locally finite measures satisfying volume growth. -/
theorem exists_measurableSet_mem_cluster_joint_time_of_volumeGrowth
    {R : ℝ} {z x : ℂ} (hR : 0 < R) (hz : z ∈ ball (0 : ℂ) R) :
    ∃ E : Set (Measure ℂ × ℝ), MeasurableSet E ∧ ∀ ν : Measure ℂ,
      IsLocallyFiniteMeasure ν → (∃ βminus βplus, VolumeGrowth ν R βminus βplus) →
      ∀ t : ℝ, 0 < t → ((ν, t) ∈ E ↔ x ∈ cluster ν R z t) := by
  classical
  choose E hE hcorrect using fun q : {q : ℚ // 0 < (q : ℝ)} =>
    exists_measurableSet_mem_cluster_of_volumeGrowth (x := x) hR hz q.property
  let A : Set (Measure ℂ × ℝ) := ⋃ q : {q : ℚ // 0 < (q : ℝ)},
    {p | p.1 ∈ E q ∧ (q : ℝ) < p.2}
  have hA : MeasurableSet A := by
    apply MeasurableSet.iUnion
    intro q
    exact ((hE q).preimage measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd)
  refine ⟨A, hA, ?_⟩
  intro ν hloc hvol t ht
  obtain ⟨βminus, βplus, hv⟩ := hvol
  constructor
  · intro h
    obtain ⟨q, hν, hqt⟩ := Set.mem_iUnion.mp h
    apply cluster_subset_of_general obstacleMonotoneGeneral_holds
      obstacleCompatibilityShiftStep_holds hloc hR hv hz q.property hqt.le
    exact (hcorrect q ν hloc ⟨βminus, βplus, hv⟩).mp hν
  · intro hx
    obtain ⟨q, hq0, hqt, hxq⟩ := mem_cluster_exists_earlier_rat ht hx
    exact Set.mem_iUnion.mpr ⟨⟨q, hq0⟩,
      (hcorrect ⟨q, hq0⟩ ν hloc ⟨βminus, βplus, hv⟩).mpr hxq, hqt⟩

/-- A measurable set-valued decoder represents the cluster jointly in the
measure and positive time, for all locally finite volume-growth measures. -/
theorem exists_measurable_cluster_joint_time_of_volumeGrowth
    {R : ℝ} {z : ℂ} (hR : 0 < R) (hz : z ∈ ball (0 : ℂ) R) :
    ∃ F : Measure ℂ × ℝ → Set ℂ, Measurable F ∧ ∀ ν : Measure ℂ,
      IsLocallyFiniteMeasure ν → (∃ βminus βplus, VolumeGrowth ν R βminus βplus) →
      ∀ t : ℝ, 0 < t → F (ν, t) = cluster ν R z t := by
  classical
  choose E hE hcorrect using fun x : ℂ =>
    exists_measurableSet_mem_cluster_joint_time_of_volumeGrowth (x := x) hR hz
  refine ⟨fun p => {x | p ∈ E x}, ?_, ?_⟩
  · apply Measurable.of_eval
    intro x
    exact (hE x).mem
  · intro ν hloc hvol t ht
    ext x
    exact hcorrect x ν hloc hvol t ht

/-- The closure of the cluster has a jointly measurable decoder on the
same class of measures and times. -/
theorem exists_measurable_closedCluster_joint_time_of_volumeGrowth
    {R : ℝ} {z : ℂ} (hR : 0 < R) (hz : z ∈ ball (0 : ℂ) R) :
    ∃ F : Measure ℂ × ℝ → Set ℂ, Measurable F ∧ ∀ ν : Measure ℂ,
      IsLocallyFiniteMeasure ν → (∃ βminus βplus, VolumeGrowth ν R βminus βplus) →
      ∀ t : ℝ, 0 < t → F (ν, t) = closure (cluster ν R z t) := by
  classical
  obtain ⟨F, hF, hcorrect⟩ := exists_measurable_cluster_joint_time_of_volumeGrowth hR hz
  let G : Measure ℂ × ℝ → Set ℂ := fun p => {x | ∀ n : ℕ, ∃ m : ℕ,
    denseSeq ℂ m ∈ F p ∧ dist x (denseSeq ℂ m) < 1 / ((n : ℝ) + 1)}
  refine ⟨G, ?_, ?_⟩
  · apply Measurable.of_eval
    intro x
    apply Measurable.forall
    intro n
    apply Measurable.exists
    intro m
    exact ((measurable_pi_apply (denseSeq ℂ m)).comp hF).and measurable_const
  · intro ν hloc hvol t ht
    obtain ⟨βminus, βplus, hv⟩ := hvol
    have hopen : IsOpen (cluster ν R z t) := by
      rw [(obstacleCompatibilityShiftStep_holds ν hloc R βminus βplus hR hv z hz t ht).2.2.1]
      exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds hloc hR hv hz ht
    ext x
    change (∀ n : ℕ, ∃ m : ℕ, denseSeq ℂ m ∈ F (ν, t) ∧
      dist x (denseSeq ℂ m) < 1 / ((n : ℝ) + 1)) ↔ _
    rw [hcorrect ν hloc ⟨βminus, βplus, hv⟩ t ht]
    exact (mem_closure_iff_denseSeq hopen x).symm

#print axioms exists_measurableSet_mem_cluster_joint_time_of_volumeGrowth
#print axioms exists_measurable_cluster_joint_time_of_volumeGrowth
#print axioms exists_measurable_closedCluster_joint_time_of_volumeGrowth

end HarmonicBalls
