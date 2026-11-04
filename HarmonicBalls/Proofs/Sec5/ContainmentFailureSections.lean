import HarmonicBalls.Proofs.Sec5.DenseVolumeGrowth
import HarmonicBalls.Proofs.Sec5.ContainmentEventLaw

/-! # Centre sections of containment failure

For a fixed time, failure of compact containment is a countable intersection
of open sets of centres.  This records the remaining projection problem: the
centre witnessing all buffer failures must be the same for every buffer.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter TopologicalSpace

/-- Centres whose cluster meets the complement of a closed concentric disc. -/
def clusterBufferFailure (ν : Measure ℂ) (t ρ : ℝ) :
    Set (ball (0 : ℂ) (1 / 2)) :=
  {z | ∃ x ∈ cluster ν 1 z t, x ∉ closedBall 0 ρ}

/-- Every fixed-buffer failure section is open in the centre. -/
theorem isOpen_clusterBufferFailure
    {ν : Measure ℂ} (hloc : IsLocallyFiniteMeasure ν)
    {βm βp t ρ : ℝ} (hv : VolumeGrowth ν 1 βm βp) (ht : 0 < t) :
    IsOpen (clusterBufferFailure ν t ρ) := by
  let f : ball (0 : ℂ) (1 / 2) → ball (0 : ℂ) 1 := fun z =>
    ⟨z, ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) z.property⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have heq : clusterBufferFailure ν t ρ =
      ⋃ x : ℂ, ⋃ (_ : x ∉ closedBall (0 : ℂ) ρ),
        {z : ball (0 : ℂ) (1 / 2) | x ∈ cluster ν 1 z t} := by
    ext z
    simp only [clusterBufferFailure, mem_ofPred_eq, mem_iUnion]
    tauto
  rw [heq]
  apply isOpen_iUnion
  intro x
  apply isOpen_iUnion
  intro _
  exact (isOpen_cluster_centre_section hloc zero_lt_one hv ht x).preimage hf

/-- A centre fails compact containment exactly when it fails every disc in a
countable exhaustion of the unit disc. -/
theorem not_cluster_closure_subset_ball_iff
    (ν : Measure ℂ) (t : ℝ) (z : ball (0 : ℂ) (1 / 2)) :
    ¬ closure (cluster ν 1 z t) ⊆ ball 0 1 ↔
      ∀ n : ℕ, z ∈ clusterBufferFailure ν t (1 - 1 / ((n : ℝ) + 1)) := by
  have hcl : closure (cluster ν 1 z t) ⊆ closedBall (0 : ℂ) 1 :=
    closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
  have hk : IsCompact (closure (cluster ν 1 z t)) :=
    (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset isClosed_closure hcl
  rw [compact_subset_ball_iff_closedBall_exhaustion hk]
  simp only [not_exists, clusterBufferFailure, mem_ofPred_eq, not_subset]
  constructor
  · intro h n
    obtain ⟨x, hx, hxn⟩ := h n
    by_contra hbad
    have hsub : cluster ν 1 z t ⊆ closedBall (0 : ℂ) (1 - 1 / ((n : ℝ) + 1)) := by
      intro y hy
      by_contra hybad
      exact hbad ⟨y, hy, hybad⟩
    exact hxn (closure_minimal hsub isClosed_closedBall hx)
  · intro h n
    obtain ⟨x, hx, hxn⟩ := h n
    exact ⟨x, subset_closure hx, hxn⟩

/-- Failure of the all-centre event is the existence of a rational time and
one centre belonging to every fixed-buffer failure section at that time. -/
theorem not_mem_unitClusterContainmentEvent_iff
    (ν : Measure ℂ) (m : ℕ)
    (hmono : ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ s t : ℝ, 0 < s → s ≤ t →
      cluster ν 1 z s ⊆ cluster ν 1 z t) :
    ν ∉ unitClusterContainmentEvent m ↔
      ∃ q : ℚ, (q : ℝ) ∈ Ioo (0 : ℝ) ((2 : ℝ)⁻¹ ^ m) ∧
        ∃ z : ball (0 : ℂ) (1 / 2),
          ∀ n : ℕ, z ∈ clusterBufferFailure ν q (1 - 1 / ((n : ℝ) + 1)) := by
  classical
  constructor
  · intro h
    change ¬ (∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t ∈ Ioo (0 : ℝ) ((2 : ℝ)⁻¹ ^ m),
      closure (cluster ν 1 z t) ⊆ ball 0 1) at h
    push Not at h
    obtain ⟨z, hz, t, ht, hfail⟩ := h
    obtain ⟨q, htq, hqT⟩ := exists_rat_btwn ht.2
    have hq : (q : ℝ) ∈ Ioo (0 : ℝ) ((2 : ℝ)⁻¹ ^ m) :=
      ⟨lt_trans ht.1 htq, hqT⟩
    refine ⟨q, hq, ⟨z, hz⟩, (not_cluster_closure_subset_ball_iff ν q ⟨z, hz⟩).mp ?_⟩
    intro hgood
    exact hfail ((closure_mono (hmono z hz t q ht.1 htq.le)).trans hgood)
  · rintro ⟨q, hq, z, hz⟩ hgood
    exact (not_cluster_closure_subset_ball_iff ν q z).mpr hz (hgood z z.property q hq)

/-- Hitting a fixed open set of centres with a fixed-buffer failure has a
Borel representative on locally finite measures with volume growth. -/
theorem exists_measurableSet_clusterBufferFailure_hits
    {t ρ : ℝ} (ht : 0 < t)
    (U : Set (ball (0 : ℂ) (1 / 2))) (hU : IsOpen U) :
    ∃ E : Set (Measure ℂ), MeasurableSet E ∧ ∀ ν : Measure ℂ,
      IsLocallyFiniteMeasure ν → (∃ βm βp, VolumeGrowth ν 1 βm βp) →
      (ν ∈ E ↔ (U ∩ clusterBufferFailure ν t ρ).Nonempty) := by
  classical
  let J := ball (0 : ℂ) (1 / 2)
  let : Nonempty J := ⟨⟨0, by dsimp [J]; norm_num⟩⟩
  let e : ℕ → J := denseSeq J
  let e' : ℕ → ball (0 : ℂ) 1 := fun i =>
    ⟨e i, ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) (e i).property⟩
  choose A hA hAgood using fun (i k : ℕ) =>
    exists_measurableSet_mem_cluster_of_volumeGrowth zero_lt_one (e' i).property ht
      (x := denseSeq ℂ k)
  let E : Set (Measure ℂ) := ⋃ i, ⋃ k,
    if e i ∈ U ∧ denseSeq ℂ k ∉ closedBall (0 : ℂ) ρ then A i k else ∅
  have hE : MeasurableSet E := by
    apply MeasurableSet.iUnion
    intro i
    apply MeasurableSet.iUnion
    intro k
    split_ifs
    · exact hA i k
    · exact MeasurableSet.empty
  refine ⟨E, hE, ?_⟩
  intro ν hloc hvol
  constructor
  · intro h
    simp only [E, mem_iUnion] at h
    obtain ⟨i, k, hk⟩ := h
    split_ifs at hk with hc
    · exact ⟨e i, hc.1, denseSeq ℂ k, (hAgood i k ν hloc hvol).mp hk, hc.2⟩
    · simp at hk
  · rintro ⟨z, hzU, x, hx, hxρ⟩
    obtain ⟨βm, βp, hv⟩ := hvol
    have hopen : IsOpen (cluster ν 1 z t) :=
      (cluster_open_laplacian_of_general greenFunctionBall
        obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
        obstacleCompatibilityShiftStep_holds hloc zero_lt_one hv
        (ball_subset_ball (by norm_num) z.property) ht).1
    obtain ⟨k, hk⟩ := (denseRange_denseSeq ℂ).exists_mem_open
      (hopen.inter isClosed_closedBall.isOpen_compl) ⟨x, hx, hxρ⟩
    let f : J → ball (0 : ℂ) 1 := fun z =>
      ⟨z, ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) z.property⟩
    have hf : Continuous f := continuous_subtype_val.subtype_mk _
    have hop : IsOpen {z : J | denseSeq ℂ k ∈ cluster ν 1 z t} :=
      (isOpen_cluster_centre_section hloc zero_lt_one hv ht (denseSeq ℂ k)).preimage hf
    obtain ⟨i, hi⟩ := (denseRange_denseSeq J).exists_mem_open (hU.inter hop) ⟨z, hzU, hk.1⟩
    change ν ∈ E
    simp only [E, mem_iUnion]
    refine ⟨i, k, ?_⟩
    simp only [show e i ∈ U ∧ denseSeq ℂ k ∉ closedBall (0 : ℂ) ρ from ⟨hi.1, hk.2⟩]
    exact (hAgood i k ν hloc ⟨βm, βp, hv⟩).mpr hi.2

universe u

/-- A fixed-buffer failure hits a fixed open set of centres in a null
measurable event under the LQG measure law. -/
theorem IsWholePlaneGFF.nullMeasurableSet_clusterBufferFailure_hits_measureLaw
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {t ρ : ℝ} (ht : 0 < t)
    (U : Set (ball (0 : ℂ) (1 / 2))) (hU : IsOpen U) :
    NullMeasurableSet {ν : Measure ℂ | (U ∩ clusterBufferFailure ν t ρ).Nonempty}
      (Measure.map μ P) := by
  obtain ⟨G, _hG, hGae, hGgood⟩ := hGFF.exists_measurable_volumeGrowth_support
    hI2 hγ hγ2 hα hμ zero_lt_one
  obtain ⟨E, hE, hgood⟩ := exists_measurableSet_clusterBufferFailure_hits ht U hU
  apply hE.nullMeasurableSet.congr
  filter_upwards [hGae] with ν hν
  exact propext (hgood ν (hGgood ν hν).1 (hGgood ν hν).2)

end HarmonicBalls
