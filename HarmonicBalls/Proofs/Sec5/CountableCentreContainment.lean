import HarmonicBalls.Proofs.Sec5.LocalMeasureEvaluations

/-! # Local containment for countable centre families -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter TopologicalSpace

universe u

/-- At countably many centres, containment up to a fixed time is measurable
with respect to the field on the disc, modulo a null set. The reduction of
time to the rationals uses cluster monotonicity. -/
theorem exists_local_lqg_countableCentre_containment
    {Ω ι : Type u} [MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {R : ℝ} (hR : 0 < R) (e : ι → ball (0 : ℂ) R) (T : ℝ) :
    ∃ E : Set Ω, MeasurableSet[fieldSigmaAlgebra α₀ hC (ball 0 R)] E ∧
      {ω | ∀ i, ∀ t ∈ Ioo (0 : ℝ) T,
        closure (cluster (μ ω) R (e i) t) ⊆ ball 0 R} =ᵐ[P] E := by
  classical
  let Q := {q : ℚ // (q : ℝ) ∈ Ioo (0 : ℝ) T}
  choose E hE hEq using fun (i : ι) (q : Q) =>
    exists_local_lqg_cluster_ball_containment hI2 hγ hγ2 hα hGFF hμ hloc
      hR (e i).property q.property.1
  refine ⟨⋂ i, ⋂ q, E i q, MeasurableSet.iInter fun i => MeasurableSet.iInter (hE i), ?_⟩
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hEq i)),
    h33 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω heq hmono
  apply propext
  simp only [mem_iInter]
  constructor
  · intro h i q
    exact (propext_iff.mp (heq i q)).mp (h i q q.property)
  · intro h i t ht
    obtain ⟨q, htq, hqT⟩ := exists_rat_btwn ht.2
    let q' : Q := ⟨q, ⟨lt_trans ht.1 htq, hqT⟩⟩
    have hq : closure (cluster (μ ω) R (e i) q') ⊆ ball 0 R :=
      (propext_iff.mp (heq i q')).mpr (h i q')
    exact (closure_mono (hmono t q' R ht.1 htq.le hR (e i) (e i).property)).trans hq

/-- A Borel set of measures represents fixed-centre compact containment on
measures with volume growth whenever the cluster is open. -/
theorem exists_measurableSet_cluster_ball_containment_of_volumeGrowth
    {R t : ℝ} {z : ℂ} (hR : 0 < R) (hz : z ∈ ball (0 : ℂ) R) (ht : 0 < t) :
    ∃ E : Set (Measure ℂ), MeasurableSet E ∧ ∀ ν : Measure ℂ,
      IsLocallyFiniteMeasure ν → (∃ βminus βplus, VolumeGrowth ν R βminus βplus) →
      IsOpen (cluster ν R z t) →
      (ν ∈ E ↔ closure (cluster ν R z t) ⊆ ball 0 R) := by
  classical
  choose A hA hAgood using fun m : ℕ =>
    exists_measurableSet_mem_cluster_of_volumeGrowth hR hz ht (x := denseSeq ℂ m)
  let B : ℕ → Set (Measure ℂ) := fun n => ⋂ m,
    if denseSeq ℂ m ∈ closedBall (0 : ℂ) (R - 1 / ((n : ℝ) + 1)) then univ else (A m)ᶜ
  have hB (n : ℕ) : MeasurableSet (B n) := by
    apply MeasurableSet.iInter
    intro m
    split_ifs
    · exact MeasurableSet.univ
    · exact (hA m).compl
  refine ⟨⋃ n, B n, MeasurableSet.iUnion hB, ?_⟩
  intro ν hloc hvol hopen
  have hcl : closure (cluster ν R z t) ⊆ closedBall (0 : ℂ) R :=
    isClosed_closedBall.closure_subset_iff.mpr (cluster_subset_ball.trans ball_subset_closedBall)
  have hk : IsCompact (closure (cluster ν R z t)) :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset isClosed_closure hcl
  rw [compact_subset_ball_iff_closedBall_exhaustion hk]
  simp only [mem_iUnion]
  apply exists_congr
  intro n
  rw [closure_subset_closedBall_iff_denseSeq hopen]
  simp only [B, mem_iInter]
  constructor
  · intro h m hm
    by_contra hc
    have hmA : ν ∈ A m := (hAgood m ν hloc hvol).mpr hm
    have := h m
    simp only [hc, ↓reduceIte, mem_compl_iff] at this
    exact this hmA
  · intro h m
    by_cases hc : denseSeq ℂ m ∈ closedBall (0 : ℂ) (R - 1 / ((n : ℝ) + 1))
    · simp only [hc, ↓reduceIte, mem_univ]
    · simp only [hc, ↓reduceIte, mem_compl_iff]
      intro hmA
      exact hc (h m ((hAgood m ν hloc hvol).mp hmA))

/-- One Borel set represents countable-centre containment for every measure
with volume growth and open, increasing clusters at those centres. -/
theorem exists_measurableSet_countableCentre_containment
    {ι : Type*} [Countable ι] {R : ℝ} (hR : 0 < R)
    (e : ι → ball (0 : ℂ) R) (T : ℝ) :
    ∃ E : Set (Measure ℂ), MeasurableSet E ∧ ∀ ν : Measure ℂ,
      IsLocallyFiniteMeasure ν → (∃ βminus βplus, VolumeGrowth ν R βminus βplus) →
      (∀ i s, 0 < s → IsOpen (cluster ν R (e i) s)) →
      (∀ i s s', 0 < s → s ≤ s' → cluster ν R (e i) s ⊆ cluster ν R (e i) s') →
      (ν ∈ E ↔ ∀ i, ∀ t ∈ Ioo (0 : ℝ) T,
        closure (cluster ν R (e i) t) ⊆ ball 0 R) := by
  classical
  let Q := {q : ℚ // (q : ℝ) ∈ Ioo (0 : ℝ) T}
  choose A hA hAgood using fun (i : ι) (q : Q) =>
    exists_measurableSet_cluster_ball_containment_of_volumeGrowth hR (e i).property q.property.1
  refine ⟨⋂ i, ⋂ q, A i q, MeasurableSet.iInter fun i => MeasurableSet.iInter (hA i), ?_⟩
  intro ν hloc hvol hopen hmono
  simp only [mem_iInter]
  constructor
  · intro h i t ht
    obtain ⟨q, htq, hqT⟩ := exists_rat_btwn ht.2
    let q' : Q := ⟨q, ⟨lt_trans ht.1 htq, hqT⟩⟩
    have hq : closure (cluster ν R (e i) q') ⊆ ball 0 R :=
      (hAgood i q' ν hloc hvol (hopen i q' q'.property.1)).mp (h i q')
    exact (closure_mono (hmono i t q' ht.1 htq.le)).trans hq
  · intro h i q
    exact (hAgood i q ν hloc hvol (hopen i q q.property.1)).mpr (h i q q.property)

/-- The countable-centre event has a Borel representative on measures, valid
almost surely for the given LQG measure. This does not quantify over every
centre. -/
theorem exists_measure_borel_countableCentre_containment
    {Ω ι : Type u} [MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {R : ℝ} (hR : 0 < R) (e : ι → ball (0 : ℂ) R) (T : ℝ) :
    ∃ E : Set (Measure ℂ), MeasurableSet E ∧
      ∀ᵐ ω ∂P, (μ ω ∈ E ↔ ∀ i, ∀ t ∈ Ioo (0 : ℝ) T,
        closure (cluster (μ ω) R (e i) t) ⊆ ball 0 R) := by
  obtain ⟨E, hE, hgood⟩ := exists_measurableSet_countableCentre_containment hR e T
  refine ⟨E, hE, ?_⟩
  obtain ⟨βm, βp, hvol⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hvol, clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hv hopen hmono
  exact hgood (μ ω) hv.1 ⟨βm, βp, hv.2 R hR⟩
    (fun i s hs => (hopen s R hs hR (e i) (e i).property).1)
    (fun i s s' hs hss => hmono s s' R hs hss hR (e i) (e i).property)

/-- The countable-centre containment event is null measurable on the original
probability space. -/
theorem nullMeasurableSet_lqg_countableCentre_containment
    {Ω ι : Type u} [MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {R : ℝ} (hR : 0 < R) (e : ι → ball (0 : ℂ) R) (T : ℝ) :
    NullMeasurableSet {ω | ∀ i, ∀ t ∈ Ioo (0 : ℝ) T,
      closure (cluster (μ ω) R (e i) t) ⊆ ball 0 R} P := by
  obtain ⟨E, hE, heq⟩ := exists_measure_borel_countableCentre_containment hI2 h33
    hγ hγ2 hα hGFF hμ hR e T
  have hnull := (hGFF.aemeasurable_lqgMeasure hμ).nullMeasurableSet_preimage hE
  apply hnull.congr
  filter_upwards [heq] with ω hω
  exact propext hω

end HarmonicBalls
