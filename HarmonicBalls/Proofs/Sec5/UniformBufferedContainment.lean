import HarmonicBalls.Proofs.Sec5.ObstacleCentreContinuity
import HarmonicBalls.Proofs.Sec5.LocalMeasureEvaluations

/-!
# Measurability of buffered containment for all centres

For a fixed closed target disc, dense-centre and rational-time tests detect
containment uniformly over all centres. This fixed-buffer event is different
from compact containment in the unit disc with a potentially varying buffer.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set TopologicalSpace Filter

universe u

/-- The all-centre, all-time closed-disc containment event has a Borel
representative on measures with volume growth and open monotone clusters. -/
theorem exists_measurableSet_uniform_buffered_containment (ρ T : ℝ) :
    ∃ E : Set (Measure ℂ), MeasurableSet E ∧ ∀ ν : Measure ℂ,
      IsLocallyFiniteMeasure ν → (∃ βm βp, VolumeGrowth ν 1 βm βp) →
      (∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t : ℝ, 0 < t → IsOpen (cluster ν 1 z t)) →
      (∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ s t : ℝ, 0 < s → s ≤ t →
        cluster ν 1 z s ⊆ cluster ν 1 z t) →
      (ν ∈ E ↔ ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t ∈ Ioo (0 : ℝ) T,
        closure (cluster ν 1 z t) ⊆ closedBall 0 ρ) := by
  classical
  let J := {z // z ∈ ball (0 : ℂ) (1 / 2)}
  let : Nonempty J := ⟨⟨0, by norm_num⟩⟩
  let e : ℕ → J := denseSeq J
  let e' : ℕ → ball (0 : ℂ) 1 := fun i =>
    ⟨e i, ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) (e i).property⟩
  let Q := {q : ℚ // (q : ℝ) ∈ Ioo (0 : ℝ) T}
  choose A hA hAgood using fun (i : ℕ) (q : Q) (m : ℕ) =>
    exists_measurableSet_mem_cluster_of_volumeGrowth zero_lt_one (e' i).property
      q.property.1 (x := denseSeq ℂ m)
  let E : Set (Measure ℂ) := ⋂ i, ⋂ q, ⋂ m,
    if denseSeq ℂ m ∈ closedBall (0 : ℂ) ρ then univ else (A i q m)ᶜ
  have hE : MeasurableSet E := by
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro q
    apply MeasurableSet.iInter
    intro m
    split_ifs
    · exact MeasurableSet.univ
    · exact (hA i q m).compl
  refine ⟨E, hE, ?_⟩
  intro ν hloc hvol hopen hmono
  have hcount : ν ∈ E ↔ ∀ (i : ℕ) (q : Q),
      closure (cluster ν 1 (e i) q) ⊆ closedBall 0 ρ := by
    simp only [E, mem_iInter]
    apply forall_congr'
    intro i
    apply forall_congr'
    intro q
    rw [closure_subset_closedBall_iff_denseSeq (hopen (e i) (e i).property q q.property.1)]
    constructor
    · intro h m hm
      by_contra hc
      have hmA : ν ∈ A i q m := (hAgood i q m ν hloc hvol).mpr hm
      have := h m
      simp only [hc, ↓reduceIte, mem_compl_iff] at this
      exact this hmA
    · intro h m
      by_cases hc : denseSeq ℂ m ∈ closedBall (0 : ℂ) ρ
      · simp only [hc, ↓reduceIte, mem_univ]
      · simp only [hc, ↓reduceIte, mem_compl_iff]
        intro hmA
        exact hc (h m ((hAgood i q m ν hloc hvol).mp hmA))
  rw [hcount]
  constructor
  · intro h z hz t ht
    obtain ⟨q, htq, hqT⟩ := exists_rat_btwn ht.2
    let q' : Q := ⟨q, ⟨lt_trans ht.1 htq, hqT⟩⟩
    have hsub : cluster ν 1 z q' ⊆ closedBall (0 : ℂ) ρ := by
      intro x hx
      let f : J → ball (0 : ℂ) 1 := fun j =>
        ⟨j, ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) j.property⟩
      have hf : Continuous f := continuous_subtype_val.subtype_mk _
      obtain ⟨βm, βp, hv⟩ := hvol
      have hop : IsOpen {j : J | x ∈ cluster ν 1 j q'} :=
        (isOpen_cluster_centre_section hloc zero_lt_one hv q'.property.1 x).preimage hf
      obtain ⟨i, hi⟩ := (denseRange_denseSeq J).exists_mem_open hop ⟨⟨z, hz⟩, hx⟩
      exact h i q' (subset_closure hi)
    apply closure_minimal _ isClosed_closedBall
    exact (hmono z hz t q' ht.1 htq.le).trans hsub
  · intro h i q
    exact h (e i) (e i).property q q.property

/-- For an LQG measure the fixed-buffer uniform-containment event is null
measurable on the original probability space. -/
theorem nullMeasurableSet_lqg_uniform_buffered_containment
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (ρ T : ℝ) :
    NullMeasurableSet {ω | ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t ∈ Ioo (0 : ℝ) T,
      closure (cluster (μ ω) 1 z t) ⊆ closedBall 0 ρ} P := by
  obtain ⟨E, hE, hgood⟩ := exists_measurableSet_uniform_buffered_containment ρ T
  obtain ⟨βm, βp, hvol⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  have heq : ∀ᵐ ω ∂P, (μ ω ∈ E ↔ ∀ z ∈ ball (0 : ℂ) (1 / 2),
      ∀ t ∈ Ioo (0 : ℝ) T, closure (cluster (μ ω) 1 z t) ⊆ closedBall 0 ρ) := by
    filter_upwards [hvol, clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
      clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hv hopen hmono
    exact hgood (μ ω) hv.1 ⟨βm, βp, hv.2 1 zero_lt_one⟩
      (fun z hz t ht => (hopen t 1 ht zero_lt_one z (ball_subset_ball (by norm_num) hz)).1)
      (fun z hz s t hs hst => hmono s t 1 hs hst zero_lt_one z (ball_subset_ball (by norm_num) hz))
  have hnull := (hGFF.aemeasurable_lqgMeasure hμ).nullMeasurableSet_preimage hE
  apply hnull.congr
  filter_upwards [heq] with ω hω
  exact propext hω

end HarmonicBalls
