import HarmonicBalls.Proofs.Sec5.UniformBufferedContainment
import HarmonicBalls.Proofs.Sec5.LocalMeasureEvaluations

/-! # Field locality of uniformly buffered containment

A fixed closed-disc buffer makes the all-centre containment event a
countable intersection of local events, modulo a null set. -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter TopologicalSpace

universe u

/-- Uniform containment in a fixed closed disc up to a fixed time has a
field-local representative. The locality input remains a proposed input. -/
theorem exists_local_lqg_uniform_buffered_containment
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) (ρ T : ℝ) :
    ∃ E : Set Ω, MeasurableSet[fieldSigmaAlgebra α₀ hC (ball 0 1)] E ∧
      {ω | ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t ∈ Ioo (0 : ℝ) T,
        closure (cluster (μ ω) 1 z t) ⊆ closedBall 0 ρ} =ᵐ[P] E := by
  classical
  let J := {z // z ∈ ball (0 : ℂ) (1 / 2)}
  let : Nonempty J := ⟨⟨0, by norm_num⟩⟩
  let e : ℕ → J := denseSeq J
  let e' : ℕ → ball (0 : ℂ) 1 := fun i =>
    ⟨e i, ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) (e i).property⟩
  let Q := {q : ℚ // (q : ℝ) ∈ Ioo (0 : ℝ) T}
  choose E hE hEq using fun (i : ℕ) (q : Q) =>
    exists_local_lqg_cluster_closedBall_containment hI2 hγ hγ2 hα hGFF hμ hloc
      zero_lt_one (e' i).property q.property.1 ρ
  refine ⟨⋂ i, ⋂ q, E i q, MeasurableSet.iInter fun i => MeasurableSet.iInter (hE i), ?_⟩
  obtain ⟨βm, βp, hvol⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hEq i)), hvol,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω heq hv hmono
  apply propext
  simp only [mem_iInter]
  constructor
  · intro h i q
    exact (propext_iff.mp (heq i q)).mp (h (e i) (e i).property q q.property)
  · intro h z hz t ht
    obtain ⟨q, htq, hqT⟩ := exists_rat_btwn ht.2
    let q' : Q := ⟨q, ⟨lt_trans ht.1 htq, hqT⟩⟩
    have hsub : cluster (μ ω) 1 z q' ⊆ closedBall (0 : ℂ) ρ := by
      intro x hx
      let f : J → ball (0 : ℂ) 1 := fun j =>
        ⟨j, ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) j.property⟩
      have hf : Continuous f := continuous_subtype_val.subtype_mk _
      have hop : IsOpen {j : J | x ∈ cluster (μ ω) 1 j q'} :=
        (isOpen_cluster_centre_section hv.1 zero_lt_one (hv.2 1 zero_lt_one)
          q'.property.1 x).preimage hf
      obtain ⟨i, hi⟩ := (denseRange_denseSeq J).exists_mem_open hop ⟨⟨z, hz⟩, hx⟩
      exact (propext_iff.mp (heq i q')).mpr (h i q') (subset_closure hi)
    apply closure_minimal _ isClosed_closedBall
    exact (hmono t q' 1 ht.1 htq.le zero_lt_one z
      (ball_subset_ball (by norm_num) hz)).trans hsub

end HarmonicBalls
