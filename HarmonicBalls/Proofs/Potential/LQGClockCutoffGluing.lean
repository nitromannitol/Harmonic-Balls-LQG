import HarmonicBalls.Proofs.Potential.LQGClockInnerUniformTime
import HarmonicBalls.Proofs.Potential.LQGClockAnnularLimitRegularity

/-! # Uniform limits from cutoff approximations

Uniformly convergent cutoff clocks and vanishing cutoff errors give a uniform
limit for the uncut clocks.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- Uniformly convergent cutoff approximations with a uniformly vanishing
cutoff error imply uniform convergence. -/
theorem exists_tendstoUniformly_of_cutoff_approximations
    {T : Type*} (A : ℕ → T → ℝ) (B : ℕ → ℕ → T → ℝ) (e : ℕ → ℝ)
    (hB : ∀ n, ∃ F : T → ℝ, TendstoUniformly (B n) F atTop)
    (he : Tendsto e atTop (𝓝 0))
    (herror : ∀ n i t, dist (A i t) (B n i t) ≤ e n) :
    ∃ F : T → ℝ, TendstoUniformly A F atTop := by
  have huc : UniformCauchySeqOn A atTop univ := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro η hη
    have hη4 : 0 < η/4 := by positivity
    obtain ⟨n, hn⟩ := (he.eventually (Iio_mem_nhds hη4)).exists
    obtain ⟨F, hF⟩ := hB n
    rw [Metric.tendstoUniformly_iff] at hF
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hF (η/4) hη4)
    refine ⟨N, ?_⟩
    intro i hi j hj t _
    have hiF := hN i hi t
    have hjF := hN j hj t
    have h1 := herror n i t
    have h2 := herror n j t
    have h3 := dist_triangle (A i t) (B n i t) (A j t)
    have h4 := dist_triangle (B n i t) (F t) (A j t)
    have h5 := dist_triangle (F t) (B n j t) (A j t)
    rw [dist_comm (B n i t) (F t), dist_comm (F t) (A j t)] at h4
    rw [dist_comm (F t), dist_comm (B n j t)] at h5
    linarith
  let F : T → ℝ := fun t => limUnder atTop (fun i => A i t)
  have hpoint (t : T) : Tendsto (fun i => A i t) atTop (𝓝 (F t)) := by
    apply tendsto_nhds_limUnder
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro η hη
    obtain ⟨N, hN⟩ := (Metric.uniformCauchySeqOn_iff.mp huc) η hη
    exact ⟨N, fun i hi j hj => hN i hi j hj t (Set.mem_univ t)⟩
  refine ⟨F, tendstoUniformlyOn_univ.mp ?_⟩
  exact huc.tendstoUniformlyOn_of_tendsto (fun t _ => hpoint t)

/-- Uniform convergence from cutoff approximations also holds when the cutoff
error is extended-real valued and tends to zero. -/
theorem exists_tendstoUniformly_of_ennreal_cutoff_approximations
    {T : Type*} (A : ℕ → T → ℝ) (B : ℕ → ℕ → T → ℝ) (e : ℕ → ℝ≥0∞)
    (hB : ∀ n, ∃ F : T → ℝ, TendstoUniformly (B n) F atTop)
    (he : Tendsto e atTop (𝓝 0))
    (herror : ∀ n i t, ENNReal.ofReal (dist (A i t) (B n i t)) ≤ e n) :
    ∃ F : T → ℝ, TendstoUniformly A F atTop := by
  have huc : UniformCauchySeqOn A atTop univ := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro η hη
    have hη4 : 0 < η/4 := by positivity
    obtain ⟨n, hn⟩ := (he.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hη4))).exists
    obtain ⟨F, hF⟩ := hB n
    rw [Metric.tendstoUniformly_iff] at hF
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hF (η/4) hη4)
    refine ⟨N, ?_⟩
    intro i hi j hj t _
    have hiF := hN i hi t
    have hjF := hN j hj t
    have h1 : dist (A i t) (B n i t) < η/4 :=
      (ENNReal.ofReal_lt_ofReal_iff hη4).mp ((herror n i t).trans_lt hn)
    have h2 : dist (A j t) (B n j t) < η/4 :=
      (ENNReal.ofReal_lt_ofReal_iff hη4).mp ((herror n j t).trans_lt hn)
    have h3 := dist_triangle (A i t) (B n i t) (A j t)
    have h4 := dist_triangle (B n i t) (F t) (A j t)
    have h5 := dist_triangle (F t) (B n j t) (A j t)
    rw [dist_comm (B n i t) (F t), dist_comm (F t) (A j t)] at h4
    rw [dist_comm (F t), dist_comm (B n j t)] at h5
    linarith
  let F : T → ℝ := fun t => limUnder atTop (fun i => A i t)
  have hpoint (t : T) : Tendsto (fun i => A i t) atTop (𝓝 (F t)) := by
    apply tendsto_nhds_limUnder
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro η hη
    obtain ⟨N, hN⟩ := (Metric.uniformCauchySeqOn_iff.mp huc) η hη
    exact ⟨N, fun i hi j hj => hN i hi j hj t (Set.mem_univ t)⟩
  refine ⟨F, tendstoUniformlyOn_univ.mp ?_⟩
  exact huc.tendstoUniformlyOn_of_tendsto (fun t _ => hpoint t)


private theorem integrable_half_disc_indicator (μ : Measure ℂ) [IsFiniteMeasure μ]
    (f : ℂ → ℝ) (hf : Continuous f) (E : Set ℂ) (hE : MeasurableSet E)
    (hsub : ∀ z ∈ E, ‖z‖ ≤ 1/2) : Integrable (E.indicator f) μ := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (1/2 : ℝ)).bddAbove_image hf.norm.continuousOn
  apply (integrable_const (max K 0)).mono' (hf.measurable.indicator hE).aestronglyMeasurable
  filter_upwards with z
  by_cases hz : z ∈ E
  · have hzball : z ∈ Metric.closedBall (0 : ℂ) (1/2 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hsub z hz
    rw [Set.indicator_of_mem hz]
    exact (hK ⟨z, hzball, rfl⟩).trans (le_max_left K 0)
  · rw [Set.indicator_of_notMem hz, norm_zero]
    exact le_max_right K 0

/-- The distance from the half-disc clock to its annular cutoff equals the
nonnegative inner occupation over the same bounded time interval. -/
theorem ofReal_dist_halfDisc_annularClock_eq_inner
    (b : ContinuousPath ℂ) (f : ℂ → ℝ) (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z)
    (δ : ℝ) (t : Icc (0 : ℝ) 1) :
    ENNReal.ofReal (dist (stoppedAnnularClock f 0 (fun _ => t.1.toNNReal) b)
      (stoppedAnnularClock f δ (fun _ => t.1.toNNReal) b)) =
    ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
      ({z : ℂ | ‖z‖ < δ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal)) := by
  let E : Set ℂ := {z | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  let I : Set ℂ := {z | ‖z‖ < δ ∧ ‖z‖ ≤ 1/2}
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let μ : Measure ℂ := Measure.map (fun u => b u) (ν.restrict (Iic t.1.toNNReal))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  have hμ : μ ≤ Measure.map (fun u => b u) ν :=
    Measure.map_mono Measure.restrict_le_self b.continuous.measurable
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le (Measure.map (fun u => b u) ν) hμ
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hI : MeasurableSet I :=
    (measurableSet_lt measurable_norm measurable_const).inter
      (measurableSet_le measurable_norm measurable_const)
  have hi : Integrable (I.indicator f) μ :=
    integrable_half_disc_indicator μ f hf I hI (fun _ hz => hz.2)
  have ha : Integrable (A.indicator f) μ :=
    integrable_half_disc_indicator μ f hf A hA (fun _ hz => hz.2)
  have hsplit : E.indicator f = fun z => A.indicator f z + I.indicator f z := by
    funext z
    by_cases hz : ‖z‖ ≤ 1/2
    · have he : z ∈ E := ⟨norm_nonneg _, hz⟩
      by_cases hδ : δ ≤ ‖z‖
      · have ha' : z ∈ A := ⟨hδ, hz⟩
        have hi' : z ∉ I := fun h => (not_lt.mpr hδ) h.1
        rw [Set.indicator_of_mem he, Set.indicator_of_mem ha', Set.indicator_of_notMem hi', add_zero]
      · have ha' : z ∉ A := fun h => hδ h.1
        have hi' : z ∈ I := ⟨lt_of_not_ge hδ, hz⟩
        rw [Set.indicator_of_mem he, Set.indicator_of_notMem ha', Set.indicator_of_mem hi', zero_add]
    · have he : z ∉ E := fun h => hz h.2
      have ha' : z ∉ A := fun h => hz h.2
      have hi' : z ∉ I := fun h => hz h.2
      rw [Set.indicator_of_notMem he, Set.indicator_of_notMem ha', Set.indicator_of_notMem hi', add_zero]
  have hdiff : stoppedAnnularClock f 0 (fun _ => t.1.toNNReal) b -
      stoppedAnnularClock f δ (fun _ => t.1.toNNReal) b = ∫ z, I.indicator f z ∂μ := by
    change (∫ z, E.indicator f z ∂μ) - (∫ z, A.indicator f z ∂μ) = _
    rw [hsplit, integral_add ha hi]
    ring
  have hnonneg : 0 ≤ ∫ z, I.indicator f z ∂μ := by
    apply integral_nonneg
    intro z
    change (0 : ℝ) ≤ I.indicator f z
    by_cases hz : z ∈ I
    · rw [Set.indicator_of_mem hz]
      exact hf0 z
    · simp [hz]
  rw [Real.dist_eq, hdiff, abs_of_nonneg hnonneg, ofReal_integral_eq_lintegral_ofReal hi]
  · have hm : Measurable (fun z => ENNReal.ofReal (I.indicator f z)) :=
      (hf.measurable.indicator hI).ennreal_ofReal
    rw [show μ = Measure.map (fun u => b u) (ν.restrict (Iic t.1.toNNReal)) from rfl,
      lintegral_map hm b.continuous.measurable]
    dsimp [ν]
    rw [Measure.restrict_map continuous_real_toNNReal.measurable measurableSet_Iic]
    rw [Measure.restrict_restrict (continuous_real_toNNReal.measurable measurableSet_Iic)]
    rw [lintegral_map (f := fun u : ℝ≥0 => ENNReal.ofReal (I.indicator f (b u)))
      (hm.comp b.continuous.measurable) continuous_real_toNNReal.measurable]
    have hsets : (Real.toNNReal ⁻¹' Iic t.1.toNNReal) ∩ Icc (0 : ℝ) 1 = Icc 0 t.1 := by
      ext s
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨hs, h0, _⟩
        exact ⟨h0, by simpa [Real.toNNReal_of_nonneg t.2.1] using
          (Real.toNNReal_le_iff_le_coe).mp hs⟩
      · rintro ⟨h0, hs⟩
        refine ⟨?_, h0, hs.trans t.2.2⟩
        exact (Real.toNNReal_le_iff_le_coe).mpr (by simpa [Real.toNNReal_of_nonneg t.2.1] using hs)
    rw [hsets, Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
  · filter_upwards with z
    change (0 : ℝ) ≤ I.indicator f z
    by_cases hz : z ∈ I
    · rw [Set.indicator_of_mem hz]
      exact hf0 z
    · simp [hz]


end HarmonicBalls
