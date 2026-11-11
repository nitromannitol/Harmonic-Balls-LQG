import HarmonicBalls.Proofs.Sec5.PuncturedMinorantComparison

/-! # Punctured-disc boundary contact

The Green function has a positive limit at the removed point, where its total
extension is zero. An admissible least supersolution therefore forces its
cluster to approach the puncture at every positive time.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- The Green function of the punctured disc converges to the full-disc
Green function at the removed point. -/
theorem tendsto_greenFunction_punctured_ball_at_puncture
    {R : ℝ} {z a : ℂ}
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a}) :
    Tendsto (greenFunction (ball (0 : ℂ) R \ {a}) z)
      (𝓝[ball (0 : ℂ) R \ {a}] a) (𝓝 (greenFunction (ball (0 : ℂ) R) z a)) := by
  have haz : a ≠ z := by simpa using Ne.symm (show z ≠ a by simpa using hz.2)
  have hcont : ContinuousAt (greenFunction (ball (0 : ℂ) R) z) a :=
    (continuousOn_greenFunction_ball hz.1).continuousAt (isOpen_compl_singleton.mem_nhds haz)
  apply Tendsto.congr' _ (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ x in 𝓝 a, x ≠ z from isOpen_compl_singleton.mem_nhds haz).filter_mono
      (nhdsWithin_le_nhds : 𝓝[ball (0 : ℂ) R \ {a}] a ≤ 𝓝 a)] with x hx hxz
  exact (greenFunction_punctured_ball ha hz hx hxz).symm

/-- The zero extension of the Green function is discontinuous at the puncture
when approached through the punctured disc. -/
theorem not_continuousWithinAt_greenFunction_punctured_ball
    {R : ℝ} {z a : ℂ}
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a}) :
    ¬ ContinuousWithinAt (greenFunction (ball (0 : ℂ) R \ {a}) z)
      (ball (0 : ℂ) R \ {a}) a := by
  have hza : z ≠ a := by simpa using hz.2
  have hac : a ∈ closure (ball (0 : ℂ) R \ {a}) := by
    have h := (dense_compl_singleton a).open_subset_closure_inter isOpen_ball ha
    simpa [sdiff_eq, inter_comm] using h
  have : (𝓝[ball (0 : ℂ) R \ {a}] a).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hac
  have hpos := greenFunction_ball_pos hz.1 ha hza
  intro hcont
  have hlim := tendsto_greenFunction_punctured_ball_at_puncture ha hz
  have heq := tendsto_nhds_unique hlim hcont
  have haU : a ∉ ball (0 : ℂ) R \ {a} := by simp
  rw [greenFunction_of_notMem_right haU] at heq
  linarith

/-- Admissibility forces all points of the domain sufficiently near the
puncture to belong to the cluster. -/
theorem eventually_mem_clusterOn_punctured_disc_of_admissible
    {μ : Measure ℂ} {R t : ℝ} {z a : ℂ}
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a}) (ht : 0 < t)
    (hv : leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t ∈
      supersolutionsOn μ (ball (0 : ℂ) R \ {a}) z t) :
    ∀ᶠ x in 𝓝[ball (0 : ℂ) R \ {a}] a,
      x ∈ clusterOn μ (ball (0 : ℂ) R \ {a}) z t := by
  have hza : z ≠ a := by simpa using hz.2
  have haz : a ≠ z := Ne.symm hza
  have hac : a ∈ closure (ball (0 : ℂ) R \ {a}) := by
    have h := (dense_compl_singleton a).open_subset_closure_inter isOpen_ball ha
    simpa [sdiff_eq, inter_comm] using h
  have haU : a ∉ ball (0 : ℂ) R \ {a} := by simp
  have hv0 : 0 ≤ leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t a := by
    have h := hv.2.2 a hac haz
    simpa [greenFunction_of_notMem_right haU] using h
  let c := greenFunction (ball (0 : ℂ) R) z a / 2
  have hc : 0 < c := by
    dsimp [c]
    linarith [greenFunction_ball_pos hz.1 ha hza]
  have hG : ∀ᶠ x in 𝓝[ball (0 : ℂ) R \ {a}] a,
      c < greenFunction (ball (0 : ℂ) R \ {a}) z x :=
    (tendsto_greenFunction_punctured_ball_at_puncture ha hz).eventually
      (Ioi_mem_nhds (by dsimp [c]; linarith [greenFunction_ball_pos hz.1 ha hza]))
  have hlt : -(t * c) < leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t a := by
    have := mul_pos ht hc
    linarith
  have hcont : ContinuousWithinAt (leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t)
      (ball (0 : ℂ) R \ {a}) a := (hv.1 a hac).mono subset_closure
  have hvnear := hcont.eventually (Ioi_mem_nhds hlt)
  filter_upwards [hG, hvnear, self_mem_nhdsWithin] with x hxG hxv hxU
  refine ⟨hxU, Or.inr ?_⟩
  nlinarith

/-- Under admissibility, an entire punctured neighbourhood of the removed
point lies in the cluster. -/
theorem exists_ball_sdiff_subset_clusterOn_punctured_disc_of_admissible
    {μ : Measure ℂ} {R t : ℝ} {z a : ℂ}
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a}) (ht : 0 < t)
    (hv : leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t ∈
      supersolutionsOn μ (ball (0 : ℂ) R \ {a}) z t) :
    ∃ ε > 0, ball a ε \ {a} ⊆ clusterOn μ (ball (0 : ℂ) R \ {a}) z t := by
  obtain ⟨δ, hδ, hδsub⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp (eventually_mem_clusterOn_punctured_disc_of_admissible ha hz ht hv))
  obtain ⟨η, hη, hηsub⟩ := Metric.isOpen_iff.mp isOpen_ball a ha
  refine ⟨min δ η, lt_min hδ hη, ?_⟩
  intro x hx
  exact hδsub (ball_subset_ball (min_le_left _ _) hx.1)
    ⟨hηsub (ball_subset_ball (min_le_right _ _) hx.1), hx.2⟩

/-- If the least supersolution is admissible, its cluster accumulates at the
removed point at every positive time. -/
theorem puncture_mem_closure_clusterOn_of_admissible
    {μ : Measure ℂ} {R t : ℝ} {z a : ℂ}
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a}) (ht : 0 < t)
    (hv : leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t ∈
      supersolutionsOn μ (ball (0 : ℂ) R \ {a}) z t) :
    a ∈ closure (clusterOn μ (ball (0 : ℂ) R \ {a}) z t) := by
  have hac : a ∈ closure (ball (0 : ℂ) R \ {a}) := by
    have h := (dense_compl_singleton a).open_subset_closure_inter isOpen_ball ha
    simpa [sdiff_eq, inter_comm] using h
  have haU : a ∉ ball (0 : ℂ) R \ {a} := by simp
  obtain ⟨c, hc, hG⟩ := frequently_green_pos_punctured_disc ha hz
  exact boundary_mem_closure_clusterOn_of_frequently_green_pos hz hac haU ht hc hv hG

/-- Compact containment of the punctured-disc cluster is incompatible with
admissibility of its least supersolution. -/
theorem not_admissible_punctured_disc_of_compact_containment
    {μ : Measure ℂ} {R t : ℝ} {z a : ℂ}
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a}) (ht : 0 < t)
    (hcl : closure (clusterOn μ (ball (0 : ℂ) R \ {a}) z t) ⊆
      ball (0 : ℂ) R \ {a}) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t ∉
      supersolutionsOn μ (ball (0 : ℂ) R \ {a}) z t := by
  intro hv
  have haU := hcl (puncture_mem_closure_clusterOn_of_admissible ha hz ht hv)
  simp at haU

end HarmonicBalls
