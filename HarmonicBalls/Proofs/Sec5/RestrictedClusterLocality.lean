import HarmonicBalls.Proofs.Sec5.CompactClusterMeasureLocality

/-! # Locality under restriction of the measure

A smaller measure enlarges the disc cluster. Combined with the local transfer
of a least supersolution, this gives equality when the discarded measure is
outside the closure of the cluster, without regularity of the restricted measure.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- A distributional upper bound remains valid for a larger measure. -/
theorem LaplacianLE.mono_measure {w : ℂ → ℝ} {μ ν : Measure ℂ} {U : Set ℂ}
    (h : LaplacianLE w μ U) (hμν : μ ≤ ν) : LaplacianLE w ν U := by
  refine ⟨h.1, fun φ hφ hφ0 hint => ?_⟩
  exact (h.2 φ hφ hφ0 (hint.mono_measure hμν)).trans
    (integral_mono_measure hμν (Filter.Eventually.of_forall hφ0) hint)

/-- Increasing the measure enlarges the set of supersolutions. -/
theorem supersolutions_mono_measure {μ ν : Measure ℂ} {r t : ℝ} {z : ℂ}
    (hμν : μ ≤ ν) : supersolutions μ r z t ⊆ supersolutions ν r z t := by
  intro w hw
  exact ⟨hw.1, hw.2.1.mono_measure hμν, hw.2.2⟩

/-- Off the pole, increasing the measure decreases the least supersolution. -/
theorem leastSupersolution_antitone_measure {μ ν : Measure ℂ} {r t : ℝ} {z x : ℂ}
    (hμν : μ ≤ ν) (ht : 0 ≤ t) (hx : x ∈ closedBall (0 : ℂ) r) (hxz : x ≠ z) :
    leastSupersolution ν r z t x ≤ leastSupersolution μ r z t x := by
  apply le_csInf ((supersolutions_nonempty μ r z ht).image _)
  rintro _ ⟨w, hw, rfl⟩
  exact leastSupersolution_le (supersolutions_mono_measure hμν hw) hx hxz

/-- Increasing the measure decreases the cluster. -/
theorem cluster_antitone_measure {μ ν : Measure ℂ} {r t : ℝ} {z : ℂ}
    (hμν : μ ≤ ν) (ht : 0 ≤ t) : cluster ν r z t ⊆ cluster μ r z t := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  rcases hx.2 with hxz | hp
  · exact Or.inl hxz
  · by_cases hxz : x = z
    · exact Or.inl hxz
    · exact Or.inr (lt_of_lt_of_le hp
        (leastSupersolution_antitone_measure hμν ht (ball_subset_closedBall hx.1) hxz))

/-- Removing measure outside an open set containing the cluster closure leaves
its least supersolution unchanged off the pole. -/
theorem leastSupersolution_eq_of_le_of_restrict_eq_of_closure_subset
    {μ ν : Measure ℂ} {U : Set ℂ} {r t : ℝ} {z x : ℂ}
    (hU : IsOpen U) (hsub : U ⊆ ball 0 r) (hνμ : ν ≤ μ)
    (hμν : μ.restrict U = ν.restrict U) (hz : z ∈ ball 0 r)
    (ht : 0 ≤ t) (hv : leastSupersolution μ r z t ∈ supersolutions μ r z t)
    (hcl : closure (cluster μ r z t) ⊆ U)
    (hx : x ∈ closedBall (0 : ℂ) r) (hxz : x ≠ z) :
    leastSupersolution ν r z t x = leastSupersolution μ r z t x := by
  apply le_antisymm
  · exact leastSupersolution_le
      (leastSupersolution_mem_supersolutions_of_restrict_eq hU hsub hμν hz hv hcl) hx hxz
  · exact leastSupersolution_antitone_measure hνμ ht hx hxz

/-- Removing measure outside an open set containing the cluster closure leaves
the cluster unchanged. -/
theorem cluster_eq_of_le_of_restrict_eq_of_closure_subset
    {μ ν : Measure ℂ} {U : Set ℂ} {r t : ℝ} {z : ℂ}
    (hU : IsOpen U) (hsub : U ⊆ ball 0 r) (hνμ : ν ≤ μ)
    (hμν : μ.restrict U = ν.restrict U) (hz : z ∈ ball 0 r)
    (ht : 0 ≤ t) (hv : leastSupersolution μ r z t ∈ supersolutions μ r z t)
    (hcl : closure (cluster μ r z t) ⊆ U) :
    cluster μ r z t = cluster ν r z t := by
  exact subset_antisymm (cluster_antitone_measure hνμ ht)
    (cluster_subset_of_restrict_eq_of_closure_subset hU hsub hμν hz hv hcl)

/-- Restricting the measure to an open set containing the cluster closure does
not change the cluster, provided the closure is also contained in the disc. -/
theorem cluster_restrict_eq_of_closure_subset
    {μ : Measure ℂ} {U : Set ℂ} {r t : ℝ} {z : ℂ}
    (hU : IsOpen U) (hz : z ∈ ball 0 r) (ht : 0 ≤ t)
    (hv : leastSupersolution μ r z t ∈ supersolutions μ r z t)
    (hclU : closure (cluster μ r z t) ⊆ U)
    (hclr : closure (cluster μ r z t) ⊆ ball 0 r) :
    cluster μ r z t = cluster (μ.restrict U) r z t := by
  have hrestrict : μ.restrict (U ∩ ball 0 r) =
      (μ.restrict U).restrict (U ∩ ball 0 r) := by
    rw [Measure.restrict_restrict (hU.inter isOpen_ball).measurableSet,
      inter_eq_left.mpr inter_subset_left]
  exact cluster_eq_of_le_of_restrict_eq_of_closure_subset (hU.inter isOpen_ball)
    inter_subset_right Measure.restrict_le_self hrestrict hz ht hv (subset_inter hclU hclr)

/-- Volume growth supplies the original least-supersolution admissibility;
no volume-growth hypothesis is needed for the restricted measure. -/
theorem cluster_restrict_eq_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {U : Set ℂ} {r t βm βp : ℝ} {z : ℂ}
    (hU : IsOpen U) (hr : 0 < r) (hV : VolumeGrowth μ r βm βp)
    (hz : z ∈ ball 0 r) (ht : 0 < t)
    (hclU : closure (cluster μ r z t) ⊆ U)
    (hclr : closure (cluster μ r z t) ⊆ ball 0 r) :
    cluster μ r z t = cluster (μ.restrict U) r z t := by
  obtain ⟨_, _, hv⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hr hV hz ht
  exact cluster_restrict_eq_of_closure_subset hU hz ht.le hv hclU hclr

end HarmonicBalls
