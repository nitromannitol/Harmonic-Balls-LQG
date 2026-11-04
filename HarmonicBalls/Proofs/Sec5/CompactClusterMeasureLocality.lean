import HarmonicBalls.Proofs.Sec5.GeneralDomainMeasureLocality
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility

/-! # Locality of compactly contained disc clusters

The disc obstacle is harmonic away from its pole. Hence, outside the closure
of the cluster, its least supersolution satisfies the Laplacian inequality for
any measure. This permits changes of measure outside a containing open set.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- A least supersolution remains admissible when the measure is changed
outside an open set containing the closure of its cluster. -/
theorem leastSupersolution_mem_supersolutions_of_restrict_eq
    {μ ν : Measure ℂ} {U : Set ℂ} {r t : ℝ} {z : ℂ}
    (hU : IsOpen U) (hsub : U ⊆ ball 0 r)
    (hμν : μ.restrict U = ν.restrict U) (hz : z ∈ ball 0 r)
    (hv : leastSupersolution μ r z t ∈ supersolutions μ r z t)
    (hcl : closure (cluster μ r z t) ⊆ U) :
    leastSupersolution μ r z t ∈ supersolutions ν r z t := by
  let O : Set ℂ := (closure (cluster μ r z t))ᶜ
  have hO : IsOpen O := isClosed_closure.isOpen_compl
  have hzO : z ∉ O := fun h => h (subset_closure (self_mem_cluster hz))
  have heq : ∀ x ∈ ball (0 : ℂ) r, x ∈ O →
      leastSupersolution μ r z t x = -t * greenFunction (ball 0 r) z x := by
    intro x hx hxO
    have hxz : x ≠ z := fun h => hzO (h ▸ hxO)
    have hnot : ¬ -t * greenFunction (ball 0 r) z x < leastSupersolution μ r z t x := by
      intro h
      exact hxO (subset_closure (show x ∈ cluster μ r z t from ⟨hx, Or.inr h⟩))
    exact le_antisymm (not_lt.mp hnot) (hv.2.2 x (ball_subset_closedBall hx) hxz)
  have hlocal : LaplacianLE (leastSupersolution μ r z t) ν U :=
    (laplacianLE_iff_of_restrict_eq hU.measurableSet hμν _).mp (hv.2.1.mono_set hsub)
  have hout : LaplacianLE (leastSupersolution μ r z t) ν (ball 0 r ∩ O) :=
    (laplacianLE_neg_mul_greenFunction_of_notMem (μ := ν) (t := t) hz inter_subset_left
      (fun h => hzO h.2)).congr_eqOn (measurableSet_ball.inter hO.measurableSet)
        (fun x hx => (heq x hx.1 hx.2).symm)
  have hunion : U ∪ (ball 0 r ∩ O) = ball (0 : ℂ) r := by
    apply subset_antisymm
    · exact union_subset hsub inter_subset_left
    · intro x hx
      by_cases hxU : x ∈ U
      · exact Or.inl hxU
      · exact Or.inr ⟨hx, fun hxcl => hxU (hcl hxcl)⟩
  exact ⟨hv.1, hunion ▸ LaplacianLE.union hU (isOpen_ball.inter hO) hlocal hout, hv.2.2⟩

/-- Changing the measure outside a containing open set cannot enlarge the
disc cluster, provided the original least supersolution is admissible. -/
theorem cluster_subset_of_restrict_eq_of_closure_subset
    {μ ν : Measure ℂ} {U : Set ℂ} {r t : ℝ} {z : ℂ}
    (hU : IsOpen U) (hsub : U ⊆ ball 0 r)
    (hμν : μ.restrict U = ν.restrict U) (hz : z ∈ ball 0 r)
    (hv : leastSupersolution μ r z t ∈ supersolutions μ r z t)
    (hcl : closure (cluster μ r z t) ⊆ U) :
    cluster ν r z t ⊆ cluster μ r z t := by
  have hw := leastSupersolution_mem_supersolutions_of_restrict_eq hU hsub hμν hz hv hcl
  intro x hx
  refine ⟨hx.1, ?_⟩
  rcases hx.2 with hxz | hp
  · exact Or.inl hxz
  · by_cases hxz : x = z
    · exact Or.inl hxz
    · exact Or.inr (lt_of_lt_of_le hp (leastSupersolution_le hw (ball_subset_closedBall hx.1) hxz))

/-- Compact containment makes the disc cluster depend only on the measure on
the containing open set, for admissible least supersolutions. -/
theorem cluster_eq_of_restrict_eq_of_closure_subset
    {μ ν : Measure ℂ} {U : Set ℂ} {r t : ℝ} {z : ℂ}
    (hU : IsOpen U) (hsub : U ⊆ ball 0 r)
    (hμν : μ.restrict U = ν.restrict U) (hz : z ∈ ball 0 r)
    (hμ : leastSupersolution μ r z t ∈ supersolutions μ r z t)
    (hν : leastSupersolution ν r z t ∈ supersolutions ν r z t)
    (hcl : closure (cluster μ r z t) ⊆ U) :
    cluster μ r z t = cluster ν r z t := by
  have hνμ := cluster_subset_of_restrict_eq_of_closure_subset hU hsub hμν hz hμ hcl
  have hclν : closure (cluster ν r z t) ⊆ U := (closure_mono hνμ).trans hcl
  exact subset_antisymm
    (cluster_subset_of_restrict_eq_of_closure_subset hU hsub hμν.symm hz hν hclν) hνμ

/-- The containing open set need not itself lie in the disc, provided the
cluster closure lies in both. -/
theorem cluster_eq_of_restrict_eq_of_closure_subset_inter
    {μ ν : Measure ℂ} {U : Set ℂ} {r t : ℝ} {z : ℂ}
    (hU : IsOpen U) (hμν : μ.restrict U = ν.restrict U)
    (hz : z ∈ ball 0 r)
    (hμ : leastSupersolution μ r z t ∈ supersolutions μ r z t)
    (hν : leastSupersolution ν r z t ∈ supersolutions ν r z t)
    (hclU : closure (cluster μ r z t) ⊆ U)
    (hclr : closure (cluster μ r z t) ⊆ ball 0 r) :
    cluster μ r z t = cluster ν r z t := by
  have hrestrict : μ.restrict (U ∩ ball 0 r) = ν.restrict (U ∩ ball 0 r) := by
    rw [inter_comm U (ball 0 r), ← Measure.restrict_restrict measurableSet_ball,
      ← Measure.restrict_restrict measurableSet_ball, hμν]
  exact cluster_eq_of_restrict_eq_of_closure_subset (hU.inter isOpen_ball)
    inter_subset_right hrestrict hz hμ hν (subset_inter hclU hclr)

/-- Local finiteness and volume growth supply the admissibility hypotheses in
the locality theorem. -/
theorem cluster_eq_of_restrict_eq_of_volumeGrowth
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {U : Set ℂ} {r t βm βp βm' βp' : ℝ} {z : ℂ}
    (hU : IsOpen U) (hμν : μ.restrict U = ν.restrict U)
    (hr : 0 < r) (hVμ : VolumeGrowth μ r βm βp) (hVν : VolumeGrowth ν r βm' βp')
    (hz : z ∈ ball 0 r) (ht : 0 < t)
    (hclU : closure (cluster μ r z t) ⊆ U)
    (hclr : closure (cluster μ r z t) ⊆ ball 0 r) :
    cluster μ r z t = cluster ν r z t := by
  obtain ⟨_, _, hvμ⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hr hVμ hz ht
  obtain ⟨_, _, hvν⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hν hr hVν hz ht
  exact cluster_eq_of_restrict_eq_of_closure_subset_inter hU hμν hz hvμ hvν hclU hclr

/-- Locally equal circle averages give the same compactly contained disc
cluster for the corresponding LQG limits. -/
theorem IsLQGLimit.cluster_eq_of_local_circle_averages_of_compact_containment
    {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {μ ν : Measure ℂ}
    (hμ : IsLQGLimit γ hε μ) (hν : IsLQGLimit γ hε' ν)
    {U : Set ℂ} (hU : IsOpen U)
    (hloc : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∀ᶠ k : ℕ in atTop, ∀ z ∈ K, hε (dyadicScale k) z = hε' (dyadicScale k) z)
    {r t : ℝ} {z : ℂ} (hz : z ∈ ball 0 r)
    (hvμ : leastSupersolution μ r z t ∈ supersolutions μ r z t)
    (hvν : leastSupersolution ν r z t ∈ supersolutions ν r z t)
    (hclU : closure (cluster μ r z t) ⊆ U)
    (hclr : closure (cluster μ r z t) ⊆ ball 0 r) :
    cluster μ r z t = cluster ν r z t :=
  cluster_eq_of_restrict_eq_of_closure_subset_inter hU (hμ.restrict_eq hν hU hloc)
    hz hvμ hvν hclU hclr

end HarmonicBalls
