import HarmonicBalls.Proofs.Sec5.FinitePunctureGreen
import HarmonicBalls.Proofs.Sec5.PuncturedDiscCompetitors
import HarmonicBalls.Proofs.Sec5.PuncturedDiscRemovalReduction

/-! # Competitors for finitely punctured discs -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian

/-- Adding finitely many functions with nonpositive weak Laplacian preserves
an upper bound on the weak Laplacian. -/
theorem LaplacianLE.add_finset_of_nonpos {ι : Type*} (K : Finset ι)
    {w : ℂ → ℝ} {b : ι → ℂ → ℝ} {μ : Measure ℂ} {U : Set ℂ}
    (hw : LaplacianLE w μ U) (hb : ∀ a ∈ K, LaplacianLE (b a) 0 U) :
    LaplacianLE (fun x => w x + ∑ a ∈ K, b a x) μ U := by
  classical
  induction K using Finset.induction_on with
  | empty => simpa using hw
  | @insert a K ha ih =>
    have hk := ih (fun i hi => hb i (Finset.mem_insert_of_mem hi))
    have h := hk.add_of_nonpos (hb a (Finset.mem_insert_self a K))
    convert h using 1
    funext x
    simp only [Finset.sum_insert ha]
    ring

/-- Finite capped Green barriers turn a disc supersolution into a competitor
on the disc with the prescribed finite set removed. -/
theorem add_finset_cappedGreenBarrier_mem_supersolutionsOn
    {μ : Measure ℂ} {R t c : ℝ} {z : ℂ} {w : ℂ → ℝ} (K : Finset ℂ)
    (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ))
    (hw : w ∈ supersolutions μ R z t) (hc : 0 < c) :
    (fun x => w x + ∑ a ∈ K, cappedGreenBarrier R a c (|w a| + 1) x) ∈
      supersolutionsOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t := by
  classical
  have hcl : closure (ball (0 : ℂ) R \ (K : Set ℂ)) ⊆ closedBall (0 : ℂ) R :=
    closure_minimal (sdiff_subset.trans ball_subset_closedBall) isClosed_closedBall
  have hbar : ∀ x a, 0 ≤ cappedGreenBarrier R a c (|w a| + 1) x := by
    intro x a
    exact cappedGreenBarrier_nonneg hc.le (by positivity)
  have hsum : ∀ x, 0 ≤ ∑ a ∈ K, cappedGreenBarrier R a c (|w a| + 1) x :=
    fun x => Finset.sum_nonneg fun a _ => hbar x a
  refine ⟨(hw.1.mono hcl).add ((continuousOn_finsetSum K ?_).mono hcl), ?_, ?_⟩
  · exact fun a ha => continuousOn_cappedGreenBarrier (hK ha) hc
  · exact ((hw.2.1.add_finset_of_nonpos K
      (fun a ha => laplacianLE_cappedGreenBarrier (hK ha) hc)).mono_set sdiff_subset)
  · intro x hx hxz
    by_cases hxK : x ∈ K
    · have hxU : x ∉ ball (0 : ℂ) R \ (K : Set ℂ) := fun h => h.2 hxK
      rw [greenFunction_of_notMem_right hxU, mul_zero]
      have hs := Finset.single_le_sum (fun a _ => hbar x a) hxK
      have heq : cappedGreenBarrier R x c (|w x| + 1) x = |w x| + 1 := by
        simp [cappedGreenBarrier]
      rw [heq] at hs
      linarith [neg_abs_le (w x)]
    · by_cases hxU : x ∈ ball (0 : ℂ) R \ (K : Set ℂ)
      · rw [greenFunction_finset_punctured_ball K hK hz hxU hxz]
        linarith [hw.2.2 x (hcl hx) hxz, hsum x]
      · have hxb : x ∉ ball (0 : ℂ) R := fun hxb => hxU ⟨hxb, hxK⟩
        have h1 := hw.2.2 x (hcl hx) hxz
        rw [greenFunction_of_notMem_right hxb, mul_zero] at h1
        rw [greenFunction_of_notMem_right hxU, mul_zero]
        linarith [hsum x]

/-- Away from the removed set, the punctured-domain infimum is bounded above
by every disc supersolution. -/
theorem leastSupersolutionOn_finset_punctured_disc_le_supersolution
    {μ : Measure ℂ} {R t : ℝ} {z x : ℂ} {w : ℂ → ℝ} (K : Finset ℂ)
    (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ))
    (hw : w ∈ supersolutions μ R z t) (hx : x ∈ ball (0 : ℂ) R \ (K : Set ℂ))
    (hxz : x ≠ z) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t x ≤ w x := by
  classical
  have hlim : Tendsto
      (fun c : ℝ => w x + ∑ a ∈ K, cappedGreenBarrier R a c (|w a| + 1) x)
      (𝓝[>] 0) (𝓝 (w x)) := by
    have hs := tendsto_finsetSum K (fun a ha =>
      tendsto_cappedGreenBarrier_coefficient_zero (R := R)
        (show x ≠ a from fun h => hx.2 (h ▸ ha)) (show 0 ≤ |w a| + 1 by positivity))
    simpa using tendsto_const_nhds.add hs
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact leastSupersolutionOn_le_of_mem
    (add_finset_cappedGreenBarrier_mem_supersolutionsOn K hK hz hw hc)
    (subset_closure hx) hxz

/-- The least supersolutions agree away from the pole and the removed set. -/
theorem leastSupersolutionOn_finset_punctured_disc_eq
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z x : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Finset ℂ)
    (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ)) (ht : 0 < t)
    (hx : x ∈ ball (0 : ℂ) R \ (K : Set ℂ)) (hxz : x ≠ z) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t x =
      leastSupersolution μ R z t x := by
  obtain ⟨_, _, hw⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  exact le_antisymm
    (leastSupersolutionOn_finset_punctured_disc_le_supersolution K hK hz hw hx hxz)
    (leastSupersolution_le_finite_punctured_disc hμ hR hV ht.le K
      (ball_subset_closedBall hx.1) hxz)

/-- Removing finitely many interior points removes exactly those points from
the disc cluster. -/
theorem clusterOn_finset_punctured_disc_eq_sdiff
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Finset ℂ)
    (hK : (K : Set ℂ) ⊆ ball (0 : ℂ) R)
    (hz : z ∈ ball (0 : ℂ) R \ (K : Set ℂ)) (ht : 0 < t) :
    clusterOn μ (ball (0 : ℂ) R \ (K : Set ℂ)) z t = cluster μ R z t \ (K : Set ℂ) := by
  apply Subset.antisymm
  · intro x ⟨hx, h⟩
    refine ⟨⟨hx.1, ?_⟩, hx.2⟩
    rcases h with h | h
    · exact Or.inl h
    · by_cases hxz : x = z
      · exact Or.inl hxz
      · right
        rw [greenFunction_finset_punctured_ball K hK hz hx hxz,
          leastSupersolutionOn_finset_punctured_disc_eq hμ hR hV K hK hz ht hx hxz] at h
        exact h
  · exact disc_cluster_sdiff_subset_finite_punctured hμ hR hV ht.le K hK hz


end HarmonicBalls
