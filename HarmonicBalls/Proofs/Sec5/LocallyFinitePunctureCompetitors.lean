import HarmonicBalls.Proofs.Sec5.LocallyFinitePointRemoval
import HarmonicBalls.Proofs.Sec5.FinitePunctureStrongCompatibility

/-! # Competitors after locally finite deletion -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace

/-- A full-disc supersolution is bounded below by an arbitrarily small
negative constant in an outer annulus. -/
theorem supersolution_lower_bound_near_sphere
    {μ : Measure ℂ} {R t δ : ℝ} {z : ℂ} {w : ℂ → ℝ}
    (hz : z ∈ ball (0 : ℂ) R)
    (hw : w ∈ supersolutions μ R z t) (hδ : 0 < δ) :
    ∃ ρ : ℝ, ρ < R ∧ ∀ x ∈ closedBall (0 : ℂ) R, ρ < ‖x‖ → -δ < w x := by
  let A : Set ℂ := closedBall (0 : ℂ) R ∩ w ⁻¹' Iic (-δ)
  have hAc : IsClosed A := hw.1.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_Iic
  have hAb : A ⊆ ball (0 : ℂ) R := by
    intro x hx
    by_contra hxb
    have hxz : x ≠ z := fun h => hxb (h ▸ hz)
    have hnonneg := hw.2.2 x hx.1 hxz
    rw [greenFunction_of_notMem_right hxb, mul_zero] at hnonneg
    have : w x ≤ -δ := hx.2
    linarith
  obtain ⟨ρ, hρ, hAρ⟩ := exists_lt_subset_ball hAc hAb
  refine ⟨ρ, hρ, ?_⟩
  intro x hx hρx
  by_contra h
  have hxA : x ∈ A := ⟨hx, le_of_not_gt h⟩
  have hxn : ‖x‖ < ρ := mem_ball_zero_iff.mp (hAρ hxA)
  linarith

/-- A small upward shift handles the outer punctures, while finitely many
capped Green barriers handle the punctures in an inner closed disc. -/
theorem add_shift_finset_barrier_mem_supersolutionsOn_locally_finite
    {μ : Measure ℂ} {R t c δ ρ : ℝ} {z : ℂ} {w : ℂ → ℝ} {K : Set ℂ}
    (hR : 0 < R)
    (hK : ∀ r : ℝ, r < R → (K ∩ closedBall (0 : ℂ) r).Finite)
    (hρ : ρ < R) (hz : z ∈ ball (0 : ℂ) R \ K)
    (hw : w ∈ supersolutions μ R z t) (hc : 0 < c) (hδ : 0 < δ)
    (htail : ∀ x ∈ closedBall (0 : ℂ) R, ρ < ‖x‖ → -δ < w x) :
    (fun x => (w x + δ) + ∑ a ∈ (hK ρ hρ).toFinset,
      cappedGreenBarrier R a c (|w a + δ| + 1) x) ∈
      supersolutionsOn μ (ball (0 : ℂ) R \ K) z t := by
  classical
  let J : Finset ℂ := (hK ρ hρ).toFinset
  have hJ : (J : Set ℂ) = K ∩ closedBall (0 : ℂ) ρ := Set.Finite.coe_toFinset _
  have hJK : (J : Set ℂ) ⊆ K := by rw [hJ]; exact inter_subset_left
  have hJR : (J : Set ℂ) ⊆ ball (0 : ℂ) R := by
    rw [hJ]
    exact inter_subset_right.trans (closedBall_subset_ball hρ)
  have hzJ : z ∈ ball (0 : ℂ) R \ (J : Set ℂ) := ⟨hz.1, fun h => hz.2 (hJK h)⟩
  have hshift : (fun x => w x + δ) ∈ supersolutions μ R z t := by
    refine ⟨hw.1.add continuousOn_const, ?_, ?_⟩
    · have hc1 := hasLaplacian_zero_of_harmonicOnNhd (U := ball (0 : ℂ) R) isOpen_ball
        (harmonicOnNhd_const (1 : ℝ))
      simpa only [mul_one] using hw.2.1.add_const_mul_of_hasLaplacian_zero hc1 δ
    · intro x hx hxz
      have := hw.2.2 x hx hxz
      linarith
  let v : ℂ → ℝ := fun x => (w x + δ) + ∑ a ∈ J,
    cappedGreenBarrier R a c (|w a + δ| + 1) x
  have hvJ : v ∈ supersolutionsOn μ (ball (0 : ℂ) R \ (J : Set ℂ)) z t :=
    add_finset_cappedGreenBarrier_mem_supersolutionsOn J hJR hzJ hshift hc
  have hclK := closure_sdiff_locally_finite_ball hR hK
  have hclJ := closure_sdiff_finset_of_isOpen (U := ball (0 : ℂ) R) isOpen_ball J
  rw [closure_ball (0 : ℂ) hR.ne'] at hclJ
  have hsub : ball (0 : ℂ) R \ K ⊆ ball (0 : ℂ) R \ (J : Set ℂ) :=
    fun _ hx => ⟨hx.1, fun h => hx.2 (hJK h)⟩
  change v ∈ supersolutionsOn μ (ball (0 : ℂ) R \ K) z t
  refine ⟨by rw [hclK, ← hclJ]; exact hvJ.1, hvJ.2.1.mono_set hsub, ?_⟩
  intro x hx hxz
  have hxball : x ∈ closedBall (0 : ℂ) R := hclK ▸ hx
  by_cases hxK : x ∈ K
  · have hxnot : x ∉ ball (0 : ℂ) R \ K := fun h => h.2 hxK
    rw [greenFunction_of_notMem_right hxnot, mul_zero]
    by_cases hxJ : x ∈ J
    · have hxnotJ : x ∉ ball (0 : ℂ) R \ (J : Set ℂ) := fun h => h.2 hxJ
      have hv := hvJ.2.2 x (hclJ.symm ▸ hxball) hxz
      rw [greenFunction_of_notMem_right hxnotJ, mul_zero] at hv
      exact hv
    · have hρx : ρ < ‖x‖ := by
        apply lt_of_not_ge
        intro hxρ
        apply hxJ
        change x ∈ (J : Set ℂ)
        rw [hJ]
        exact ⟨hxK, mem_closedBall_zero_iff.mpr hxρ⟩
      have hsum : 0 ≤ ∑ a ∈ J, cappedGreenBarrier R a c (|w a + δ| + 1) x :=
        Finset.sum_nonneg fun a _ => cappedGreenBarrier_nonneg hc.le (by positivity)
      dsimp [v]
      linarith [htail x hxball hρx]
  · by_cases hxb : x ∈ ball (0 : ℂ) R
    · have hxU : x ∈ ball (0 : ℂ) R \ K := ⟨hxb, hxK⟩
      have hxUJ : x ∈ ball (0 : ℂ) R \ (J : Set ℂ) := hsub hxU
      rw [greenFunction_locally_finite_punctured_ball K hK hz hxU hxz,
        ← greenFunction_finset_punctured_ball J hJR hzJ hxUJ hxz]
      exact hvJ.2.2 x (hclJ.symm ▸ hxball) hxz
    · have hxnot : x ∉ ball (0 : ℂ) R \ K := fun h => hxb h.1
      have hxnotJ : x ∉ ball (0 : ℂ) R \ (J : Set ℂ) := fun h => hxb h.1
      have hv := hvJ.2.2 x (hclJ.symm ▸ hxball) hxz
      rw [greenFunction_of_notMem_right hxnot, greenFunction_of_notMem_right hxnotJ, mul_zero] at *
      exact hv

/-- The least supersolution on a locally finitely punctured disc is bounded
above by every full-disc supersolution away from the pole and punctures. -/
theorem leastSupersolutionOn_locally_finite_punctured_disc_le_supersolution
    {μ : Measure ℂ} {R t : ℝ} {z x : ℂ} {w : ℂ → ℝ} {K : Set ℂ}
    (hR : 0 < R)
    (hK : ∀ r : ℝ, r < R → (K ∩ closedBall (0 : ℂ) r).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K) (hw : w ∈ supersolutions μ R z t)
    (hx : x ∈ ball (0 : ℂ) R \ K) (hxz : x ≠ z) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t x ≤ w x := by
  classical
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨ρ, hρ, htail⟩ := supersolution_lower_bound_near_sphere hz.1 hw hδ
  let J : Finset ℂ := (hK ρ hρ).toFinset
  have hJ : (J : Set ℂ) = K ∩ closedBall (0 : ℂ) ρ := Set.Finite.coe_toFinset _
  have hlim : Tendsto
      (fun c : ℝ => (w x + δ) + ∑ a ∈ J,
        cappedGreenBarrier R a c (|w a + δ| + 1) x)
      (𝓝[>] 0) (𝓝 (w x + δ)) := by
    have hs := tendsto_finsetSum J (fun a ha =>
      tendsto_cappedGreenBarrier_coefficient_zero (R := R)
        (show x ≠ a from fun h => hx.2 (by
          have ha' : a ∈ (J : Set ℂ) := ha
          rw [hJ] at ha'
          exact h ▸ ha'.1)) (show 0 ≤ |w a + δ| + 1 by positivity))
    simpa using tendsto_const_nhds.add hs
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact leastSupersolutionOn_le_of_mem
    (add_shift_finset_barrier_mem_supersolutionsOn_locally_finite
      hR hK hρ hz hw hc hδ htail) (subset_closure hx) hxz

/-- The two least supersolutions agree off the pole and the punctures. -/
theorem leastSupersolutionOn_locally_finite_punctured_disc_eq
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z x : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {K : Set ℂ}
    (hK : ∀ r : ℝ, r < R → (K ∩ closedBall (0 : ℂ) r).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (hx : x ∈ ball (0 : ℂ) R \ K) (hxz : x ≠ z) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t x = leastSupersolution μ R z t x := by
  obtain ⟨_, _, hw⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  exact le_antisymm
    (leastSupersolutionOn_locally_finite_punctured_disc_le_supersolution hR hK hz hw hx hxz)
    (leastSupersolution_le_locally_finite_punctured_disc hμ hR hV ht.le hK
      (ball_subset_closedBall hx.1) hxz)

/-- Locally finite point deletion removes precisely those points from a
full-disc cluster. -/
theorem clusterOn_locally_finite_punctured_disc_eq_sdiff
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {K : Set ℂ}
    (hK : ∀ r : ℝ, r < R → (K ∩ closedBall (0 : ℂ) r).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t) :
    clusterOn μ (ball (0 : ℂ) R \ K) z t = cluster μ R z t \ K := by
  apply Subset.antisymm _ (disc_cluster_sdiff_subset_locally_finite_punctured hμ hR hV ht.le hK hz)
  intro x hx
  refine ⟨⟨hx.1.1, ?_⟩, hx.1.2⟩
  rcases hx.2 with hxz | hxpos
  · exact Or.inl hxz
  · by_cases hxz : x = z
    · exact Or.inl hxz
    · refine Or.inr ?_
      rw [greenFunction_locally_finite_punctured_ball K hK hz hx.1 hxz,
        leastSupersolutionOn_locally_finite_punctured_disc_eq hμ hR hV hK hz ht hx.1 hxz] at hxpos
      exact hxpos

/-- Removing a locally finite set from an open subset of the disc preserves
its closure. -/
theorem closure_sdiff_locally_finite_of_isOpen {R : ℝ} {U K : Set ℂ}
    (hU : IsOpen U) (hUR : U ⊆ ball (0 : ℂ) R)
    (hK : ∀ r : ℝ, r < R → (K ∩ closedBall (0 : ℂ) r).Finite) :
    closure (U \ K) = closure U := by
  classical
  apply Subset.antisymm (closure_mono sdiff_subset)
  apply closure_minimal _ isClosed_closure
  intro x hx
  have hxR := mem_ball_zero_iff.mp (hUR hx)
  obtain ⟨ρ, hxρ, hρR⟩ := exists_between hxR
  let J : Finset ℂ := (hK ρ hρR).toFinset
  have hJ : (J : Set ℂ) = K ∩ closedBall (0 : ℂ) ρ := Set.Finite.coe_toFinset _
  have hd : Dense ((J : Set ℂ)ᶜ) := J.finite_toSet.countable.dense_compl ℂ
  have hxcl := hd.open_subset_closure_inter (hU.inter isOpen_ball)
    (show x ∈ U ∩ ball (0 : ℂ) ρ from ⟨hx, mem_ball_zero_iff.mpr hxρ⟩)
  apply closure_mono (show (U ∩ ball (0 : ℂ) ρ) ∩ (J : Set ℂ)ᶜ ⊆ U \ K from ?_) hxcl
  intro y hy
  refine ⟨hy.1.1, ?_⟩
  intro hyK
  apply hy.2
  rw [hJ]
  exact ⟨hyK, ball_subset_closedBall hy.1.2⟩

/-- Cluster closures agree after locally finite point deletion. -/
theorem closure_clusterOn_locally_finite_punctured_disc_eq
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {K : Set ℂ}
    (hK : ∀ r : ℝ, r < R → (K ∩ closedBall (0 : ℂ) r).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t) :
    closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) = closure (cluster μ R z t) := by
  rw [clusterOn_locally_finite_punctured_disc_eq_sdiff hμ hR hV hK hz ht]
  apply closure_sdiff_locally_finite_of_isOpen _ cluster_subset_ball hK
  rw [(obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z hz.1 t ht).2.2.1]
  exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds hμ hR hV hz.1 ht

/-- Strong compatibility holds for a locally finitely punctured disc under
either compact-containment alternative. -/
theorem regularizedFamily_strongCompatibility_locally_finite_punctured_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ R : ℝ, 0 < R → VolumeGrowth μ R βm βp)
    {R t : ℝ} {z : ℂ} (hR : 0 < R) {K : Set ℂ}
    (hK : ∀ r : ℝ, r < R → (K ∩ closedBall (0 : ℂ) r).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ ball (0 : ℂ) R \ K ∨
      closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) ⊆ ball 0 R \ K) :
    closure (Λ t) = closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) := by
  have hc := closure_clusterOn_locally_finite_punctured_disc_eq hμ hR (hV R hR) hK hz ht
  have hopen : ∀ r : ℝ, 0 < r → z ∈ ball (0 : ℂ) r → IsOpen (cluster μ r z t) := by
    intro r hr hzr
    rw [(obstacleCompatibilityShiftStep_holds μ hμ r βm βp hr (hV r hr) z hzr t ht).2.2.1]
    exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds
      hμ hr (hV r hr) hzr ht
  rcases hcl with hΛcl | hcl
  · have hΛR := hΛcl.trans sdiff_subset
    have heq := hΛ.2.2 t ht R hR hΛR R le_rfl
    rw [heq, closure_regularizedCluster_eq_of_isOpen (hopen R hR hz.1), hc]
  · have hdisc : closure (cluster μ R z t) ⊆ ball (0 : ℂ) R := by
      rw [← hc]
      exact hcl.trans sdiff_subset
    have hv := (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
      obstacleCompatibilityShiftStep_holds hμ hR (hV R hR) hz.1 ht).2.2
    rw [hc]
    exact regularizedFamily_closure_eq_discCluster_of_compact_containment
      hR hz.1 ht hΛ hopen hv hdisc

end HarmonicBalls
