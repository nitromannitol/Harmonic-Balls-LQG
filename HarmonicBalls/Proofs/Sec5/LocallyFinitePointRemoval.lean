import HarmonicBalls.Proofs.Sec5.FinitePointRemoval
import HarmonicBalls.Proofs.Sec5.LocallyFinitePunctureGreen

/-! # Removal of locally finite point sets for continuous supersolutions -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Laplacian

/-- A continuous weak supersolution extends across a set meeting each compact
subset of the open domain in finitely many points. -/
theorem laplacianLE_zero_of_locally_finite_removal {U K : Set ℂ} (hU : IsOpen U)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ U → (K ∩ C).Finite)
    {w : ℂ → ℝ} (hwc : ContinuousOn w U) (hw : LaplacianLE w 0 (U \ K)) :
    LaplacianLE w 0 U := by
  classical
  refine ⟨hwc.locallyIntegrableOn hU.measurableSet, ?_⟩
  intro φ hφ hφ0 hφμ
  obtain ⟨V, hVo, hφV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hφ.2.1 hU hφ.2.2
  let J : Finset ℂ := (hK (closure V) hVc hVU).toFinset
  have hJ : (J : Set ℂ) = K ∩ closure V := Set.Finite.coe_toFinset _
  have hsub : V \ (J : Set ℂ) ⊆ U \ K := by
    intro x hx
    refine ⟨hVU (subset_closure hx.1), ?_⟩
    intro hxK
    apply hx.2
    rw [hJ]
    exact ⟨hxK, subset_closure hx.1⟩
  have hlocal : LaplacianLE w 0 V :=
    laplacianLE_zero_of_finite_removal hVo (hwc.mono (subset_closure.trans hVU)) J
      (hw.mono_set hsub)
  exact hlocal.2 φ ⟨hφ.1, hφ.2.1, hφV⟩ hφ0 hφμ

/-- The same removal principle holds for a measure-valued weak Laplacian
when the measure has a continuous potential on the domain. -/
theorem laplacianLE_of_locally_finite_removal {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {U K : Set ℂ} (hU : IsOpen U)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ U → (K ∩ C).Finite)
    {w q : ℂ → ℝ} (hwc : ContinuousOn w U) (hqc : ContinuousOn q U)
    (hq : HasLaplacian q 0 μ U) (hw : LaplacianLE w μ (U \ K)) : LaplacianLE w μ U := by
  have hp := (laplacianLE_iff_add_potential hμ (hq.mono_domain sdiff_subset)).mp hw
  exact (laplacianLE_iff_add_potential hμ hq).mpr
    (laplacianLE_zero_of_locally_finite_removal hU hK (hwc.add hqc) hp)

/-- For a disc, local volume growth supplies the continuous potential needed
for removal of a locally finite set. -/
theorem laplacianLE_disc_of_locally_finite_removal {μ : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {K : Set ℂ}
    (hK : ∀ ρ : ℝ, ρ < R → (K ∩ closedBall (0 : ℂ) ρ).Finite)
    {w : ℂ → ℝ} (hwc : ContinuousOn w (ball (0 : ℂ) R))
    (hw : LaplacianLE w μ (ball (0 : ℂ) R \ K)) : LaplacianLE w μ (ball 0 R) := by
  apply laplacianLE_of_locally_finite_removal hμ isOpen_ball _ hwc
    ((greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV).mono ball_subset_closedBall)
    (greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR hV) hw
  intro C hC hCU
  obtain ⟨ρ, hρ, hCρ⟩ := exists_lt_subset_ball hC.isClosed hCU
  exact (hK ρ hρ).subset (inter_subset_inter_right K (hCρ.trans ball_subset_closedBall))

/-- Deleting a set locally finite in a disc leaves the closure of the disc
unchanged. -/
theorem closure_sdiff_locally_finite_ball {R : ℝ} (hR : 0 < R) {K : Set ℂ}
    (hK : ∀ ρ : ℝ, ρ < R → (K ∩ closedBall (0 : ℂ) ρ).Finite) :
    closure (ball (0 : ℂ) R \ K) = closedBall 0 R := by
  apply Subset.antisymm (closure_minimal (sdiff_subset.trans ball_subset_closedBall) isClosed_closedBall)
  rw [← closure_ball (0 : ℂ) hR.ne']
  apply closure_minimal _ isClosed_closure
  intro x hx
  have hnorm : ‖x‖ < R := mem_ball_zero_iff.mp hx
  obtain ⟨ρ, hxρ, hρR⟩ := exists_between hnorm
  let J : Finset ℂ := (hK ρ hρR).toFinset
  have hJ : (J : Set ℂ) = K ∩ closedBall (0 : ℂ) ρ := Set.Finite.coe_toFinset _
  have hd : Dense ((J : Set ℂ)ᶜ) := J.finite_toSet.countable.dense_compl ℂ
  have hxcl := hd.open_subset_closure_inter isOpen_ball (mem_ball_zero_iff.mpr hxρ)
  apply closure_mono (show ball (0 : ℂ) ρ ∩ (J : Set ℂ)ᶜ ⊆ ball (0 : ℂ) R \ K from ?_) hxcl
  intro y hy
  refine ⟨ball_subset_ball hρR.le hy.1, ?_⟩
  intro hyK
  apply hy.2
  rw [hJ]
  exact ⟨hyK, ball_subset_closedBall hy.1⟩

/-- A supersolution on a disc minus a locally finite set is a supersolution
on the full disc. -/
theorem locally_finite_punctured_disc_supersolution_mem_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (ht : 0 ≤ t)
    {K : Set ℂ} (hK : ∀ ρ : ℝ, ρ < R → (K ∩ closedBall (0 : ℂ) ρ).Finite)
    {z : ℂ} {w : ℂ → ℝ}
    (hw : w ∈ supersolutionsOn μ (ball (0 : ℂ) R \ K) z t) :
    w ∈ supersolutions μ R z t := by
  have hcl := closure_sdiff_locally_finite_ball hR hK
  refine ⟨by simpa only [hcl] using hw.1, ?_, ?_⟩
  · exact laplacianLE_disc_of_locally_finite_removal hμ hR hV hK
      (hw.1.mono (by rw [hcl]; exact ball_subset_closedBall)) hw.2.1
  · intro x hx hxz
    have hwx := hw.2.2 x (hcl ▸ hx) hxz
    have hG := Section6.greenFunction_le_of_subset
      (show ball (0 : ℂ) R \ K ⊆ ball 0 R from sdiff_subset) isBounded_ball z x
    nlinarith

/-- The full-disc least supersolution bounds the infimum on a locally
finitely punctured disc from below. -/
theorem leastSupersolution_le_locally_finite_punctured_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (ht : 0 ≤ t)
    {K : Set ℂ} (hK : ∀ ρ : ℝ, ρ < R → (K ∩ closedBall (0 : ℂ) ρ).Finite)
    {z x : ℂ} (hx : x ∈ closedBall (0 : ℂ) R) (hxz : x ≠ z) :
    leastSupersolution μ R z t x ≤ leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t x := by
  apply le_csInf
  · exact ⟨_, ⟨0, zero_mem_supersolutionsOn (isBounded_ball.subset sdiff_subset) ht, rfl⟩⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact leastSupersolution_le
      (locally_finite_punctured_disc_supersolution_mem_disc hμ hR hV ht hK hw) hx hxz

/-- Removing a locally finite set from the disc removes at most those points
from its cluster, as far as the inclusion from the original cluster goes. -/
theorem disc_cluster_sdiff_subset_locally_finite_punctured
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (ht : 0 ≤ t)
    {K : Set ℂ} (hK : ∀ ρ : ℝ, ρ < R → (K ∩ closedBall (0 : ℂ) ρ).Finite)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R \ K) :
    cluster μ R z t \ K ⊆ clusterOn μ (ball (0 : ℂ) R \ K) z t := by
  intro x ⟨⟨hxb, hxcluster⟩, hxK⟩
  have hx : x ∈ ball (0 : ℂ) R \ K := ⟨hxb, hxK⟩
  rcases hxcluster with hxz | hxcluster
  · exact ⟨hx, Or.inl hxz⟩
  · by_cases hxz : x = z
    · exact ⟨hx, Or.inl hxz⟩
    · refine ⟨hx, Or.inr ?_⟩
      have hle := leastSupersolution_le_locally_finite_punctured_disc hμ hR hV ht hK
        (ball_subset_closedBall hxb) hxz
      have hG := greenFunction_locally_finite_punctured_ball K hK hz hx hxz
      rw [hG]
      linarith

#print axioms laplacianLE_zero_of_locally_finite_removal
#print axioms laplacianLE_of_locally_finite_removal
#print axioms laplacianLE_disc_of_locally_finite_removal
#print axioms closure_sdiff_locally_finite_ball
#print axioms locally_finite_punctured_disc_supersolution_mem_disc
#print axioms leastSupersolution_le_locally_finite_punctured_disc
#print axioms disc_cluster_sdiff_subset_locally_finite_punctured

end HarmonicBalls
