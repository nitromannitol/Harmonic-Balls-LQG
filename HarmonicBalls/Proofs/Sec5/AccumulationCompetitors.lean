import HarmonicBalls.Proofs.Sec5.AccumulationBarrierCover
import HarmonicBalls.Proofs.Sec5.LocallyFinitePunctureCompetitors

/-! # Competitors for deletions with locally finite accumulation -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace

/-- Given invariance of the disc Green function, finite capped barrier covers
provide the reverse comparison away from the deletion and its accumulation
set. The Green identity remains an explicit hypothesis. -/
theorem leastSupersolutionOn_accumulating_punctured_disc_le_supersolution
    {μ : Measure ℂ} {R t : ℝ} {z x : ℂ} {w : ℂ → ℝ} {K L : Set ℂ}
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ L → (K ∩ C).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K) (hx : x ∈ ball (0 : ℂ) R \ K)
    (hxL : x ∉ L) (hxz : x ≠ z)
    (hgreen : ∀ y ∈ ball (0 : ℂ) R \ K, y ≠ z →
      greenFunction (ball (0 : ℂ) R \ K) z y = greenFunction (ball 0 R) z y)
    (hw : w ∈ supersolutions μ R z t) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t x ≤ w x := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  obtain ⟨ρ, hρ, htail⟩ := supersolution_lower_bound_near_sphere hz.1 hw hδ
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hw.1
  let M := max B 0
  have hM : 0 ≤ M := le_max_right B 0
  obtain ⟨J₁, J₂, c₁, c₂, hJ₁, hJ₂, hc₁, hc₂, hsmall, hcover⟩ :=
    exists_cappedGreenBarrier_cover_of_locally_finite_accumulation
      (C := closedBall (0 : ℂ) ρ) (isCompact_closedBall _ _) (closedBall_subset_ball hρ)
      hL hK hx.2 hxL hM hδ
  let b₁ : ℂ → ℝ := fun y => ∑ a ∈ J₁, cappedGreenBarrier R a c₁ (M + 1) y
  let b₂ : ℂ → ℝ := fun y => ∑ a ∈ J₂, cappedGreenBarrier R a c₂ (M + 1) y
  have hb₁ : ∀ y, 0 ≤ b₁ y := fun y => Finset.sum_nonneg fun a _ =>
    cappedGreenBarrier_nonneg hc₁.le (by linarith)
  have hb₂ : ∀ y, 0 ≤ b₂ y := fun y => Finset.sum_nonneg fun a _ =>
    cappedGreenBarrier_nonneg hc₂.le (by linarith)
  have hcl : closure (ball (0 : ℂ) R \ K) ⊆ closedBall (0 : ℂ) R :=
    closure_minimal (sdiff_subset.trans ball_subset_closedBall) isClosed_closedBall
  let v : ℂ → ℝ := fun y => (w y + δ + b₁ y) + b₂ y
  have hv : v ∈ supersolutionsOn μ (ball (0 : ℂ) R \ K) z t := by
    refine ⟨?_, ?_, ?_⟩
    · have hb₁c : ContinuousOn b₁ (closedBall (0 : ℂ) R) :=
        continuousOn_finsetSum J₁ (fun a ha => continuousOn_cappedGreenBarrier (hJ₁ ha) hc₁)
      have hb₂c : ContinuousOn b₂ (closedBall (0 : ℂ) R) :=
        continuousOn_finsetSum J₂ (fun a ha => continuousOn_cappedGreenBarrier (hJ₂ ha) hc₂)
      exact (((hw.1.add continuousOn_const).add hb₁c).add hb₂c).mono hcl
    · have hc := hasLaplacian_zero_of_harmonicOnNhd (U := ball (0 : ℂ) R) isOpen_ball
        (harmonicOnNhd_const (1 : ℝ))
      have hwδ : LaplacianLE (fun y => w y + δ) μ (ball (0 : ℂ) R) := by
        simpa only [mul_one] using hw.2.1.add_const_mul_of_hasLaplacian_zero hc δ
      have h₁ := hwδ.add_finset_of_nonpos J₁
        (b := fun a => cappedGreenBarrier R a c₁ (M + 1))
        (fun a ha => laplacianLE_cappedGreenBarrier (hJ₁ ha) hc₁)
      have h₂ := h₁.add_finset_of_nonpos J₂
        (b := fun a => cappedGreenBarrier R a c₂ (M + 1))
        (fun a ha => laplacianLE_cappedGreenBarrier (hJ₂ ha) hc₂)
      exact h₂.mono_set sdiff_subset
    · intro y hy hyz
      have hycl := hcl hy
      by_cases hyK : y ∈ K
      · have hynot : y ∉ ball (0 : ℂ) R \ K := fun h => h.2 hyK
        rw [greenFunction_of_notMem_right hynot, mul_zero]
        by_cases hyρ : y ∈ closedBall (0 : ℂ) ρ
        · have hcov := hcover y ⟨hyK, hyρ⟩
          have hbound : ‖w y‖ ≤ M := (hB y hycl).trans (le_max_left B 0)
          have habs : -‖w y‖ ≤ w y := by simpa only [Real.norm_eq_abs] using neg_abs_le (w y)
          dsimp [v, b₁, b₂]
          linarith
        · have hyρ' : ρ < ‖y‖ := by
            rw [mem_closedBall_zero_iff] at hyρ
            exact lt_of_not_ge hyρ
          dsimp [v]
          linarith [htail y hycl hyρ', hb₁ y, hb₂ y]
      · by_cases hyball : y ∈ ball (0 : ℂ) R
        · rw [hgreen y ⟨hyball, hyK⟩ hyz]
          dsimp [v]
          linarith [hw.2.2 y hycl hyz, hb₁ y, hb₂ y]
        · have hynot : y ∉ ball (0 : ℂ) R \ K := fun h => hyball h.1
          have hwbound := hw.2.2 y hycl hyz
          rw [greenFunction_of_notMem_right hyball, mul_zero] at hwbound
          rw [greenFunction_of_notMem_right hynot, mul_zero]
          dsimp [v]
          linarith [hb₁ y, hb₂ y]
  have hle := leastSupersolutionOn_le_of_mem hv (subset_closure hx) hxz
  dsimp [v, b₁, b₂, δ] at hle hsmall ⊢
  linarith

/-- The two least supersolutions agree away from the deletion, its possible
accumulation points and the pole, provided the Green functions agree there. -/
theorem leastSupersolutionOn_accumulating_punctured_disc_eq_of_green_eq
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z x : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {K L : Set ℂ}
    (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ L → (K ∩ C).Finite)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t)
    (hx : x ∈ ball (0 : ℂ) R \ K) (hxL : x ∉ L) (hxz : x ≠ z)
    (hgreen : ∀ y ∈ ball (0 : ℂ) R \ K, y ≠ z →
      greenFunction (ball (0 : ℂ) R \ K) z y = greenFunction (ball 0 R) z y) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t x = leastSupersolution μ R z t x := by
  obtain ⟨_, _, hw⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hR hV hz.1 ht
  exact le_antisymm
    (leastSupersolutionOn_accumulating_punctured_disc_le_supersolution
      hL hK hz hx hxL hxz hgreen hw)
    (leastSupersolution_le_accumulating_punctured_disc hμ hR hV ht.le hLclosed hL hK
      (ball_subset_closedBall hx.1) hxz)

#print axioms leastSupersolutionOn_accumulating_punctured_disc_eq_of_green_eq
#print axioms leastSupersolutionOn_accumulating_punctured_disc_le_supersolution

end HarmonicBalls
