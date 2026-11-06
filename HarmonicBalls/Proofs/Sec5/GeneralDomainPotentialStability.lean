import HarmonicBalls.Proofs.Sec5.PoleInfimumCharacterization
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility

/-! # General-domain stability under potential perturbations

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- Transfer a competitor using the difference of enclosing-disc potentials. -/
theorem supersolutionsOn_potential_transfer
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {R βm βp γm γp : ℝ} (hR : 0 < R)
    (hVμ : VolumeGrowth μ R βm βp) (hVν : VolumeGrowth ν R γm γp)
    {U : Set ℂ} (hsub : U ⊆ ball (0 : ℂ) R) {z : ℂ} {t ε : ℝ}
    (hpot : ∀ x ∈ closure U, greenPotentialBall ν R x ≤ greenPotentialBall μ R x + ε)
    {w : ℂ → ℝ} (hw : w ∈ supersolutionsOn μ U z t) :
    (fun x => w x + greenPotentialBall μ R x - greenPotentialBall ν R x + ε) ∈
      supersolutionsOn ν U z t := by
  obtain ⟨hcμ, hΔμ⟩ := enclosingDisc_potential_shift_on_domain hμ hR hVμ hsub
  obtain ⟨hcν, hΔν⟩ := enclosingDisc_potential_shift_on_domain hν hR hVν hsub
  refine ⟨((hw.1.add hcμ).sub hcν).add continuousOn_const, ?_, ?_⟩
  · apply (laplacianLE_iff_add_potential hν hΔν).mpr
    have hzero : HasLaplacian (fun _ : ℂ => (1 : ℝ)) 0 0 U :=
      hasLaplacian_zero_of_harmonicOnNhd (isOpen_univ) (InnerProductSpace.harmonicOnNhd_const 1) |>.mono_domain (subset_univ U)
    have h := ((laplacianLE_iff_add_potential hμ hΔμ).mp hw.2.1).add_const_mul_of_hasLaplacian_zero hzero ε
    convert h using 1
    ext x
    simp only [mul_one]
    ring
  · intro x hx hxz
    have h := hw.2.2 x hx hxz
    have hp := hpot x hx
    linarith

/-- The competitor infimum is stable on the entire closed domain, including the pole. -/
theorem abs_leastSupersolutionOn_sub_le_of_greenPotentialBall
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {R βm βp γm γp : ℝ} (hR : 0 < R)
    (hVμ : VolumeGrowth μ R βm βp) (hVν : VolumeGrowth ν R γm γp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t ε : ℝ} (ht : 0 ≤ t)
    (hpot : ∀ x ∈ closure U, |greenPotentialBall μ R x - greenPotentialBall ν R x| ≤ ε)
    {x : ℂ} (hx : x ∈ closure U) :
    |leastSupersolutionOn μ U z t x - leastSupersolutionOn ν U z t x| ≤ 2 * ε := by
  have glb : ∀ (ρ : Measure ℂ), IsLocallyFiniteMeasure ρ →
      ∀ a b, VolumeGrowth ρ R a b →
      IsGLB ((fun w : ℂ → ℝ => w x) '' supersolutionsOn ρ U z t)
        (leastSupersolutionOn ρ U z t x) := by
    intro ρ hρ a b hV
    by_cases hxz : x = z
    · subst x
      exact isGLB_supersolutionsOn_values_pole hρ hR hV hU hsub hz ht
    · exact isGLB_supersolutionsOn_values_of_ne_pole (isBounded_ball.subset hsub) ht hx hxz
  have hμg := glb μ hμ βm βp hVμ
  have hνg := glb ν hν γm γp hVν
  have h₁ : leastSupersolutionOn ν U z t x - 2 * ε ≤ leastSupersolutionOn μ U z t x := by
    apply hμg.2
    rintro _ ⟨w, hw, rfl⟩
    have hw' := supersolutionsOn_potential_transfer (ε := ε) hμ hν hR hVμ hVν hsub
      (fun y hy => by have h := (abs_le.mp (hpot y hy)).1; linarith) hw
    have h := hνg.1 ⟨_, hw', rfl⟩
    have hp := (abs_le.mp (hpot x hx)).2
    linarith
  have h₂ : leastSupersolutionOn μ U z t x - 2 * ε ≤ leastSupersolutionOn ν U z t x := by
    apply hνg.2
    rintro _ ⟨w, hw, rfl⟩
    have hw' := supersolutionsOn_potential_transfer (ε := ε) hν hμ hR hVν hVμ hsub
      (fun y hy => by have h := (abs_le.mp (hpot y hy)).2; linarith) hw
    have h := hμg.1 ⟨_, hw', rfl⟩
    have hp := (abs_le.mp (hpot x hx)).1
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The destination obstacle gap is at least the source gap minus twice the error. -/
theorem obstacle_gap_le_of_greenPotentialBall
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {R βm βp γm γp : ℝ} (hR : 0 < R)
    (hVμ : VolumeGrowth μ R βm βp) (hVν : VolumeGrowth ν R γm γp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t ε : ℝ} (ht : 0 ≤ t)
    (hpot : ∀ x ∈ closure U, |greenPotentialBall μ R x - greenPotentialBall ν R x| ≤ ε)
    {x : ℂ} (hx : x ∈ closure U) :
    leastSupersolutionOn μ U z t x - (-t * greenFunction U z x) - 2 * ε ≤
      leastSupersolutionOn ν U z t x - (-t * greenFunction U z x) := by
  have h := (abs_le.mp (abs_leastSupersolutionOn_sub_le_of_greenPotentialBall
    hμ hν hR hVμ hVν hU hsub hz ht hpot hx)).2
  linarith

/-- A gap larger than twice the potential error transfers directly to noncontact. -/
theorem mem_clusterOn_of_potential_gap
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) (hν : IsLocallyFiniteMeasure ν)
    {R βm βp γm γp : ℝ} (hR : 0 < R)
    (hVμ : VolumeGrowth μ R βm βp) (hVν : VolumeGrowth ν R γm γp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t ε : ℝ} (ht : 0 ≤ t)
    (hpot : ∀ x ∈ closure U, |greenPotentialBall μ R x - greenPotentialBall ν R x| ≤ ε)
    {x : ℂ} (hx : x ∈ U)
    (hgap : -t * greenFunction U z x + 2 * ε < leastSupersolutionOn μ U z t x) :
    x ∈ clusterOn ν U z t := by
  have h := obstacle_gap_le_of_greenPotentialBall
    hμ hν hR hVμ hVν hU hsub hz ht hpot (subset_closure hx)
  exact ⟨hx, Or.inr (by linarith)⟩

/-- Uniform convergence of potentials implies uniform convergence of actual infima. -/
theorem tendstoUniformlyOn_leastSupersolutionOn_of_potential
    {μ : ℕ → Measure ℂ} {ν : Measure ℂ}
    (hμ : ∀ n, IsLocallyFiniteMeasure (μ n)) (hν : IsLocallyFiniteMeasure ν)
    {R βm βp : ℝ} {γm γp : ℕ → ℝ} (hR : 0 < R)
    (hVμ : ∀ n, VolumeGrowth (μ n) R (γm n) (γp n))
    (hVν : VolumeGrowth ν R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t)
    (hpot : TendstoUniformlyOn (fun n => greenPotentialBall (μ n) R)
      (greenPotentialBall ν R) atTop (closure U)) :
    TendstoUniformlyOn (fun n => leastSupersolutionOn (μ n) U z t)
      (leastSupersolutionOn ν U z t) atTop (closure U) := by
  rw [Metric.tendstoUniformlyOn_iff] at hpot ⊢
  intro ε hε
  filter_upwards [hpot (ε / 4) (by positivity)] with n hn
  intro x hx
  have hbound : ∀ y ∈ closure U,
      |greenPotentialBall (μ n) R y - greenPotentialBall ν R y| ≤ ε / 4 := by
    intro y hy
    exact le_of_lt (by simpa only [Real.dist_eq, abs_sub_comm] using hn y hy)
  have h := abs_leastSupersolutionOn_sub_le_of_greenPotentialBall
    (hμ n) hν hR (hVμ n) hVν hU hsub hz ht hbound hx
  rw [Real.dist_eq, abs_sub_comm]
  linarith

#print axioms obstacle_gap_le_of_greenPotentialBall
#print axioms mem_clusterOn_of_potential_gap
#print axioms tendstoUniformlyOn_leastSupersolutionOn_of_potential

#print axioms supersolutionsOn_potential_transfer
#print axioms abs_leastSupersolutionOn_sub_le_of_greenPotentialBall

end HarmonicBalls
