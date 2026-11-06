import HarmonicBalls.Proofs.Sec5.GeneralDomainQuadrature
import HarmonicBalls.Proofs.Sec6.GeneralDomainStopped

/-! # General-domain cluster quadrature for Green kernels

The potential-theoretic infrastructure uses work of Leonardo Bonanno. -/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace
open scoped ENNReal

/-- The obstacle mass is dominated by the original measure: the open
cluster and its frontier are disjoint. -/
theorem general_clusterOn_obstacle_mass_le
    {μ ν : Measure ℂ} {U : Set ℂ} {z : ℂ} {t : ℝ}
    (hopen : IsOpen (clusterOn μ U z t)) (hν : ν ≤ μ) :
    μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t)) ≤ μ := by
  calc
    _ ≤ μ.restrict (clusterOn μ U z t) + μ.restrict (clusterOn μ U z t)ᶜ :=
      add_le_add le_rfl (Measure.restrict_mono (by
        intro x hx hxΛ
        exact (hopen.frontier_eq ▸ hx).2 hxΛ) hν)
    _ = μ := Measure.restrict_add_restrict_compl hopen.measurableSet

/-- The enclosing-disc Green kernel is integrable against the full obstacle
mass, including the frontier part and a pole on the frontier. -/
theorem integrable_greenFunction_ball_obstacle_mass
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hcl : closure (clusterOn μ U z t) ⊆ U) (hν : ν ≤ μ)
    {y : ℂ} (hy : y ∈ closedBall (0 : ℂ) R) :
    Integrable (fun x => greenFunction (ball (0 : ℂ) R) x y)
      (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t))) := by
  let _ : IsLocallyFiniteMeasure μ := hμ
  let Λ := clusterOn μ U z t
  let σ := μ.restrict Λ + ν.restrict (frontier Λ)
  have hΛo : IsOpen Λ := isOpen_clusterOn_of_volumeGrowth hμ hR hV hU hsub hz ht
  have hσ : σ ≤ μ := general_clusterOn_obstacle_mass_le hΛo hν
  have hmem : ∀ᵐ x ∂σ, x ∈ ball (0 : ℂ) R := by
    change ∀ᵐ x ∂(μ.restrict Λ + ν.restrict (frontier Λ)), x ∈ ball (0 : ℂ) R
    rw [ae_add_measure_iff]
    exact ⟨(ae_restrict_mem hΛo.measurableSet).mono
      (fun _ hx => hsub (hcl (subset_closure hx))),
      (ae_restrict_mem isClosed_frontier.measurableSet).mono
      (fun _ hx => hsub (hcl (frontier_subset_closure hx)))⟩
  have hs : σ.restrict (ball (0 : ℂ) R) = σ := Measure.restrict_eq_self_of_ae_mem hmem
  apply (integrable_greenFunction_ball_left hR hV hy).mono_measure
  change σ ≤ μ.restrict (ball (0 : ℂ) R)
  rw [← hs]
  exact Measure.restrict_mono subset_rfl hσ

/-- A finite source measure supported on a compact subset away from the pole
integrates the Green kernel at the pole. -/
theorem integrable_greenFunction_source_of_compact
    {O K : Set ℂ} (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    {z : ℂ} (hz : z ∈ O) (hK : IsCompact K) (hKO : K ⊆ O \ {z})
    {ρ : Measure ℂ} [IsFiniteMeasure ρ] (hρ : ρ Kᶜ = 0) :
    Integrable (greenFunction O z) ρ := by
  have hcont : ContinuousOn (greenFunction O z) K := by
    intro x hx
    exact ((Section6.harmonicOnNhd_greenFunction_right hO hOb hz x (hKO hx)).1.continuousAt).continuousWithinAt
  have hrestrict : ρ.restrict K = ρ := Measure.restrict_eq_self_of_ae_mem (by
    rw [ae_iff]
    change ρ Kᶜ = 0
    exact hρ)
  have hi := hcont.integrableOn_compact (μ := ρ) hK
  change Integrable (greenFunction O z) (ρ.restrict K) at hi
  rwa [hrestrict] at hi

/-- A Green kernel with pole outside the closed cluster satisfies quadrature
for the same obstacle mass as the distributional odometer equation. -/
theorem general_clusterOn_green_quadrature_away_closure
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hcl : closure (clusterOn μ U z t) ⊆ U)
    (hLap : HasLaplacian
      (fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x)
      (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t)))
      (ENNReal.ofReal t • Measure.dirac z) U)
    {O : Set ℂ} (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    (hΛO : closure (clusterOn μ U z t) ⊆ O)
    {y : ℂ} (hy : y ∈ O) (hyΛ : y ∉ closure (clusterOn μ U z t)) :
    Integrable (greenFunction O y)
      (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t))) ∧
    ∫ x, greenFunction O y x
      ∂(μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t))) =
        t * greenFunction O y z := by
  refine general_clusterOn_harmonic_quadrature_of_hasLaplacian hμ hR hV hU hsub hz ht hcl hLap
    (q := greenFunction O y) (hO.sdiff isClosed_singleton) ?_
    (Section6.harmonicOnNhd_greenFunction_right hO hOb hy)
  intro x hx
  exact ⟨hΛO hx, fun hxy => hyΛ (hxy ▸ hx)⟩

/-- A compactly contained cluster with null frontier is a harmonic ball for
the original measure. -/
theorem general_clusterOn_isHarmonicBall_of_frontier_null
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hcl : closure (clusterOn μ U z t) ⊆ U)
    (hfront : μ (frontier (clusterOn μ U z t)) = 0) :
    IsHarmonicBall μ (clusterOn μ U z t) z := by
  obtain ⟨hmass, hquad⟩ :=
    general_clusterOn_harmonic_quadrature_of_frontier_null hμ hR hV hU hsub hz ht hcl hfront
  refine ⟨isOpen_clusterOn_of_volumeGrowth hμ hR hV hU hsub hz ht, ⟨hz, Or.inl rfl⟩, ?_, ?_, ?_⟩
  · rw [hmass]; exact ENNReal.ofReal_pos.mpr ht
  · rw [hmass]; exact ENNReal.ofReal_lt_top
  · intro q hq
    obtain ⟨hi, he⟩ := hquad {x | HarmonicAt q x} q (isOpen_setOfPred_harmonicAt q) hq (fun _ hx => hx)
    refine ⟨hi, ?_⟩
    rw [measureReal_def, hmass, ENNReal.toReal_ofReal ht.le, he]
    ring

#print axioms integrable_greenFunction_source_of_compact
#print axioms integrable_greenFunction_ball_obstacle_mass
#print axioms general_clusterOn_obstacle_mass_le
#print axioms general_clusterOn_green_quadrature_away_closure
#print axioms general_clusterOn_isHarmonicBall_of_frontier_null

end HarmonicBalls
