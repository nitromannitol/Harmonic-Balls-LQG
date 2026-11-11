import HarmonicBalls.Proofs.Sec5.GeneralDomainQuadrature
import HarmonicBalls.Proofs.Sec4.GreenRepresentation
import HarmonicBalls.Proofs.Sec4.ClusterGreenIdentity
import HarmonicBalls.Proofs.Sec6.GeneralDomainStopped

/-! # General-domain cluster quadrature for Green kernels

The potential-theoretic infrastructure uses work of Leonardo Bonanno. -/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace Filter Laplacian ComplexConjugate
open scoped Topology
open scoped ENNReal

/-- A compactly supported distributional Laplacian extends by zero from an
open set to the plane. Both source measures must be concentrated on the same
compact set. -/
theorem HasLaplacian.extend_by_zero_of_compact
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {f : ℂ → ℝ} {α β : Measure ℂ} (hf : HasLaplacian f α β U)
    (hfzero : ∀ x ∈ U, x ∉ K → f x = 0)
    (hα : α Kᶜ = 0) (hβ : β Kᶜ = 0) :
    HasLaplacian (U.indicator f) α β Set.univ := by
  classical
  let g := U.indicator f
  have hgK : ∀ x ∉ K, g x = 0 := by
    intro x hx
    by_cases hxU : x ∈ U
    · simpa [g, hxU] using hfzero x hxU hx
    · simp [g, hxU]
  have hgU : EqOn f g U := fun x hx => (indicator_of_mem hx f).symm
  have hgiK : IntegrableOn g K := by
    have hi := hf.1.integrableOn_compact_subset hKU hK
    exact hi.congr_fun (fun x hx => hgU (hKU hx)) hK.measurableSet
  have hgi : Integrable g := (integrableOn_iff_integrable_of_support_subset (by
    intro x hx
    by_contra hn
    exact hx (hgK x hn))).mp hgiK
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨χ, hχd, hχc, hχU, -, hχ1⟩ :=
    exists_cutoff_of_isCompact_subset_isOpen hK.cthickening hU hδU
  have hχnear : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, χ y = 1 := by
    intro x hx
    filter_upwards [isOpen_thickening.mem_nhds (self_subset_thickening hδ _ hx)] with y hy
    exact hχ1 y (thickening_subset_cthickening _ _ hy)
  have haeα : ∀ᵐ x ∂α, x ∈ K := by rw [ae_iff]; exact hα
  have haeβ : ∀ᵐ x ∂β, x ∈ K := by rw [ae_iff]; exact hβ
  refine ⟨hgi.locallyIntegrable.locallyIntegrableOn _, fun φ hφ => ?_⟩
  let ψ : ℂ → ℝ := fun x => φ x * χ x
  have hψ : IsTestFunction U ψ :=
    ⟨hφ.1.mul hχd, hχc.of_isClosed_subset (isClosed_tsupport _) tsupport_mul_subset_right,
      tsupport_mul_subset_right.trans hχU⟩
  obtain ⟨hiα, hiβ, he⟩ := hf.2 ψ hψ
  have hψφ : ∀ x ∈ K, ψ x = φ x := by
    intro x hx
    simp [ψ, (hχnear x hx).self_of_nhds]
  have hΔ : ∀ x ∈ K, Δ ψ x = Δ φ x := by
    intro x hx
    apply (laplacian_congr_nhds ?_).self_of_nhds
    filter_upwards [hχnear x hx] with y hy
    simp [ψ, hy]
  have heqα : ψ =ᵐ[α] φ := haeα.mono (fun x hx => hψφ x hx)
  have heqβ : ψ =ᵐ[β] φ := haeβ.mono (fun x hx => hψφ x hx)
  refine ⟨hiα.congr heqα, hiβ.congr heqβ, ?_⟩
  have heq : (fun x => g x * Δ φ x) = (fun x => f x * Δ ψ x) := by
    funext x
    by_cases hx : x ∈ K
    · rw [← hgU (hKU hx), hΔ x hx]
    · rw [hgK x hx, zero_mul]
      by_cases hxU : x ∈ U
      · rw [hfzero x hxU hx, zero_mul]
      · rw [laplacian_eq_zero_of_notMem_tsupport (fun h => hxU (hψ.2.2 h)), mul_zero]
  rw [heq, he, integral_congr_ae heqα, integral_congr_ae heqβ]

/-- The compactly contained odometer satisfies its distributional equation
on the whole plane after extension by zero. -/
theorem general_odometer_zero_extended_hasLaplacian
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hcl : closure (clusterOn μ U z t) ⊆ U)
    (hLap : HasLaplacian
      (fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x)
      (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t)))
      (ENNReal.ofReal t • Measure.dirac z) U) :
    HasLaplacian
      (U.indicator (fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x))
      (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t)))
      (ENNReal.ofReal t • Measure.dirac z) univ := by
  let Λ := clusterOn μ U z t
  have hΛo : IsOpen Λ := isOpen_clusterOn_of_volumeGrowth hμ hR hV hU hsub hz ht
  have hK : IsCompact (closure Λ) :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset isClosed_closure
      (hcl.trans (hsub.trans ball_subset_closedBall))
  refine HasLaplacian.extend_by_zero_of_compact hU hK hcl hLap ?_ ?_ ?_
  · intro x hxU hxK
    exact general_odometer_eq_zero_of_notMem_clusterOn hsub ht.le
      ⟨hxU, fun hxΛ => hxK (subset_closure hxΛ)⟩
  · have hae : ∀ᵐ x ∂(μ.restrict Λ + ν.restrict (frontier Λ)), x ∈ closure Λ := by
      rw [ae_add_measure_iff]
      exact ⟨(ae_restrict_mem hΛo.measurableSet).mono (fun _ hx => subset_closure hx),
        (ae_restrict_mem isClosed_frontier.measurableSet).mono
          (fun _ hx => frontier_subset_closure hx)⟩
    rw [ae_iff] at hae
    exact hae
  · have hzK : z ∈ closure Λ := subset_closure ⟨hz, Or.inl rfl⟩
    simp [Measure.smul_apply, Measure.dirac_apply, hzK]

/-- Distributional Laplacians are unchanged by changing a function on a
volume-null set. -/
theorem HasLaplacian.congr_ae_volume
    {U : Set ℂ} {f g : ℂ → ℝ} {α β : Measure ℂ}
    (hf : HasLaplacian f α β U) (hfg : f =ᵐ[volume] g) :
    HasLaplacian g α β U := by
  refine ⟨hf.1.congr (ae_restrict_of_ae hfg), fun φ hφ => ?_⟩
  obtain ⟨hα, hβ, he⟩ := hf.2 φ hφ
  refine ⟨hα, hβ, ?_⟩
  have heq : (fun x => f x * Δ φ x) =ᵐ[volume] fun x => g x * Δ φ x := by
    filter_upwards [hfg] with x hx
    rw [hx]
  rw [← integral_congr_ae heq, he]

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

/-- The zero-extended general-domain odometer has the enclosing-disc Green
representation at every point away from its pole. -/
theorem general_odometer_enclosingDisc_green_representation
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hcl : closure (clusterOn μ U z t) ⊆ U) (hν : ν ≤ μ)
    (hLap : HasLaplacian
      (fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x)
      (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t)))
      (ENNReal.ofReal t • Measure.dirac z) U)
    {y : ℂ} (hy : y ∈ ball (0 : ℂ) R) (hyz : y ≠ z) :
    ∫ x, greenFunction (ball (0 : ℂ) R) y x
      ∂(μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t))) =
      t * greenFunction (ball (0 : ℂ) R) z y -
        U.indicator (fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x) y := by
  classical
  let Λ := clusterOn μ U z t
  let σ := μ.restrict Λ + ν.restrict (frontier Λ)
  let g := U.indicator (fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x)
  let G := greenFunction (ball (0 : ℂ) R) z
  obtain ⟨h, hh, hG⟩ := exists_harmonicOnNhd_greenFunction_difference hU
    (isBounded_ball.subset hsub) hsub hz
  let w : ℂ → ℝ := fun x => if x ∈ U then leastSupersolutionOn μ U z t x + t * h x else -t * G x
  have hΛo : IsOpen Λ := isOpen_clusterOn_of_volumeGrowth hμ hR hV hU hsub hz ht
  have hzK : z ∈ closure Λ := subset_closure ⟨hz, Or.inl rfl⟩
  have hgzero : ∀ x ∉ closure Λ, g x = 0 := by
    intro x hx
    by_cases hxU : x ∈ U
    · simp only [g, indicator_of_mem hxU]
      exact general_odometer_eq_zero_of_notMem_clusterOn hsub ht.le
        ⟨hxU, fun hΛ => hx (subset_closure hΛ)⟩
    · simp [g, hxU]
  have hw_eq : ∀ x, x ≠ z → w x = g x - t * G x := by
    intro x hxz
    by_cases hxU : x ∈ U
    · simp only [w, hxU, ↓reduceIte, g, indicator_of_mem hxU, G]
      have he := hG x hxU hxz
      rw [← he]
      ring
    · simp [w, g, hxU, G]
  have hwc : Continuous w := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hxU : x ∈ U
    · have hc := ((general_domain_interior_infimum_regularity hμ hR hV hU hsub hz ht).1.continuousAt
        (hU.mem_nhds hxU)).add (((hh x hxU).1.continuousAt).const_mul t)
      apply hc.congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hxU] with y hy
      simp [w, hy]
    · have hxK : x ∉ closure Λ := fun h => hxU (hcl h)
      have hxz : x ≠ z := fun e => hxU (e ▸ hz)
      have hc := ((continuousOn_greenFunction_ball (hsub hz)).continuousAt
        (isOpen_compl_singleton.mem_nhds hxz)).const_mul (-t)
      apply hc.congr_of_eventuallyEq
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxK] with y hy
      have hyz : y ≠ z := fun e => hy (e ▸ hzK)
      rw [hw_eq y hyz, hgzero y hy]
      simp [G]
  have hgo := general_odometer_zero_extended_hasLaplacian hμ hR hV hU hsub hz ht hcl hLap
  have hgB : HasLaplacian g σ (ENNReal.ofReal t • Measure.dirac z) (ball 0 R) :=
    hgo.mono_domain (subset_univ _)
  have hGB : HasLaplacian G 0 (Measure.dirac z) (ball 0 R) :=
    (greenFunctionBall R hR z (hsub hz)).1
  have hwΔ : HasLaplacian w σ 0 (ball 0 R) := by
    apply (hgB.sub_const_mul ht.le hGB).congr_ae_volume
    filter_upwards [ae_ne_complex z] with x hx
    exact (hw_eq x hx).symm
  have hw0 : ∀ x ∈ sphere (0 : ℂ) R, w x = 0 := by
    intro x hx
    have hxB : x ∉ ball (0 : ℂ) R := by
      intro h
      rw [mem_sphere] at hx
      rw [mem_ball] at h
      linarith
    have hxU : x ∉ U := fun h => hxB (hsub h)
    simp [w, hxU, G, greenFunction_of_notMem_right hxB]
  have hle : σ.restrict (ball (0 : ℂ) R) ≤ μ.restrict (ball (0 : ℂ) R) :=
    Measure.restrict_mono subset_rfl (general_clusterOn_obstacle_mass_le hΛo hν)
  obtain ⟨-, hrep⟩ := greenRepresentationBallStep_holds μ hμ R βm βp hR hV σ w hle
    hwc.continuousOn hw0 hwΔ y hy
  have hσB : σ.restrict (ball (0 : ℂ) R) = σ := by
    apply Measure.restrict_eq_self_of_ae_mem
    change ∀ᵐ x ∂(μ.restrict Λ + ν.restrict (frontier Λ)), x ∈ ball (0 : ℂ) R
    rw [ae_add_measure_iff]
    exact ⟨(ae_restrict_mem hΛo.measurableSet).mono
      (fun _ hx => hsub (hcl (subset_closure hx))),
      (ae_restrict_mem isClosed_frontier.measurableSet).mono
      (fun _ hx => hsub (hcl (frontier_subset_closure hx)))⟩
  change w y = -∫ x, greenFunction (ball (0 : ℂ) R) y x ∂(σ.restrict (ball 0 R)) at hrep
  rw [hσB, hw_eq y hyz] at hrep
  change g y - t * greenFunction (ball (0 : ℂ) R) z y = _ at hrep
  linarith

/-- The Newtonian potential of the full obstacle mass is the pole
potential minus the zero-extended odometer. -/
theorem general_odometer_newton_representation
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hcl : closure (clusterOn μ U z t) ⊆ U) (hν : ν ≤ μ)
    (hLap : HasLaplacian
      (fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x)
      (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t)))
      (ENNReal.ofReal t • Measure.dirac z) U)
    {y : ℂ} (hyz : y ≠ z) :
    Integrable (fun x => newtonKernel x y)
      (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t))) ∧
    ∫ x, newtonKernel x y
      ∂(μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t))) =
      t * newtonKernel z y -
        U.indicator (fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x) y := by
  let _ : IsLocallyFiniteMeasure μ := hμ
  let Λ := clusterOn μ U z t
  let σ := μ.restrict Λ + ν.restrict (frontier Λ)
  let g := U.indicator (fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x)
  have hΛo : IsOpen Λ := isOpen_clusterOn_of_volumeGrowth hμ hR hV hU hsub hz ht
  have hclB : closure Λ ⊆ ball (0 : ℂ) R := hcl.trans hsub
  have hmem : ∀ᵐ x ∂σ, x ∈ closure Λ := by
    change ∀ᵐ x ∂(μ.restrict Λ + ν.restrict (frontier Λ)), x ∈ closure Λ
    rw [ae_add_measure_iff]
    exact ⟨(ae_restrict_mem hΛo.measurableSet).mono (fun _ hx => subset_closure hx),
      (ae_restrict_mem isClosed_frontier.measurableSet).mono (fun _ hx => frontier_subset_closure hx)⟩
  have hσμ : σ ≤ μ := general_clusterOn_obstacle_mass_le hΛo hν
  have hsing : σ {y} = 0 := by
    by_cases hyB : y ∈ ball (0 : ℂ) R
    · exact le_antisymm ((hσμ _).trans (le_of_eq (hV.measure_singleton hyB))) bot_le
    · have hae : ∀ᵐ x ∂σ, x ≠ y := hmem.mono (fun x hx hxy => hyB (hxy ▸ hclB hx))
      rw [ae_iff] at hae
      simpa using hae
  have hne : ∀ᵐ x ∂σ, x ≠ y := by rw [ae_iff]; simpa using hsing
  have hquad : ∀ (O : Set ℂ) (q : ℂ → ℝ), IsOpen O → closure Λ ⊆ O →
      HarmonicOnNhd q O → Integrable q σ ∧ ∫ x, q x ∂σ = t * q z := by
    intro O q hO hΛO hq
    exact general_clusterOn_harmonic_quadrature_of_hasLaplacian hμ hR hV hU hsub hz ht hcl hLap hO hΛO hq
  by_cases hyB : y ∈ ball (0 : ℂ) R
  · have hGi : Integrable (fun x => greenFunction (ball 0 R) y x) σ := by
      have hi := integrable_greenFunction_ball_left hR hV (ball_subset_closedBall hyB)
      have hσB : σ ≤ μ.restrict (ball (0 : ℂ) R) := by
        have hs : σ.restrict (ball (0 : ℂ) R) = σ :=
          Measure.restrict_eq_self_of_ae_mem (hmem.mono (fun _ hx => hclB hx))
        rw [← hs]
        exact Measure.restrict_mono subset_rfl hσμ
      have he : (fun x => greenFunction (ball (0 : ℂ) R) y x) =
          (fun x => greenFunction (ball (0 : ℂ) R) x y) :=
        funext fun x => greenFunction_ball_comm R y x
      rw [he]
      exact hi.mono_measure hσB
    have hGe := general_odometer_enclosingDisc_green_representation hμ hR hV hU hsub hz ht hcl hν hLap hyB hyz
    have hyR : ‖y‖ < R := mem_ball_zero_iff.1 hyB
    have hqO : IsOpen {x : ℂ | (R : ℂ) ^ 2 - conj y * x ≠ 0} :=
      isOpen_ne_fun (continuous_const.sub (continuous_const.mul continuous_id)) continuous_const
    have hqh : HarmonicOnNhd (greatestHarmonicMinorantBall R y)
        {x : ℂ | (R : ℂ) ^ 2 - conj y * x ≠ 0} :=
      fun x hx => harmonicAt_greatestHarmonicMinorantBall hx
    have hΛq : closure Λ ⊆ {x : ℂ | (R : ℂ) ^ 2 - conj y * x ≠ 0} := fun x hx =>
      norm_pos_iff.1 (norm_sub_conj_mul_pos hR hyR (mem_ball_zero_iff.1 (hclB hx)).le)
    obtain ⟨hqi, hqe⟩ := hquad _ _ hqO hΛq hqh
    have hae : (fun x => newtonKernel x y) =ᵐ[σ]
        fun x => greenFunction (ball 0 R) y x + greatestHarmonicMinorantBall R y x := by
      filter_upwards [hne, hmem] with x hxy hx
      rw [greenFunction_ball_eq_sub hyB (hclB hx) (Ne.symm hxy), newtonKernel_comm]
      ring
    refine ⟨(hGi.add hqi).congr hae.symm, ?_⟩
    rw [integral_congr_ae hae, integral_add hGi hqi, hqe, hGe,
      greenFunction_ball_comm R z y, greenFunction_ball_eq_sub hyB (hsub hz) hyz,
      newtonKernel_comm z y]
    ring
  · have hqh : HarmonicOnNhd (fun x => newtonKernel y x) (ball (0 : ℂ) R) :=
      fun x hx => harmonicAt_newtonKernel (fun e => hyB (e ▸ hx))
    obtain ⟨hqi, hqe⟩ := hquad _ _ isOpen_ball hclB hqh
    have he : (fun x => newtonKernel x y) = fun x => newtonKernel y x :=
      funext fun x => newtonKernel_comm x y
    have hg : g y = 0 := indicator_of_notMem (fun h => hyB (hsub h)) _
    refine ⟨he ▸ hqi, ?_⟩
    change (∫ x, newtonKernel x y ∂σ) = t * newtonKernel z y - g y
    rw [he, hqe, hg, newtonKernel_comm z y, sub_zero]

/-- Green representation for the full obstacle mass on any bounded open
set containing the closed cluster, at every point away from the pole. -/
theorem general_odometer_green_representation
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hcl : closure (clusterOn μ U z t) ⊆ U) (hν : ν ≤ μ)
    (hLap : HasLaplacian
      (fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x)
      (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t)))
      (ENNReal.ofReal t • Measure.dirac z) U)
    {O : Set ℂ} (hO : IsOpen O) (hΛO : closure (clusterOn μ U z t) ⊆ O)
    {y : ℂ} (hy : y ∈ O) (hyz : y ≠ z) :
    Integrable (fun x => greenFunction O x y)
      (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t))) ∧
    ∫ x, greenFunction O x y
      ∂(μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t))) =
      t * greenFunction O z y -
        U.indicator (fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x) y := by
  let _ : IsLocallyFiniteMeasure μ := hμ
  let Λ := clusterOn μ U z t
  let σ := μ.restrict Λ + ν.restrict (frontier Λ)
  have hΛo : IsOpen Λ := isOpen_clusterOn_of_volumeGrowth hμ hR hV hU hsub hz ht
  have hzK : z ∈ closure Λ := subset_closure ⟨hz, Or.inl rfl⟩
  have hK : IsCompact (closure Λ) := (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
    isClosed_closure (hcl.trans (hsub.trans ball_subset_closedBall))
  have hmem : ∀ᵐ x ∂σ, x ∈ closure Λ := by
    change ∀ᵐ x ∂(μ.restrict Λ + ν.restrict (frontier Λ)), x ∈ closure Λ
    rw [ae_add_measure_iff]
    exact ⟨(ae_restrict_mem hΛo.measurableSet).mono (fun _ hx => subset_closure hx),
      (ae_restrict_mem isClosed_frontier.measurableSet).mono (fun _ hx => frontier_subset_closure hx)⟩
  have hσK : σ (closure Λ)ᶜ = 0 := by
    rw [ae_iff] at hmem
    exact hmem
  have hσμ : σ ≤ μ := general_clusterOn_obstacle_mass_le hΛo hν
  have hσfinite : IsFiniteMeasure σ := by
    have hs : σ.restrict (closure Λ) = σ := Measure.restrict_eq_self_of_ae_mem hmem
    rw [← hs]
    apply isFiniteMeasure_restrict.2
    exact ((hσμ _).trans_lt hK.measure_lt_top).ne
  let _ : IsFiniteMeasure σ := hσfinite
  have hsing : σ {y} = 0 := by
    by_cases hyB : y ∈ ball (0 : ℂ) R
    · exact le_antisymm ((hσμ _).trans (le_of_eq (hV.measure_singleton hyB))) bot_le
    · have hae : ∀ᵐ x ∂σ, x ≠ y := hmem.mono (fun x hx hxy => hyB (hxy ▸ hsub (hcl hx)))
      rw [ae_iff] at hae
      simpa using hae
  have hne : ∀ᵐ x ∂σ, x ≠ y := by rw [ae_iff]; simpa using hsing
  obtain ⟨δ, hδ, hδO⟩ := hK.exists_cthickening_subset_open hO hΛO
  have hε : 0 < δ / 3 := by positivity
  have h3 : cthickening (3 * (δ / 3)) (closure Λ) ⊆ O := by
    rw [show 3 * (δ / 3) = δ by ring]
    exact hδO
  have hbal : ∀ w : ℂ, (∀ x ∈ closure Λ, δ / 3 < ‖x - w‖) →
      ∫ x, regularizedNewtonKernel (δ / 3) x w ∂σ =
        t * regularizedNewtonKernel (δ / 3) z w := by
    intro w hw
    have hW : IsOpen {x : ℂ | δ / 3 < ‖x - w‖} :=
      isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
    have hq : HarmonicOnNhd (fun x => regularizedNewtonKernel (δ / 3) x w)
        {x : ℂ | δ / 3 < ‖x - w‖} := by
      intro x hx
      have hxw : x ≠ w := fun e => by
        have hx' : δ / 3 < ‖x - w‖ := hx
        rw [e, sub_self, norm_zero] at hx'
        linarith
      have hev : (fun x => regularizedNewtonKernel (δ / 3) x w) =ᶠ[𝓝 x] newtonKernel w := by
        filter_upwards [hW.mem_nhds hx] with v hv
        rw [regularizedNewtonKernel_of_le_norm (le_of_lt hv), newtonKernel_comm]
      exact (harmonicAt_congr_nhds hev).2 (harmonicAt_newtonKernel hxw)
    exact (general_clusterOn_harmonic_quadrature_of_hasLaplacian hμ hR hV hU hsub hz ht hcl hLap
      hW (fun x hx => hw x hx) hq).2
  obtain ⟨H, hHm, hHag, hHbd, hHid⟩ :=
    greenHarmonicCorrectionBalayageStep_holds O (closure Λ) σ z t (δ / 3)
      hO hK hσfinite hσK hzK hε h3 hbal
  have hHi : Integrable (fun x => H x y) σ := by
    obtain ⟨C, hC⟩ := hHbd {y} isCompact_singleton (singleton_subset_iff.2 hy)
    refine Integrable.of_bound (hHm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable C ?_
    filter_upwards [hmem] with x hx
    rw [Real.norm_eq_abs]
    exact hC x hx y rfl
  have hGeq : ∀ x ∈ closure Λ, x ≠ y → greenFunction O x y = newtonKernel x y - H x y := by
    intro x hx hxy
    rw [greenFunction, ite_eq_left ⟨hΛO hx, hy, hxy⟩, hHag x hx y hy]
  obtain ⟨hNi, hNe⟩ := general_odometer_newton_representation hμ hR hV hU hsub hz ht hcl hν hLap hyz
  have hae : (fun x => greenFunction O x y) =ᵐ[σ] fun x => newtonKernel x y - H x y := by
    filter_upwards [hne, hmem] with x hxy hx
    exact hGeq x hx hxy
  refine ⟨(hNi.sub hHi).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_sub hNi hHi, hNe, hHid y hy, hGeq z hzK (Ne.symm hyz)]
  ring

/-- Exterior Green quadrature holds on the frontier as well as outside the
closed cluster, for the same dominated obstacle mass. -/
theorem general_clusterOn_green_quadrature_exterior
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hcl : closure (clusterOn μ U z t) ⊆ U) (hν : ν ≤ μ)
    (hLap : HasLaplacian
      (fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x)
      (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t)))
      (ENNReal.ofReal t • Measure.dirac z) U)
    {O : Set ℂ} (hO : IsOpen O) (hΛO : closure (clusterOn μ U z t) ⊆ O)
    {y : ℂ} (hy : y ∈ O \ clusterOn μ U z t) :
    Integrable (fun x => greenFunction O x y)
      (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t))) ∧
    ∫ x, greenFunction O x y
      ∂(μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t))) =
      t * greenFunction O z y := by
  have hyz : y ≠ z := by
    intro e
    apply hy.2
    rw [e]
    exact ⟨hz, Or.inl rfl⟩
  have h := general_odometer_green_representation hμ hR hV hU hsub hz ht hcl hν hLap hO hΛO hy.1 hyz
  have hg : U.indicator (fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x) y = 0 := by
    by_cases hyU : y ∈ U
    · rw [indicator_of_mem hyU]
      exact general_odometer_eq_zero_of_notMem_clusterOn hsub ht.le ⟨hyU, hy.2⟩
    · exact indicator_of_notMem hyU _
  exact ⟨h.1, by simpa only [hg, sub_zero] using h.2⟩

/-- On a compact set of poles, the Green kernel has a jointly measurable
representative. -/
theorem aestronglyMeasurable_greenFunction_prod_of_compact
    {O L : Set ℂ} (hO : IsOpen O) (hL : IsCompact L) (hLO : L ⊆ O)
    {z : ℂ} (hz : z ∈ L) {α β : Measure ℂ}
    [IsFiniteMeasure α] [IsFiniteMeasure β] (hα : α Lᶜ = 0) :
    AEStronglyMeasurable (Function.uncurry (greenFunction O)) (α.prod β) := by
  classical
  obtain ⟨δ, hδ, hδO⟩ := hL.exists_cthickening_subset_open hO hLO
  have hε : 0 < δ / 3 := by positivity
  have h3 : cthickening (3 * (δ / 3)) L ⊆ O := by
    rw [show 3 * (δ / 3) = δ by ring]
    exact hδO
  have hbal : ∀ w : ℂ, (∀ x ∈ L, δ / 3 < ‖x - w‖) →
      ∫ x, regularizedNewtonKernel (δ / 3) x w ∂(0 : Measure ℂ) =
        (0 : ℝ) * regularizedNewtonKernel (δ / 3) z w := by
    intros
    simp
  obtain ⟨H, hHm, hHag, -, -⟩ :=
    greenHarmonicCorrectionBalayageStep_holds O L 0 z 0 (δ / 3) hO hL
      inferInstance (by simp) hz hε h3 hbal
  have hprod : ∀ᵐ p ∂(α.prod β), p.1 ∈ L := by
    have h0 : (α.prod β) (Lᶜ ×ˢ univ) = 0 := by
      rw [Measure.prod_prod, hα, zero_mul]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with p hp
    by_contra hc
    exact hp ⟨hc, mem_univ _⟩
  have hset : MeasurableSet {p : ℂ × ℂ | p.2 ∈ O ∧ p.1 ≠ p.2} :=
    (measurable_snd hO.measurableSet).inter isClosed_diagonal.isOpen_compl.measurableSet
  have hm : Measurable (fun p : ℂ × ℂ =>
      if p.2 ∈ O ∧ p.1 ≠ p.2 then newtonKernel p.1 p.2 - H p.1 p.2 else 0) :=
    Measurable.ite hset (measurable_uncurry_newtonKernel.sub hHm) measurable_const
  apply hm.aestronglyMeasurable.congr
  filter_upwards [hprod] with p hp
  simp only [Function.uncurry]
  by_cases hc : p.2 ∈ O ∧ p.1 ≠ p.2
  · rw [ite_eq_left hc, greenFunction, ite_eq_left ⟨hLO hp, hc.1, hc.2⟩,
      hHag p.1 hp p.2 hc.1]
  · rw [ite_eq_right hc, greenFunction, ite_eq_right (fun h => hc ⟨h.2.1, h.2.2⟩)]

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

/-- Green potentials of finite compactly supported exterior source measures
satisfy quadrature for the full obstacle mass, including frontier sources. -/
theorem general_clusterOn_greenPotential_quadrature
    {μ ν : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hcl : closure (clusterOn μ U z t) ⊆ U) (hν : ν ≤ μ)
    (hLap : HasLaplacian
      (fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x)
      (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t)))
      (ENNReal.ofReal t • Measure.dirac z) U)
    {O K : Set ℂ} (hO : IsOpen O) (hOb : Bornology.IsBounded O)
    (hΛO : closure (clusterOn μ U z t) ⊆ O) (hK : IsCompact K)
    (hKO : K ⊆ O \ clusterOn μ U z t) {ρ : Measure ℂ} [IsFiniteMeasure ρ] (hρ : ρ Kᶜ = 0) :
    Integrable (greenPotential O ρ)
      (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t))) ∧
    ∫ x, greenPotential O ρ x
      ∂(μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t))) =
      t * greenPotential O ρ z := by
  let _ : IsLocallyFiniteMeasure μ := hμ
  let Λ := clusterOn μ U z t
  let σ := μ.restrict Λ + ν.restrict (frontier Λ)
  have hΛo : IsOpen Λ := isOpen_clusterOn_of_volumeGrowth hμ hR hV hU hsub hz ht
  have hzΛ : z ∈ Λ := ⟨hz, Or.inl rfl⟩
  have hL : IsCompact (closure Λ) := (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
    isClosed_closure (hcl.trans (hsub.trans ball_subset_closedBall))
  have hmem : ∀ᵐ x ∂σ, x ∈ closure Λ := by
    change ∀ᵐ x ∂(μ.restrict Λ + ν.restrict (frontier Λ)), x ∈ closure Λ
    rw [ae_add_measure_iff]
    exact ⟨(ae_restrict_mem hΛo.measurableSet).mono (fun _ hx => subset_closure hx),
      (ae_restrict_mem isClosed_frontier.measurableSet).mono (fun _ hx => frontier_subset_closure hx)⟩
  have hσL : σ (closure Λ)ᶜ = 0 := by rw [ae_iff] at hmem; exact hmem
  have hσμ : σ ≤ μ := general_clusterOn_obstacle_mass_le hΛo hν
  let _ : IsFiniteMeasure σ := by
    have hs : σ.restrict (closure Λ) = σ := Measure.restrict_eq_self_of_ae_mem hmem
    rw [← hs]
    exact isFiniteMeasure_restrict.2 ((hσμ _).trans_lt hL.measure_lt_top).ne
  have hρK : ∀ᵐ y ∂ρ, y ∈ K := by rw [ae_iff]; exact hρ
  have hGz : Integrable (greenFunction O z) ρ :=
    integrable_greenFunction_source_of_compact hO hOb (hΛO (subset_closure hzΛ)) hK
      (fun y hy => ⟨(hKO hy).1, by
        intro hyz
        apply (hKO hy).2
        rw [hyz]
        exact hzΛ⟩) hρ
  have hΦ : AEStronglyMeasurable (Function.uncurry (greenFunction O)) (σ.prod ρ) :=
    aestronglyMeasurable_greenFunction_prod_of_compact hO hL hΛO (subset_closure hzΛ) hσL
  have hfib : ∀ y ∈ K, Integrable (fun x => greenFunction O x y) σ ∧
      ∫ x, greenFunction O x y ∂σ = t * greenFunction O z y := by
    intro y hy
    exact general_clusterOn_green_quadrature_exterior hμ hR hV hU hsub hz ht hcl hν hLap hO hΛO (hKO hy)
  have hnorm : (fun y => ∫ x, ‖greenFunction O x y‖ ∂σ) =ᵐ[ρ]
      fun y => t * greenFunction O z y := by
    filter_upwards [hρK] with y hy
    rw [← (hfib y hy).2]
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (greenFunction_nonneg hOb x y)]
  have hInt : Integrable (Function.uncurry (greenFunction O)) (σ.prod ρ) := by
    apply (integrable_prod_iff' hΦ).2
    constructor
    · filter_upwards [hρK] with y hy
      exact (hfib y hy).1
    · exact (hGz.const_mul t).congr hnorm.symm
  refine ⟨hInt.integral_prod_left, ?_⟩
  calc ∫ x, greenPotential O ρ x ∂σ = ∫ x, ∫ y, greenFunction O x y ∂ρ ∂σ := rfl
    _ = ∫ y, ∫ x, greenFunction O x y ∂σ ∂ρ := integral_integral_swap (f := greenFunction O) hInt
    _ = ∫ y, t * greenFunction O z y ∂ρ := integral_congr_ae (hρK.mono (fun y hy => (hfib y hy).2))
    _ = t * greenPotential O ρ z := integral_const_mul _ _

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

/-- A compactly contained cluster with null frontier is a harmonic ball for
the frozen enlarged class of harmonic functions and exterior Green potentials. -/
theorem general_clusterOn_isHarmonicBallGen_of_frontier_null
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hcl : closure (clusterOn μ U z t) ⊆ U)
    (hfront : μ (frontier (clusterOn μ U z t)) = 0) :
    IsHarmonicBallGen μ (clusterOn μ U z t) z := by
  let Λ := clusterOn μ U z t
  obtain ⟨ν, hν, hLap, -⟩ := general_odometer_mass_of_compact_containment hμ hR hV hU hsub hz ht hcl
  have hn : ν (frontier Λ) = 0 := le_antisymm ((hν _).trans (le_of_eq hfront)) bot_le
  have hr : ν.restrict (frontier Λ) = 0 := Measure.restrict_eq_zero.mpr hn
  have hmass := (general_clusterOn_harmonic_quadrature_of_frontier_null hμ hR hV hU hsub hz ht hcl hfront).1
  have hreal : μ.real Λ = t := by rw [measureReal_def, hmass, ENNReal.toReal_ofReal ht.le]
  refine ⟨general_clusterOn_isHarmonicBall_of_frontier_null hμ hR hV hU hsub hz ht hcl hfront, ?_⟩
  intro f hf
  obtain ⟨f₁, f₂, O, hf₁, hO, hOb, hΛO, hf₂, rfl⟩ := hf
  obtain ⟨K, ρ₁, ρ₂, hK, hKO, hρ₁, hρ₂, hρ₁K, hρ₂K, rfl⟩ := hf₂
  let _ : IsFiniteMeasure ρ₁ := hρ₁
  let _ : IsFiniteMeasure ρ₂ := hρ₂
  have hq := general_clusterOn_harmonic_quadrature_of_hasLaplacian hμ hR hV hU hsub hz ht hcl hLap
    (q := f₁) (isOpen_setOfPred_harmonicAt f₁) hf₁ (fun _ hx => hx)
  have h1 := general_clusterOn_greenPotential_quadrature hμ hR hV hU hsub hz ht hcl hν hLap
    hO hOb hΛO hK hKO hρ₁K
  have h2 := general_clusterOn_greenPotential_quadrature hμ hR hV hU hsub hz ht hcl hν hLap
    hO hOb hΛO hK hKO hρ₂K
  change ν.restrict (frontier (clusterOn μ U z t)) = 0 at hr
  simp only [hr, add_zero] at hq h1 h2
  refine ⟨hq.1.add (h1.1.sub h2.1), ?_⟩
  change (f₁ z + (greenPotential O ρ₁ z - greenPotential O ρ₂ z)) * μ.real Λ =
    ∫ x, f₁ x + (greenPotential O ρ₁ - greenPotential O ρ₂) x ∂(μ.restrict Λ)
  rw [hreal, integral_add hq.1 (h1.1.sub h2.1)]
  simp only [Pi.sub_apply]
  rw [integral_sub h1.1 h2.1, hq.2, h1.2, h2.2]
  ring


end HarmonicBalls
