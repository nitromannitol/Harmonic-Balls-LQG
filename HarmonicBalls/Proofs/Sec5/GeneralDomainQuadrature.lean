import HarmonicBalls.Proofs.Sec5.GeneralDomainObstacleMass

/-! # Quadrature for compactly contained general-domain clusters

The potential-theoretic infrastructure uses work of Leonardo Bonanno. -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace
open scoped ContDiff ENNReal

/-- Harmonic quadrature for the actual cluster and frontier obstacle mass. -/
theorem general_clusterOn_harmonic_quadrature
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hcl : closure (clusterOn μ U z t) ⊆ U) :
    ∃ ν : Measure ℂ, ν ≤ μ ∧
      HasLaplacian (fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x)
        (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t)))
        (ENNReal.ofReal t • Measure.dirac z) U ∧
      ∀ (O : Set ℂ) (q : ℂ → ℝ), IsOpen O → closure (clusterOn μ U z t) ⊆ O →
        HarmonicOnNhd q O →
        Integrable q (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t))) ∧
        ∫ x, q x ∂(μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t))) = t * q z := by
  let Λ := clusterOn μ U z t
  let o := fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x
  obtain ⟨ν, hν, hLap, -⟩ := general_odometer_mass_of_compact_containment hμ hR hV hU hsub hz ht hcl
  refine ⟨ν, hν, hLap, ?_⟩
  intro O q hO hΛO hq
  have hΛo : IsOpen Λ := isOpen_clusterOn_of_volumeGrowth hμ hR hV hU hsub hz ht
  have hzΛ : z ∈ Λ := ⟨hz, Or.inl rfl⟩
  have hK : IsCompact (closure Λ) := (isCompact_closedBall 0 R).of_isClosed_subset isClosed_closure
    (hcl.trans (hsub.trans ball_subset_closedBall))
  have hW : IsOpen (O ∩ U) := hO.inter hU
  have hKW : closure Λ ⊆ O ∩ U := subset_inter hΛO hcl
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_cthickening_subset_open hW hKW
  obtain ⟨χ, hχd, hχc, hχW, -, hχ1⟩ := exists_cutoff_of_isCompact_subset_isOpen hK.cthickening hW hδW
  let φ : ℂ → ℝ := fun x => q x * χ x
  have hφd : ContDiff ℝ ∞ φ := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ O
    · exact ((_root_.HarmonicAt.analyticAt (hq x hx)).contDiffAt).mul hχd.contDiffAt
    · have hx' : x ∉ tsupport χ := fun h => hx (hχW h).1
      have hev : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
        simp only [φ, hy, Pi.zero_apply, mul_zero]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hφts : tsupport φ ⊆ tsupport χ := tsupport_mul_subset_right
  have hφT : IsTestFunction U φ :=
    ⟨hφd, hχc.of_isClosed_subset (isClosed_tsupport _) hφts, hφts.trans (hχW.trans inter_subset_right)⟩
  obtain ⟨hi, -, heq⟩ := hLap.2 φ hφT
  have hφq : ∀ x ∈ thickening δ (closure Λ), φ x = q x := fun x hx => by
    simp only [φ, hχ1 x (thickening_subset_cthickening _ _ hx), mul_one]
  have hφK : EqOn φ q (closure Λ) := fun x hx => hφq x (self_subset_thickening hδ _ hx)
  have hΔφ0 : ∀ x ∈ closure Λ, Δ φ x = 0 := by
    intro x hx
    have hev : φ =ᶠ[𝓝 x] q := by
      filter_upwards [isOpen_thickening.mem_nhds (self_subset_thickening hδ _ hx)] with y hy using hφq y hy
    rw [(InnerProductSpace.laplacian_congr_nhds hev).self_of_nhds]
    exact (hq x (hΛO hx)).2.self_of_nhds
  have hoΔ : (fun x => o x * Δ φ x) = fun _ => 0 := by
    funext x
    by_cases hxΛ : x ∈ Λ
    · rw [hΔφ0 x (subset_closure hxΛ), mul_zero]
    by_cases hxU : x ∈ U
    · change (leastSupersolutionOn μ U z t x + t * greenFunction U z x) * Δ φ x = 0
      rw [general_odometer_eq_zero_of_notMem_clusterOn hsub ht.le ⟨hxU, hxΛ⟩, zero_mul]
    · rw [laplacian_eq_zero_of_notMem_tsupport (fun h => hxU (hφT.2.2 h)), mul_zero]
  have hae : φ =ᵐ[μ.restrict Λ + ν.restrict (frontier Λ)] q := by
    change ∀ᵐ x ∂(μ.restrict Λ + ν.restrict (frontier Λ)), φ x = q x
    rw [ae_add_measure_iff]
    constructor
    · filter_upwards [ae_restrict_mem hΛo.measurableSet] with x hx
      exact hφK (subset_closure hx)
    · filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
      exact hφK (frontier_subset_closure hx)
  refine ⟨hi.congr hae, ?_⟩
  rw [hoΔ, integral_zero, integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal ht.le,
    smul_eq_mul, hφK (subset_closure hzΛ), integral_congr_ae hae] at heq
  linarith

/-- Smooth Laplacian-positive tests satisfy quadrature inequality for the obstacle mass. -/
theorem general_clusterOn_smooth_laplacian_quadrature
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hcl : closure (clusterOn μ U z t) ⊆ U) :
    ∃ ν : Measure ℂ, ν ≤ μ ∧
      HasLaplacian (fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x)
        (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t)))
        (ENNReal.ofReal t • Measure.dirac z) U ∧
      ∀ (O : Set ℂ) (q : ℂ → ℝ), IsOpen O → closure (clusterOn μ U z t) ⊆ O →
        ContDiffOn ℝ ∞ q O → (∀ x ∈ O, 0 ≤ Δ q x) →
        Integrable q (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t))) ∧
        ∫ x, q x ∂(μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t))) ≥ t * q z := by
  let Λ := clusterOn μ U z t
  let o := fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x
  obtain ⟨ν, hν, hLap, -⟩ := general_odometer_mass_of_compact_containment hμ hR hV hU hsub hz ht hcl
  refine ⟨ν, hν, hLap, ?_⟩
  intro O q hO hΛO hq hqΔ
  have hΛo : IsOpen Λ := isOpen_clusterOn_of_volumeGrowth hμ hR hV hU hsub hz ht
  have hzΛ : z ∈ Λ := ⟨hz, Or.inl rfl⟩
  have hK : IsCompact (closure Λ) := (isCompact_closedBall 0 R).of_isClosed_subset isClosed_closure
    (hcl.trans (hsub.trans ball_subset_closedBall))
  have hW : IsOpen (O ∩ U) := hO.inter hU
  have hKW : closure Λ ⊆ O ∩ U := subset_inter hΛO hcl
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_cthickening_subset_open hW hKW
  obtain ⟨χ, hχd, hχc, hχW, -, hχ1⟩ := exists_cutoff_of_isCompact_subset_isOpen hK.cthickening hW hδW
  let φ : ℂ → ℝ := fun x => q x * χ x
  have hφd : ContDiff ℝ ∞ φ := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ O
    · exact (hq.contDiffAt (hO.mem_nhds hx)).mul hχd.contDiffAt
    · have hx' : x ∉ tsupport χ := fun h => hx (hχW h).1
      have hev : φ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
        simp only [φ, hy, Pi.zero_apply, mul_zero]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hφts : tsupport φ ⊆ tsupport χ := tsupport_mul_subset_right
  have hφT : IsTestFunction U φ :=
    ⟨hφd, hχc.of_isClosed_subset (isClosed_tsupport _) hφts, hφts.trans (hχW.trans inter_subset_right)⟩
  obtain ⟨hi, -, heq⟩ := hLap.2 φ hφT
  have hφq : ∀ x ∈ thickening δ (closure Λ), φ x = q x := fun x hx => by
    simp only [φ, hχ1 x (thickening_subset_cthickening _ _ hx), mul_one]
  have hφK : EqOn φ q (closure Λ) := fun x hx => hφq x (self_subset_thickening hδ _ hx)
  have hΔφ : ∀ x ∈ closure Λ, Δ φ x = Δ q x := by
    intro x hx
    have hev : φ =ᶠ[𝓝 x] q := by
      filter_upwards [isOpen_thickening.mem_nhds (self_subset_thickening hδ _ hx)] with y hy using hφq y hy
    exact (InnerProductSpace.laplacian_congr_nhds hev).self_of_nhds
  have hoΔ : ∀ᵐ x ∂(volume : Measure ℂ), 0 ≤ o x * Δ φ x := by
    filter_upwards [ae_ne_complex z] with x hxz
    by_cases hxΛ : x ∈ Λ
    · rw [hΔφ x (subset_closure hxΛ)]
      have ho := green_obstacle_le_leastSupersolutionOn (μ := μ) hsub ht.le hxΛ.1 hxz
      exact mul_nonneg (by dsimp [o]; linarith) (hqΔ x (hΛO (subset_closure hxΛ)))
    by_cases hxU : x ∈ U
    · change 0 ≤ (leastSupersolutionOn μ U z t x + t * greenFunction U z x) * Δ φ x
      rw [general_odometer_eq_zero_of_notMem_clusterOn hsub ht.le ⟨hxU, hxΛ⟩, zero_mul]
    · rw [laplacian_eq_zero_of_notMem_tsupport (fun h => hxU (hφT.2.2 h)), mul_zero]
  have hae : φ =ᵐ[μ.restrict Λ + ν.restrict (frontier Λ)] q := by
    change ∀ᵐ x ∂(μ.restrict Λ + ν.restrict (frontier Λ)), φ x = q x
    rw [ae_add_measure_iff]
    constructor
    · filter_upwards [ae_restrict_mem hΛo.measurableSet] with x hx
      exact hφK (subset_closure hx)
    · filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
      exact hφK (frontier_subset_closure hx)
  refine ⟨hi.congr hae, ?_⟩
  have hnonneg : 0 ≤ ∫ x, o x * Δ φ x := integral_nonneg_of_ae hoΔ
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal ht.le,
    smul_eq_mul, hφK (subset_closure hzΛ), integral_congr_ae hae] at heq
  linarith

/-- If the frontier is μ-null, the open cluster has the full source mass and
satisfies harmonic quadrature. -/
theorem general_clusterOn_harmonic_quadrature_of_frontier_null
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hcl : closure (clusterOn μ U z t) ⊆ U)
    (hfront : μ (frontier (clusterOn μ U z t)) = 0) :
    μ (clusterOn μ U z t) = ENNReal.ofReal t ∧
      ∀ (O : Set ℂ) (q : ℂ → ℝ), IsOpen O → closure (clusterOn μ U z t) ⊆ O →
        HarmonicOnNhd q O → Integrable q (μ.restrict (clusterOn μ U z t)) ∧
        ∫ x, q x ∂μ.restrict (clusterOn μ U z t) = t * q z := by
  obtain ⟨ν, hν, -, hquad⟩ := general_clusterOn_harmonic_quadrature hμ hR hV hU hsub hz ht hcl
  have hn : ν (frontier (clusterOn μ U z t)) = 0 :=
    le_antisymm ((hν _).trans (le_of_eq hfront)) bot_le
  have hr : ν.restrict (frontier (clusterOn μ U z t)) = 0 := Measure.restrict_eq_zero.mpr hn
  have hm := general_odometer_mass_of_compact_containment hμ hR hV hU hsub hz ht hcl
  obtain ⟨ν', hν', -, hm⟩ := hm
  have hn' : ν' (frontier (clusterOn μ U z t)) = 0 :=
    le_antisymm ((hν' _).trans (le_of_eq hfront)) bot_le
  refine ⟨by simpa only [hn', add_zero] using hm, ?_⟩
  intro O q hO hΛO hq
  simpa only [hr, add_zero] using hquad O q hO hΛO hq

/-- Smooth Laplacian-positive quadrature when the frontier is μ-null. -/
theorem general_clusterOn_smooth_laplacian_quadrature_of_frontier_null
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hcl : closure (clusterOn μ U z t) ⊆ U)
    (hfront : μ (frontier (clusterOn μ U z t)) = 0)
    {O : Set ℂ} {q : ℂ → ℝ} (hO : IsOpen O)
    (hΛO : closure (clusterOn μ U z t) ⊆ O) (hq : ContDiffOn ℝ ∞ q O)
    (hqΔ : ∀ x ∈ O, 0 ≤ Δ q x) :
    Integrable q (μ.restrict (clusterOn μ U z t)) ∧
      t * q z ≤ ∫ x, q x ∂μ.restrict (clusterOn μ U z t) := by
  obtain ⟨ν, hν, -, hquad⟩ :=
    general_clusterOn_smooth_laplacian_quadrature hμ hR hV hU hsub hz ht hcl
  have hn : ν (frontier (clusterOn μ U z t)) = 0 :=
    le_antisymm ((hν _).trans (le_of_eq hfront)) bot_le
  have hr : ν.restrict (frontier (clusterOn μ U z t)) = 0 := Measure.restrict_eq_zero.mpr hn
  simpa only [hr, add_zero] using hquad O q hO hΛO hq hqΔ

/-- The harmonic mean-value property for a frontier-null cluster. -/
theorem general_clusterOn_harmonic_mean_value_of_frontier_null
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hcl : closure (clusterOn μ U z t) ⊆ U)
    (hfront : μ (frontier (clusterOn μ U z t)) = 0)
    {O : Set ℂ} {q : ℂ → ℝ} (hO : IsOpen O)
    (hΛO : closure (clusterOn μ U z t) ⊆ O) (hq : HarmonicOnNhd q O) :
    q z = (∫ x, q x ∂μ.restrict (clusterOn μ U z t)) / t := by
  have h := (general_clusterOn_harmonic_quadrature_of_frontier_null hμ hR hV hU hsub hz ht hcl hfront).2 O q hO hΛO hq
  rw [h.2, mul_div_cancel_left₀ _ (ne_of_gt ht)]

#print axioms general_clusterOn_harmonic_mean_value_of_frontier_null
#print axioms general_clusterOn_smooth_laplacian_quadrature_of_frontier_null
#print axioms general_clusterOn_smooth_laplacian_quadrature
#print axioms general_clusterOn_harmonic_quadrature
#print axioms general_clusterOn_harmonic_quadrature_of_frontier_null

end HarmonicBalls
