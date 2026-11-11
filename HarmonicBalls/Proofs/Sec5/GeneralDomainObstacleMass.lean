import HarmonicBalls.Proofs.Sec5.GeneralDomainNoncontactHarmonicity
import HarmonicBalls.Proofs.Sec3.ConservationOfMassStep2

/-! # General-domain obstacle mass

The potential-theoretic infrastructure uses work of Leonardo Bonanno. -/

namespace HarmonicBalls

open MeasureTheory Metric Filter Topology Set Laplacian InnerProductSpace
open scoped ENNReal

/-- Away from the pole, the general-domain Green function is harmonic. -/
theorem harmonicOnNhd_general_green_off_pole {U : Set ℂ} (hU : IsOpen U)
    {R : ℝ} (hsub : U ⊆ ball (0 : ℂ) R) {z : ℂ} (hz : z ∈ U) :
    HarmonicOnNhd (greenFunction U z) (U \ {z}) := by
  obtain ⟨h, hh, heq⟩ := exists_harmonicOnNhd_greenFunction_difference hU
    (isBounded_ball.subset hsub) hsub hz
  intro x hx
  apply (harmonicAt_congr_nhds (f₁ := greenFunction U z)
    (f₂ := fun y => greenFunction (ball 0 R) z y + h y) ?_).2
    (((harmonicOnNhd_greenFunction_ball (hsub hz)) x ⟨hsub hx.1, hx.2⟩).add (hh x hx.1))
  filter_upwards [hU.mem_nhds hx.1, isOpen_compl_singleton.mem_nhds hx.2] with y hy hyz
  have := heq y hy hyz
  linarith

/-- The general Green function has distributional Laplacian minus the pole
mass, with its assigned value at the pole irrelevant to volume integration. -/
theorem hasLaplacian_general_green {U : Set ℂ} (hU : IsOpen U)
    {R : ℝ} (hR : 0 < R) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) :
    HasLaplacian (greenFunction U z) 0 (Measure.dirac z) U := by
  obtain ⟨h, hh, heq⟩ := exists_harmonicOnNhd_greenFunction_difference hU
    (isBounded_ball.subset hsub) hsub hz
  have hd := ((greenFunctionBall R hR z (hsub hz)).1).mono_domain hsub
  have hhL := hasLaplacian_zero_of_harmonicOnNhd hU hh
  have hl : LocallyIntegrableOn (fun x => greenFunction (ball 0 R) z x + h x) U := hd.1.add hhL.1
  have hae : ∀ᵐ x ∂volume.restrict U,
      greenFunction (ball 0 R) z x + h x = greenFunction U z x := by
    rw [ae_restrict_iff' hU.measurableSet]
    filter_upwards [ae_ne_complex z] with x hxz hx
    have hx := heq x hx hxz
    linarith
  refine ⟨hl.congr hae, fun φ hφ => ?_⟩
  obtain ⟨h0, hzφ, hdφ⟩ := hd.2 φ hφ
  have hhφ := (hhL.2 φ hφ).2.2
  rw [integral_zero_measure, sub_zero] at hhφ
  have hi : ∫ x, greenFunction U z x * Δ φ x =
      ∫ x, (greenFunction (ball 0 R) z x + h x) * Δ φ x := by
    apply integral_congr_ae
    filter_upwards [ae_ne_complex z] with x hxz
    by_cases hx : x ∈ U
    · have h := heq x hx hxz
      congr 1
      linarith
    · rw [laplacian_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h)), mul_zero, mul_zero]
  refine ⟨h0, hzφ, ?_⟩
  rw [hi]
  have he : (fun x => (greenFunction (ball 0 R) z x + h x) * Δ φ x) =
      fun x => greenFunction (ball 0 R) z x * Δ φ x + h x * Δ φ x := by
    funext x; ring
  rw [he, integral_add (integrable_mul_laplacian_of_test hd.1 hφ)
    (integrable_mul_laplacian_of_test hhL.1 hφ), hhφ, add_zero]
  exact hdφ


/-- The actual infimum lies above its Green obstacle away from the pole. -/
theorem green_obstacle_le_leastSupersolutionOn
    {μ : Measure ℂ} {R : ℝ} {U : Set ℂ} (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} {t : ℝ} (ht : 0 ≤ t) {x : ℂ} (hx : x ∈ U) (hxz : x ≠ z) :
    -t * greenFunction U z x ≤ leastSupersolutionOn μ U z t x := by
  exact (isGLB_supersolutionsOn_values_of_ne_pole (μ := μ)
    (isBounded_ball.subset hsub) ht (subset_closure hx) hxz).2
    (by rintro _ ⟨w, hw, rfl⟩; exact hw.2.2 x (subset_closure hx) hxz)

/-- The general-domain odometer is zero at every off-pole contact point. -/
theorem general_odometer_eq_zero_of_notMem_clusterOn
    {μ : Measure ℂ} {R : ℝ} {U : Set ℂ} (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} {t : ℝ} (ht : 0 ≤ t) {x : ℂ}
    (hx : x ∈ U \ clusterOn μ U z t) :
    leastSupersolutionOn μ U z t x + t * greenFunction U z x = 0 := by
  have hxz : x ≠ z := fun h => hx.2 ⟨hx.1, Or.inl h⟩
  have hnot : ¬ -t * greenFunction U z x < leastSupersolutionOn μ U z t x :=
    fun h => hx.2 ⟨hx.1, Or.inr h⟩
  have hle := green_obstacle_le_leastSupersolutionOn (μ := μ) hsub ht hx.1 hxz
  linarith

/-- The odometer is distributionally subharmonic away from the pole. -/
theorem laplacianGE_general_odometer_off_pole
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) :
    LaplacianGE (fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x)
      0 (U \ {z}) := by
  let D := U \ {z}
  let Λ := clusterOn μ U z t
  let v := leastSupersolutionOn μ U z t
  let G := greenFunction U z
  let q := greenPotentialBall μ R
  let w := fun x => v x + q x
  let o := fun x => v x + t * G x
  have hDo : IsOpen D := hU.sdiff isClosed_singleton
  have hΛo : IsOpen Λ := isOpen_clusterOn_of_volumeGrowth hμ hR hV hU hsub hz ht
  have hvcont : ContinuousOn v U := (general_domain_interior_infimum_regularity hμ hR hV hU hsub hz ht).1
  have hGh : HarmonicOnNhd G D := harmonicOnNhd_general_green_off_pole hU hsub hz
  have hGc : ContinuousOn G D := hGh.continuousOn
  have hoc : ContinuousOn o D := (hvcont.mono sdiff_subset).add (continuousOn_const.mul hGc)
  have ho0 : ∀ x ∈ D, 0 ≤ o x := by
    intro x hx
    have h := green_obstacle_le_leastSupersolutionOn (μ := μ) hsub ht.le hx.1 hx.2
    dsimp [o, v, G]
    linarith
  have hw : HarmonicOnNhd w Λ := harmonicOnNhd_shifted_infimum_clusterOn hμ hR hV hU hsub hz ht
  have hqc : ContinuousOn q (ball (0 : ℂ) R) :=
    (greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV).mono ball_subset_closedBall
  have hqsh := isSuperharmonicOn_greenPotentialBall hμ hR hV
  have hoci : ∀ {x : ℂ} {r : ℝ}, 0 < r → closedBall x r ⊆ D → CircleIntegrable o x r :=
    fun hr hs => (hoc.mono (sphere_subset_closedBall.trans hs)).circleIntegrable hr.le
  have hloc : ∀ x ∈ D, ∃ r₀ > 0, ∀ r ∈ Ioo 0 r₀,
      CircleIntegrable (-o) x r ∧ Real.circleAverage (-o) x r ≤ (-o) x := by
    intro x hx
    by_cases hxΛ : x ∈ Λ
    · obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 (hΛo.inter hDo) x ⟨hxΛ, hx⟩
      refine ⟨ρ, hρ, fun r hr => ?_⟩
      have hs : closedBall x r ⊆ Λ ∩ D := (closedBall_subset_ball hr.2).trans hρsub
      have hsΛ : closedBall x r ⊆ Λ := fun y hy => (hs hy).1
      have hsD : closedBall x r ⊆ D := fun y hy => (hs hy).2
      have hsB : closedBall x r ⊆ ball (0 : ℂ) R := fun y hy => hsub (hsD hy).1
      have hwc : ContinuousOn w Λ := hw.continuousOn
      have hwi : CircleIntegrable w x r := (hwc.mono (sphere_subset_closedBall.trans hsΛ)).circleIntegrable hr.1.le
      have hGi : CircleIntegrable G x r := (hGc.mono (sphere_subset_closedBall.trans hsD)).circleIntegrable hr.1.le
      have hqi : CircleIntegrable q x r := (hqc.mono (sphere_subset_closedBall.trans hsB)).circleIntegrable hr.1.le
      have hweq : Real.circleAverage w x r = w x :=
        InnerProductSpace.HarmonicOnNhd.circleAverage_eq (hw.mono (by rw [abs_of_pos hr.1]; exact hsΛ))
      have hGeq : Real.circleAverage G x r = G x :=
        InnerProductSpace.HarmonicOnNhd.circleAverage_eq (hGh.mono (by rw [abs_of_pos hr.1]; exact hsD))
      have hqavg := (hqsh.2 x (hsB (mem_closedBall_self hr.1.le)) r hr.1 hsB).2
      have heq : o = fun y => w y + t • G y - q y := by
        funext y
        dsimp [o, w]
        ring
      have hti : CircleIntegrable (fun y => t • G y) x r := hGi.const_smul
      have hoavg : Real.circleAverage o x r = w x + t * G x - Real.circleAverage q x r := by
        rw [heq]
        rw [Real.circleAverage_fun_sub (f₁ := fun y => w y + t • G y) (hwi.add hti) hqi,
          Real.circleAverage_fun_add hwi hti, Real.circleAverage_fun_smul, hweq, hGeq, smul_eq_mul]
      refine ⟨(hoci hr.1 hsD).neg, ?_⟩
      rw [circleAverage_neg_fun, Pi.neg_apply, hoavg]
      dsimp [o, w]
      linarith
    · obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 hDo x hx
      refine ⟨ρ, hρ, fun r hr => ?_⟩
      have hs : closedBall x r ⊆ D := (closedBall_subset_ball hr.2).trans hρsub
      have hoi := hoci hr.1 hs
      have hox : o x = 0 := general_odometer_eq_zero_of_notMem_clusterOn hsub ht.le ⟨hx.1, hxΛ⟩
      have hm := Real.circleAverage_mono (continuousOn_const.circleIntegrable' (f := fun _ : ℂ => (0 : ℝ))) hoi
        (fun y hy => ho0 y (hs (sphere_subset_closedBall (by rwa [abs_of_pos hr.1] at hy))))
      rw [Real.circleAverage_const] at hm
      refine ⟨hoi.neg, ?_⟩
      rw [circleAverage_neg_fun, Pi.neg_apply, hox]
      linarith
  have hlsc : LowerSemicontinuousOn (-o) D := hoc.neg.lowerSemicontinuousOn
  have hsh : IsSuperharmonicOn D (-o) := ⟨hlsc, fun x hx r hr hs =>
    ⟨(hoci hr hs).neg, circleAverage_le_of_localSuperMean hlsc hloc hr hs (hoci hr hs).neg⟩⟩
  exact LaplacianGE.of_laplacianLE_neg (laplacianLEOfSuperharmonicStep_holds D (-o) hDo hoc.neg hsh)

/-- The distributional obstacle mass consists of the original measure on the
open cluster and a dominated measure on its frontier. -/
theorem general_odometer_mass_decomposition
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) :
    ∃ ν : Measure ℂ, ν ≤ μ ∧
      HasLaplacian (fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x)
        (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t)))
        (ENNReal.ofReal t • Measure.dirac z) U := by
  let v := leastSupersolutionOn μ U z t
  let q := greenPotentialBall μ R
  let w := fun x => v x + q x
  let G := greenFunction U z
  let Λ := clusterOn μ U z t
  have hΛo : IsOpen Λ := isOpen_clusterOn_of_volumeGrowth hμ hR hV hU hsub hz ht
  have hΛU : Λ ⊆ U := fun _ hx => hx.1
  have hzΛ : z ∈ Λ := ⟨hz, Or.inl rfl⟩
  have hq : HasLaplacian q 0 μ U := (enclosingDisc_potential_shift_on_domain hμ hR hV hsub).2
  have hwLE : LaplacianLE w 0 U := (laplacianLE_iff_add_potential hμ hq).1
    (general_domain_interior_infimum_regularity hμ hR hV hU hsub hz ht).2
  have hwΛ : HasLaplacian w 0 0 Λ := hasLaplacian_zero_of_harmonicOnNhd hΛo
    (harmonicOnNhd_shifted_infimum_clusterOn hμ hR hV hU hsub hz ht)
  have ho : (fun x => w x - (-t * G x + q x)) = fun x => v x + t * G x := by
    funext x
    dsimp [w]
    ring
  have hge : LaplacianGE (fun x => w x - (-t * G x + q x)) 0 (U \ {z}) := by
    rw [ho]
    exact laplacianGE_general_odometer_off_pole hμ hR hV hU hsub hz ht
  have hzero : ∀ x ∈ U \ Λ, w x - (-t * G x + q x) = 0 := by
    intro x hx
    rw [show w x - (-t * G x + q x) = v x + t * G x by dsimp [w]; ring]
    exact general_odometer_eq_zero_of_notMem_clusterOn hsub ht.le hx
  obtain ⟨ν, hν, hΔ⟩ := obstacleConservationOfMassStep2_holds U Λ z μ t w G q hU hΛo hΛU hzΛ hμ ht.le
    hwLE hwΛ (hasLaplacian_general_green hU hR hsub hz) hq hge hzero
  exact ⟨ν, hν, ho ▸ hΔ⟩

/-- Compact containment identifies the total cluster and frontier mass. -/
theorem general_odometer_mass_of_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hcl : closure (clusterOn μ U z t) ⊆ U) :
    ∃ ν : Measure ℂ, ν ≤ μ ∧
      HasLaplacian (fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x)
        (μ.restrict (clusterOn μ U z t) + ν.restrict (frontier (clusterOn μ U z t)))
        (ENNReal.ofReal t • Measure.dirac z) U ∧
      μ (clusterOn μ U z t) + ν (frontier (clusterOn μ U z t)) = ENNReal.ofReal t := by
  let Λ := clusterOn μ U z t
  let K := closure Λ
  let o := fun x => leastSupersolutionOn μ U z t x + t * greenFunction U z x
  obtain ⟨ν, hν, hΔ⟩ := general_odometer_mass_decomposition hμ hR hV hU hsub hz ht
  have hΛo : IsOpen Λ := isOpen_clusterOn_of_volumeGrowth hμ hR hV hU hsub hz ht
  have hzΛ : z ∈ Λ := ⟨hz, Or.inl rfl⟩
  have hK : IsCompact K := IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) R) isClosed_closure
    (hcl.trans (hsub.trans ball_subset_closedBall))
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hcl
  obtain ⟨χ, hχd, hχc, hχU, hχ01, hχ1⟩ :=
    exists_cutoff_of_isCompact_subset_isOpen hK.cthickening hU hδU
  have hχ : IsTestFunction U χ := ⟨hχd, hχc, hχU⟩
  have hχK : ∀ x ∈ K, χ x = 1 := fun x hx => hχ1 x (self_subset_cthickening _ hx)
  have hΔχ : ∀ x ∈ K, Δ χ x = 0 := by
    intro x hx
    have heq : χ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [ball_mem_nhds x hδ] with y hy
      exact hχ1 y (mem_cthickening_of_dist_le y x δ _ hx (mem_ball.1 hy).le)
    rw [(InnerProductSpace.laplacian_congr_nhds heq).self_of_nhds]
    simp
  have hoχ : (fun x => o x * Δ χ x) = fun _ => 0 := by
    funext x
    by_cases hx : x ∈ K
    · rw [hΔχ x hx, mul_zero]
    by_cases hxU : x ∈ U
    · have hxΛ : x ∉ Λ := fun h => hx (subset_closure h)
      change (leastSupersolutionOn μ U z t x + t * greenFunction U z x) * Δ χ x = 0
      rw [general_odometer_eq_zero_of_notMem_clusterOn hsub ht.le ⟨hxU, hxΛ⟩, zero_mul]
    · rw [laplacian_eq_zero_of_notMem_tsupport (fun h => hxU (hχU h)), mul_zero]
  have he := (hΔ.2 χ hχ).2.2
  rw [hoχ, integral_zero, integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal ht.le, smul_eq_mul, hχK z (subset_closure hzΛ), mul_one] at he
  have hlin : ∫⁻ x, ENNReal.ofReal (χ x) ∂(μ.restrict Λ + ν.restrict (frontier Λ)) =
      μ Λ + ν (frontier Λ) := by
    rw [lintegral_add_measure]
    have h1 : ∫⁻ x, ENNReal.ofReal (χ x) ∂μ.restrict Λ = μ Λ := by
      calc
        _ = ∫⁻ _x, (1 : ℝ≥0∞) ∂μ.restrict Λ := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem hΛo.measurableSet] with x hx
          rw [hχK x (subset_closure hx), ENNReal.ofReal_one]
        _ = μ Λ := by simp
    have h2 : ∫⁻ x, ENNReal.ofReal (χ x) ∂ν.restrict (frontier Λ) = ν (frontier Λ) := by
      calc
        _ = ∫⁻ _x, (1 : ℝ≥0∞) ∂ν.restrict (frontier Λ) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
          rw [hχK x (frontier_subset_closure hx), ENNReal.ofReal_one]
        _ = ν (frontier Λ) := by simp
    rw [h1, h2]
  refine ⟨ν, hν, hΔ, ?_⟩
  rw [← hlin, ← ofReal_integral_eq_lintegral_ofReal (hΔ.2 χ hχ).1
    (Eventually.of_forall fun x => (hχ01 x).1)]
  congr 1
  linarith

/-- Compact containment bounds the mass of the open cluster by the source mass. -/
theorem general_clusterOn_mass_le_of_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hcl : closure (clusterOn μ U z t) ⊆ U) :
    μ (clusterOn μ U z t) ≤ ENNReal.ofReal t := by
  obtain ⟨ν, -, -, hm⟩ := general_odometer_mass_of_compact_containment hμ hR hV hU hsub hz ht hcl
  exact le_trans (le_add_right le_rfl) (le_of_eq hm)





end HarmonicBalls
