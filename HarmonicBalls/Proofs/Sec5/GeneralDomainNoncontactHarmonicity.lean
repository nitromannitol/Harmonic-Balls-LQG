import HarmonicBalls.Proofs.Sec5.GeneralDomainInteriorInfimum

/-! # General-domain noncontact set

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open Filter MeasureTheory Metric Set Laplacian InnerProductSpace
open scoped Topology

/-- The general-domain noncontact set is open, including at the pole. -/
theorem isOpen_clusterOn_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) :
    IsOpen (clusterOn μ U z t) := by
  have hv := (general_domain_interior_infimum_regularity hμ hR hV hU hsub hz ht).1
  rw [isOpen_iff_mem_nhds]
  intro x hx
  change x ∈ U ∧ (x = z ∨ -t * greenFunction U z x < leastSupersolutionOn μ U z t x) at hx
  by_cases hxz : x = z
  · subst x
    have hn := eventually_nhdsWithin_iff.mp
      (eventually_strict_noncontact_nhdsWithin_pole hμ hR hV hU hsub hz ht)
    filter_upwards [hU.mem_nhds hz, hn] with y hy hynear
    change y ∈ U ∧ (y = z ∨ -t * greenFunction U z y < leastSupersolutionOn μ U z t y)
    refine ⟨hy, ?_⟩
    by_cases hyz : y = z
    · exact Or.inl hyz
    · exact Or.inr (hynear hyz).2.2
  · have hlt := hx.2.resolve_left hxz
    obtain ⟨h, hh, hG⟩ :=
      exists_harmonicOnNhd_greenFunction_difference hU (isBounded_ball.subset hsub) hsub hz
    have hGc : ContinuousAt (greenFunction U z) x := by
      have hc := ((hh x hx.1).1.continuousAt).add
        ((continuousOn_greenFunction_ball (hsub hz)).continuousAt
          (isOpen_compl_singleton.mem_nhds hxz))
      apply hc.congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hx.1, isOpen_compl_singleton.mem_nhds hxz] with y hy hyz
      have he := hG y hy hyz
      change greenFunction U z y = h y + greenFunction (ball 0 R) z y
      linarith
    have hvx := hv.continuousAt (hU.mem_nhds hx.1)
    filter_upwards [hU.mem_nhds hx.1, (hGc.const_mul (-t)).eventually_lt hvx hlt] with y hy hlt'
    exact ⟨hy, Or.inr hlt'⟩

/-- On a compact interior set, one admissible competitor approximates the
pointwise infimum uniformly from above. -/
theorem exists_supersolutionOn_uniformly_lt
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ w ∈ supersolutionsOn μ U z t, ∀ x ∈ K,
      w x < leastSupersolutionOn μ U z t x + ε := by
  classical
  let f := leastSupersolutionOn μ U z t
  have hfc : ContinuousOn f U :=
    (general_domain_interior_infimum_regularity hμ hR hV hU hsub hz ht).1
  have hne : (supersolutionsOn μ U z t).Nonempty :=
    ⟨0, zero_mem_supersolutionsOn (isBounded_ball.subset hsub) ht.le⟩
  have hex : ∀ x ∈ K, ∃ w ∈ supersolutionsOn μ U z t, w x < f x + ε := by
    intro x hx
    have hlt : sInf ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ U z t) < f x + ε := by
      change f x < f x + ε
      linarith
    obtain ⟨a, ⟨w, hw, rfl⟩, ha⟩ := exists_lt_of_csInf_lt (hne.image _) hlt
    exact ⟨w, hw, ha⟩
  choose W hW hWlt using hex
  let V : K → Set ℂ := fun x => {y | W x x.property y < f y + ε}
  have hVnear : ∀ x : K, V x ∈ 𝓝 (x : ℂ) := by
    intro x
    have hwc : ContinuousAt (W x x.property) x :=
      ((hW x x.property).1.mono subset_closure).continuousAt (hU.mem_nhds (hKU x.property))
    have hfx : ContinuousAt (fun y => f y + ε) x :=
      (hfc.continuousAt (hU.mem_nhds (hKU x.property))).add continuousAt_const
    exact hwc.eventually_lt hfx (hWlt x x.property)
  obtain ⟨F, hF⟩ := hK.elim_nhds_subcover' (fun x hx => V ⟨x, hx⟩) (fun x hx => hVnear ⟨x, hx⟩)
  have hind : ∀ F : Finset K, ∃ w ∈ supersolutionsOn μ U z t,
      ∀ x ∈ F, ∀ y ∈ V x, w y < f y + ε := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      obtain ⟨w, hw⟩ := hne
      exact ⟨w, hw, by simp⟩
    | @insert a F ha ih =>
      obtain ⟨w, hw, hwlt⟩ := ih
      refine ⟨fun y => min (W a a.property y) (w y),
        min_mem_supersolutionsOn hμ hR hV hU hsub (hW a a.property) hw, ?_⟩
      intro x hx y hy
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact lt_of_le_of_lt (min_le_left _ _) hy
      · exact lt_of_le_of_lt (min_le_right _ _) (hwlt x hx y hy)
  obtain ⟨w, hw, hwlt⟩ := hind F
  refine ⟨w, hw, fun x hx => ?_⟩
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp (hF hx)
  exact hwlt a ha x hxa

#print axioms exists_supersolutionOn_uniformly_lt

/-- A constant-barrier disc has the Poisson extension of the actual
frozen infimum as its shifted infimum. -/
theorem shifted_infimum_eq_discPoissonIntegral
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) {c : ℂ} {ρ L : ℝ}
    (hρ : 0 < ρ) (hd : closedBall c ρ ⊆ U)
    (hb : ∀ y ∈ sphere c ρ, L ≤ leastSupersolutionOn μ U z t y + greenPotentialBall μ R y)
    (ho : ∀ y ∈ ball c ρ, y ≠ z →
      -t * greenFunction U z y + greenPotentialBall μ R y ≤ L)
    {x : ℂ} (hx : x ∈ ball c ρ) :
    leastSupersolutionOn μ U z t x + greenPotentialBall μ R x =
      discPoissonIntegral (fun y => leastSupersolutionOn μ U z t y + greenPotentialBall μ R y) c ρ x := by
  let f := fun y => leastSupersolutionOn μ U z t y + greenPotentialBall μ R y
  have hfc : ContinuousOn f U :=
    (general_domain_interior_infimum_regularity hμ hR hV hU hsub hz ht).1.add
      ((enclosingDisc_potential_shift_on_domain hμ hR hV hsub).1.mono subset_closure)
  have hfi : CircleIntegrable f c ρ :=
    (show IsSweepDisc U c ρ from ⟨hρ, hd⟩).circleIntegrable hfc
  have hs := isSuperharmonicOn_shifted_infimum_of_lowerSemicontinuous hμ hR hV hU hsub hz ht.le
    (lowerSemicontinuousOn_shifted_infimum hμ hR hV hU hsub hz ht)
  have hle : discPoissonIntegral f c ρ x ≤ f x :=
    discPoissonIntegral_le hs.1 (hs.localSuperMean hU) hρ hd hfi x hx
  apply le_antisymm ?_ hle
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨w, hw, hwlt⟩ := exists_supersolutionOn_uniformly_lt hμ hR hV hU hsub hz ht
    (isCompact_sphere c ρ) (sphere_subset_closedBall.trans hd) hε
  let g := fun y => w y + greenPotentialBall μ R y
  have hgi : CircleIntegrable g c ρ :=
    (show IsSweepDisc U c ρ from ⟨hρ, hd⟩).circleIntegrable
      ((hw.1.mono subset_closure).add
        ((enclosingDisc_potential_shift_on_domain hμ hR hV hsub).1.mono subset_closure))
  have hfe : CircleIntegrable (fun y => f y + ε) c ρ := hfi.add (circleIntegrable_const ε c ρ)
  have hmono := discPoissonIntegral_mono hgi hfe hx (fun y hy => by
    have h := hwlt y hy
    dsimp [f, g] at *
    linarith)
  have hsum : discPoissonIntegral (fun y => f y + ε) c ρ x = discPoissonIntegral f c ρ x + ε := by
    change Real.circleAverage (fun y => poissonKernel c x y * (f y + ε)) c ρ =
      Real.circleAverage (fun y => poissonKernel c x y * f y) c ρ + ε
    have he : (fun y => poissonKernel c x y * (f y + ε)) =
        (fun y => poissonKernel c x y * f y + ε * poissonKernel c x y) := by
      funext y
      ring
    have hi₁ : CircleIntegrable (fun y => poissonKernel c x y * f y) c ρ := by
      convert CircleIntegrable.poissonKernel_smul hfi hx using 1
    have hi₂ : CircleIntegrable (fun y => ε * poissonKernel c x y) c ρ := by
      convert (CircleIntegrable.const_smul (a := ε) (circleIntegrable_poissonKernel hx)) using 1
    rw [he, Real.circleAverage_fun_add hi₁ hi₂]
    have he₂ : (fun y => ε * poissonKernel c x y) = ε • poissonKernel c x := by
      ext y
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [he₂, Real.circleAverage_smul, circleAverage_poissonKernel hx]
    simp only [smul_eq_mul, mul_one]
  rw [hsum] at hmono
  have hg := (isGLB_poissonIntegrals_shifted_supersolutionsOn hμ hR hV hU hsub hz ht.le
    hρ hd hb ho hx).1 ⟨w, hw, rfl⟩
  exact hg.trans hmono

#print axioms shifted_infimum_eq_discPoissonIntegral

/-- The shifted general-domain infimum is harmonic on its noncontact set. -/
theorem harmonicOnNhd_shifted_infimum_clusterOn
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) :
    HarmonicOnNhd (fun x => leastSupersolutionOn μ U z t x + greenPotentialBall μ R x)
      (clusterOn μ U z t) := by
  intro x hx
  change x ∈ U ∧ (x = z ∨ -t * greenFunction U z x < leastSupersolutionOn μ U z t x) at hx
  have hbar : ∃ ρ L : ℝ, 0 < ρ ∧ closedBall x ρ ⊆ U ∧
      (∀ y ∈ sphere x ρ, L ≤ leastSupersolutionOn μ U z t y + greenPotentialBall μ R y) ∧
      ∀ y ∈ ball x ρ, y ≠ z → -t * greenFunction U z y + greenPotentialBall μ R y ≤ L := by
    by_cases hxz : x = z
    · subst x
      exact exists_constant_barrier_at_pole hμ hR hV hU hsub hz ht
    · have hlsc := lowerSemicontinuousOn_shifted_infimum hμ hR hV hU hsub hz ht
      have hnonneg : ∀ y ∈ U, 0 ≤ leastSupersolutionOn μ U z t y + greenPotentialBall μ R y :=
        fun y hy => shifted_leastSupersolutionOn_nonneg hμ hR hV hU hsub hz ht.le hy
      have heq : lscRegularization U (fun y => leastSupersolutionOn μ U z t y +
          greenPotentialBall μ R y) x = leastSupersolutionOn μ U z t x + greenPotentialBall μ R x := by
        apply le_antisymm (lscRegularization_le hnonneg hx.1)
        apply le_lscRegularization hnonneg hx.1
        intro ε hε
        have h := hlsc x hx.1 (leastSupersolutionOn μ U z t x + greenPotentialBall μ R x - ε) (by linarith)
        rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hx.1)] at h
        filter_upwards [h] with y hy _
        exact hy.le
      apply exists_constant_barrier_of_strict_regularized_noncontact hμ hR hV hU hsub hz ht.le hx.1 hxz
      rw [heq]
      have h := hx.2.resolve_left hxz
      linarith
  obtain ⟨ρ, L, hρ, hd, hb, ho⟩ := hbar
  let f := fun y => leastSupersolutionOn μ U z t y + greenPotentialBall μ R y
  have hfc : ContinuousOn f U :=
    (general_domain_interior_infimum_regularity hμ hR hV hU hsub hz ht).1.add
      ((enclosingDisc_potential_shift_on_domain hμ hR hV hsub).1.mono subset_closure)
  have hfi : CircleIntegrable f x ρ := (show IsSweepDisc U x ρ from ⟨hρ, hd⟩).circleIntegrable hfc
  apply (harmonicAt_congr_nhds (f₁ := f) (f₂ := discPoissonIntegral f x ρ) ?_).2
    (harmonicOnNhd_discPoissonIntegral hfi x (mem_ball_self hρ))
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ)] with y hy
  exact shifted_infimum_eq_discPoissonIntegral hμ hR hV hU hsub hz ht hρ hd hb ho hy

#print axioms harmonicOnNhd_shifted_infimum_clusterOn

/-- Removing a potential from a distributionally harmonic sum gives the
positive measure as the Laplacian. -/
theorem hasLaplacian_of_add_potential_zero {μ : Measure ℂ} {U : Set ℂ}
    {w q : ℂ → ℝ} (hq : HasLaplacian q 0 μ U)
    (hs : HasLaplacian (fun x => w x + q x) 0 0 U) :
    HasLaplacian w μ 0 U := by
  have hwloc : LocallyIntegrableOn w U := by
    have he : (fun x => (w x + q x) - q x) = w := funext fun x => add_sub_cancel_right _ _
    exact he ▸ hs.1.sub hq.1
  refine ⟨hwloc, fun φ hφ => ?_⟩
  obtain ⟨_, hφμ, hqφ⟩ := hq.2 φ hφ
  have hsφ := (hs.2 φ hφ).2.2
  rw [integral_zero_measure, zero_sub] at hqφ
  rw [integral_zero_measure, sub_zero] at hsφ
  have he : (fun x => (w x + q x) * Δ φ x) =
      fun x => w x * Δ φ x + q x * Δ φ x := by
    funext x
    ring
  rw [he, integral_add (integrable_mul_laplacian_of_test hwloc hφ)
    (integrable_mul_laplacian_of_test hq.1 hφ)] at hsφ
  refine ⟨hφμ, integrable_zero_measure, ?_⟩
  rw [integral_zero_measure, sub_zero]
  linarith

/-- On the noncontact set, the distributional Laplacian of the unshifted
infimum is the original measure, including at the pole. -/
theorem hasLaplacian_leastSupersolutionOn_clusterOn
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) :
    HasLaplacian (leastSupersolutionOn μ U z t) μ 0 (clusterOn μ U z t) := by
  have hopen := isOpen_clusterOn_of_volumeGrowth hμ hR hV hU hsub hz ht
  have hsubset : clusterOn μ U z t ⊆ U := fun _ hx => hx.1
  apply hasLaplacian_of_add_potential_zero
    ((enclosingDisc_potential_shift_on_domain hμ hR hV hsub).2.mono_domain hsubset)
  exact hasLaplacian_zero_of_harmonicOnNhd hopen
    (harmonicOnNhd_shifted_infimum_clusterOn hμ hR hV hU hsub hz ht)

#print axioms hasLaplacian_leastSupersolutionOn_clusterOn
#print axioms hasLaplacian_of_add_potential_zero
#print axioms isOpen_clusterOn_of_volumeGrowth

end HarmonicBalls
