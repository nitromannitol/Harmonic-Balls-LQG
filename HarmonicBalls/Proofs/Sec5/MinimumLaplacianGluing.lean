import HarmonicBalls.Proofs.Sec5.DiscSupportedBoundary

/-! # Minimum and gluing of distributional supersolutions -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- The minimum of two continuous distributional supersolutions is a
supersolution when the measure admits a continuous potential. -/
theorem LaplacianLE.min_of_potential {μ : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) {U : Set ℂ} (hU : IsOpen U)
    {u v q : ℂ → ℝ} (huc : ContinuousOn u U) (hvc : ContinuousOn v U)
    (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (hu : LaplacianLE u μ U) (hv : LaplacianLE v μ U) :
    LaplacianLE (fun x => min (u x) (v x)) μ U := by
  have huq := (laplacianLE_iff_add_potential hμ hq).mp hu
  have hvq := (laplacianLE_iff_add_potential hμ hq).mp hv
  have hsu := superharmonicOfLaplacianLEStep_holds U (fun x => u x + q x) hU
    (huc.add hqc) huq
  have hsv := superharmonicOfLaplacianLEStep_holds U (fun x => v x + q x) hU
    (hvc.add hqc) hvq
  have hs := isSuperharmonicOn_min_continuous (huc.add hqc) (hvc.add hqc) hsu hsv
  have hc : ContinuousOn (fun x => min (u x + q x) (v x + q x)) U :=
    fun x hx => ((huc x hx).add (hqc x hx)).min ((hvc x hx).add (hqc x hx))
  have hl := laplacianLEOfSuperharmonicStep_holds U _ hU hc hs
  apply (laplacianLE_iff_add_potential hμ hq).mpr
  have he : (fun x => min (u x) (v x) + q x) =
      (fun x => min (u x + q x) (v x + q x)) := by
    funext x
    exact (min_add_add_right (u x) (v x) (q x)).symm
  rw [he]
  exact hl

/-- Two distributional supersolutions that agree on the overlap of an open
cover can be glued without changing their common Laplacian bound. -/
theorem LaplacianLE.glue_of_open_cover {μ : Measure ℂ} {D U O : Set ℂ}
    (hD : IsOpen D) (hU : IsOpen U) (hO : IsOpen O) (hsub : U ⊆ D)
    (hcover : closure D ⊆ U ∪ O) {u v : ℂ → ℝ}
    (huc : ContinuousOn u U) (hvc : ContinuousOn v (closure D))
    (hu : LaplacianLE u μ U) (hv : LaplacianLE v μ D)
    (heq : EqOn u v (U ∩ O)) :
    ∃ w : ℂ → ℝ, ContinuousOn w (closure D) ∧ LaplacianLE w μ D ∧
      EqOn w u U ∧ EqOn w v O := by
  classical
  let w : ℂ → ℝ := fun x => if x ∈ U then u x else v x
  have hwin : EqOn w u U := by
    intro x hx
    simp [w, hx]
  have hwO : EqOn w v O := by
    intro x hx
    by_cases hxU : x ∈ U
    · simpa [w, hxU] using heq ⟨hxU, hx⟩
    · simp [w, hxU]
  have hwc : ContinuousOn w (closure D) := by
    intro x hx
    by_cases hxU : x ∈ U
    · have hev : w =ᶠ[𝓝 x] u := by
        filter_upwards [hU.mem_nhds hxU] with y hy
        exact hwin hy
      exact ((huc.continuousAt (hU.mem_nhds hxU)).congr hev.symm).continuousWithinAt
    · have hxO : x ∈ O := (hcover hx).resolve_left hxU
      have hev : w =ᶠ[𝓝 x] v := by
        filter_upwards [hO.mem_nhds hxO] with y hy
        exact hwO hy
      exact (hvc x hx).congr_of_eventuallyEq (hev.filter_mono nhdsWithin_le_nhds) (hwO hxO)
  have hLU : LaplacianLE w μ U := hu.congr_eqOn hU.measurableSet (fun x hx => (hwin hx).symm)
  have hLO : LaplacianLE w μ (D ∩ O) :=
    (hv.mono_set inter_subset_left).congr_eqOn (hD.inter hO).measurableSet
      (fun x hx => (hwO hx.2).symm)
  have hunion : U ∪ (D ∩ O) = D := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hsub hx
      · exact hx.1
    · intro hx
      rcases hcover (subset_closure hx) with hxU | hxO
      · exact Or.inl hxU
      · exact Or.inr ⟨hx, hxO⟩
  exact ⟨w, hwc, hunion ▸ LaplacianLE.union hU (hD.inter hO) hLU hLO,
    hwin, hwO⟩

/-- An arbitrary general-domain competitor can be clipped against the disc
least supersolution and extended to a disc competitor when the disc cluster
is compactly contained in the general domain. -/
theorem exists_disc_supersolution_le_shift_of_compact_cluster
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {U : Set ℂ} (hU : IsOpen U) {r t : ℝ} (hr : 0 < r) {z : ℂ}
    (hsub : U ⊆ ball (0 : ℂ) r) (hz : z ∈ U)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    {h : ℂ → ℝ} (hc : ContinuousOn h (closure U))
    (hh : InnerProductSpace.HarmonicOnNhd h U)
    (hG : ∀ x ∈ closure U, x ≠ z →
      greenFunction U z x - greenFunction (ball 0 r) z x = h x)
    (hd : leastSupersolution μ r z t ∈ supersolutions μ r z t)
    (hcl : closure (cluster μ r z t) ⊆ U)
    {v : ℂ → ℝ} (hv : v ∈ supersolutionsOn μ U z t) :
    ∃ w ∈ supersolutions μ r z t, ∀ x ∈ U, w x ≤ v x + t * h x := by
  classical
  let d := leastSupersolution μ r z t
  let g : ℂ → ℝ := fun x => v x + t * h x
  let a : ℂ → ℝ := fun x => min (g x) (d x)
  let O := (closure (cluster μ r z t))ᶜ
  have hO : IsOpen O := isClosed_closure.isOpen_compl
  have hzball := hsub hz
  have hzO : z ∉ O := fun h => h (subset_closure ⟨hzball, Or.inl rfl⟩)
  have hcover : closure (ball (0 : ℂ) r) ⊆ U ∪ O := by
    intro x _
    by_cases hx : x ∈ U
    · exact Or.inl hx
    · exact Or.inr (fun hxcl => hx (hcl hxcl))
  have huc : ContinuousOn g U :=
    (hv.1.mono subset_closure).add (continuousOn_const.mul (hc.mono subset_closure))
  have hdc : ContinuousOn d (closure (ball (0 : ℂ) r)) := by
    rw [closure_ball (0 : ℂ) hr.ne']
    exact hd.1
  have hdcU : ContinuousOn d U := hdc.mono (hsub.trans subset_closure)
  have hLu : LaplacianLE g μ U :=
    hv.2.1.add_const_mul_of_hasLaplacian_zero (hasLaplacian_zero_of_harmonicOnNhd hU hh) t
  have hLd : LaplacianLE d μ U := hd.2.1.mono_set hsub
  have hLa : LaplacianLE a μ U := hLu.min_of_potential hμ hU huc hdcU hqc hq hLd
  have hshift : ∀ x ∈ U, x ≠ z → -t * greenFunction (ball 0 r) z x ≤ g x := by
    intro x hx hxz
    have h1 := hv.2.2 x (subset_closure hx) hxz
    have h2 := hG x (subset_closure hx) hxz
    have heq : t * h x = t * greenFunction U z x -
        t * greenFunction (ball 0 r) z x := by rw [← h2]; ring
    dsimp [g]
    linarith
  have hEq : EqOn a d (U ∩ O) := by
    intro x hx
    have hxz : x ≠ z := fun he => hzO (he ▸ hx.2)
    have hno : ¬ -t * greenFunction (ball 0 r) z x < d x :=
      fun hpos => hx.2 (subset_closure ⟨hsub hx.1, Or.inr hpos⟩)
    have hlow := hd.2.2 x (ball_subset_closedBall (hsub hx.1)) hxz
    have hdeq : d x = -t * greenFunction (ball 0 r) z x :=
      le_antisymm (not_lt.mp hno) hlow
    exact min_eq_right (hdeq ▸ hshift x hx.1 hxz)
  obtain ⟨w, hwc, hwL, hwa, hwd⟩ :=
    LaplacianLE.glue_of_open_cover isOpen_ball hU hO hsub hcover
      (fun x hx => (huc x hx).min (hdcU x hx)) hdc hLa hd.2.1 hEq
  have hwS : w ∈ supersolutions μ r z t := by
    refine ⟨?_, hwL, ?_⟩
    · simpa only [closure_ball (0 : ℂ) hr.ne'] using hwc
    · intro x hx hxz
      by_cases hxU : x ∈ U
      · rw [hwa hxU]
        exact le_min (hshift x hxU hxz) (hd.2.2 x hx hxz)
      · have hxO : x ∈ O := fun hxc => hxU (hcl hxc)
        rw [hwd hxO]
        exact hd.2.2 x hx hxz
  refine ⟨w, hwS, ?_⟩
  intro x hx
  rw [hwa hx]
  exact min_le_left _ _

/-- Compact containment of the disc cluster makes the shifted disc least
supersolution the admissible least supersolution on the smaller domain. -/
theorem leastSupersolutionOn_mem_of_compact_disc_cluster
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {U : Set ℂ} (hU : IsOpen U) {r t : ℝ} (hr : 0 < r) {z : ℂ}
    (hsub : U ⊆ ball (0 : ℂ) r) (hz : z ∈ U)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    {h : ℂ → ℝ} (hc : ContinuousOn h (closure U))
    (hh : InnerProductSpace.HarmonicOnNhd h U)
    (hG : ∀ x ∈ closure U, x ≠ z →
      greenFunction U z x - greenFunction (ball 0 r) z x = h x)
    (hd : leastSupersolution μ r z t ∈ supersolutions μ r z t)
    (hcl : closure (cluster μ r z t) ⊆ U) :
    leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t := by
  let f : ℂ → ℝ := fun x => leastSupersolution μ r z t x + (-t) * h x
  have hf : f ∈ supersolutionsOn μ U z t :=
    shifted_supersolutionOn_of_green_difference hU hsub hd hc hh hG
  have hbound : ∀ v ∈ supersolutionsOn μ U z t, ∀ x ∈ closure U, f x ≤ v x := by
    intro v hv
    obtain ⟨w, hw, hwle⟩ := exists_disc_supersolution_le_shift_of_compact_cluster
      hμ hU hr hsub hz hqc hq hc hh hG hd hcl hv
    have hoff : ∀ x ∈ U, x ≠ z → f x ≤ v x := by
      intro x hx hxz
      have h1 := leastSupersolution_le hw (ball_subset_closedBall (hsub hx)) hxz
      have h2 := hwle x hx
      dsimp [f]
      linarith
    have hin : ∀ x ∈ U, f x ≤ v x := by
      intro x hx
      by_cases hxz : x = z
      · subst x
        have hfc := hf.1.continuousAt (mem_of_superset (hU.mem_nhds hz) subset_closure)
        have hvc := hv.1.continuousAt (mem_of_superset (hU.mem_nhds hz) subset_closure)
        have : (𝓝[{z}ᶜ] z).NeBot := by
          apply mem_closure_iff_nhdsWithin_neBot.mp
          exact (dense_compl_singleton z) z
        apply le_of_tendsto_of_tendsto (b := 𝓝[{z}ᶜ] z)
          (hfc.tendsto.mono_left nhdsWithin_le_nhds)
          (hvc.tendsto.mono_left nhdsWithin_le_nhds)
        filter_upwards [(show ∀ᶠ y in 𝓝 z, y ∈ U from hU.mem_nhds hz).filter_mono
          nhdsWithin_le_nhds,
          self_mem_nhdsWithin] with y hy hyz
        exact hoff y hy (by simpa using hyz)
      · exact hoff x hx hxz
    exact fun x hx => le_on_closure hin hf.1 hv.1 hx
  have heq : EqOn (leastSupersolutionOn μ U z t) f (closure U) := by
    intro x hx
    have hbdd : BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ U z t) := by
      refine ⟨f x, ?_⟩
      rintro _ ⟨v, hv, rfl⟩
      exact hbound v hv x hx
    apply le_antisymm
    · exact csInf_le hbdd ⟨_, hf, rfl⟩
    · change f x ≤ sInf ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ U z t)
      apply le_csInf (show ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ U z t).Nonempty
        from ⟨_, ⟨f, hf, rfl⟩⟩)
      rintro _ ⟨v, hv, rfl⟩
      exact hbound v hv x hx
  refine ⟨hf.1.congr heq, ?_, ?_⟩
  · exact hf.2.1.congr_eqOn hU.measurableSet (heq.symm.mono subset_closure)
  · intro x hx hxz
    rw [heq hx]
    exact hf.2.2 x hx hxz

/-- Under volume growth and Green boundary regularity, compact containment
of the disc cluster implies admissibility on the smaller domain. -/
theorem leastSupersolutionOn_mem_of_compact_disc_cluster_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U : Set ℂ}
    (hU : IsOpen U) {r βm βp : ℝ} (hr : 0 < r)
    (hV : VolumeGrowth μ r βm βp) (hsub : U ⊆ ball (0 : ℂ) r)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ y ∈ closure U, y ∉ U →
      Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0))
    (hcl : closure (cluster μ r z t) ⊆ U) :
    leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t := by
  obtain ⟨h, hc, hh, hG⟩ :=
    exists_continuousOn_green_difference_of_boundary_limits hU hsub hz hboundary
  obtain ⟨_, _, hd⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hr hV (hsub hz) ht
  exact leastSupersolutionOn_mem_of_compact_disc_cluster hμ hU hr hsub hz
    ((greenPotentialBallContinuousStep_holds μ hμ r βm βp hr hV).mono
      (hsub.trans ball_subset_closedBall))
    ((greenPotentialBallLaplacianStep_holds μ hμ r βm βp hr hV).mono_domain hsub)
    hc hh hG hd hcl

/-- A compactly contained disc cluster agrees with the smaller-domain cluster
without a separate general-domain admissibility hypothesis. -/
theorem clusterOn_eq_cluster_of_compact_disc_cluster_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U : Set ℂ}
    (hU : IsOpen U) {r βm βp : ℝ} (hr : 0 < r)
    (hV : VolumeGrowth μ r βm βp) (hsub : U ⊆ ball (0 : ℂ) r)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ y ∈ closure U, y ∉ U →
      Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0))
    (hcl : closure (cluster μ r z t) ⊆ U) :
    clusterOn μ U z t = cluster μ r z t := by
  have hv := leastSupersolutionOn_mem_of_compact_disc_cluster_of_volumeGrowth
    hμ hU hr hV hsub hz ht hboundary hcl
  obtain ⟨h, hc, hh, hG⟩ :=
    exists_continuousOn_green_difference_of_boundary_limits hU hsub hz hboundary
  exact clusterOn_eq_cluster_of_green_difference_of_nonneg hU hsub hz ht.le hv hc hh hG
    (Or.inl hcl)

/-- A regularized cluster compactly contained in a Green-regular domain has
the same closure as its general-domain cluster, without assuming the latter's
least supersolution is admissible. -/
theorem regularizedFamily_closure_eq_clusterOn_of_boundary_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hboundary : ∀ y ∈ closure U, y ∉ U →
      Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0))
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U) :
    closure (Λ t) = closure (clusterOn μ U z t) := by
  obtain ⟨r₁, hr₁⟩ := hUb.subset_ball (0 : ℂ)
  obtain ⟨r₂, hr₂⟩ := ((hΛ.1.isBounded t ht).closure).subset_ball (0 : ℂ)
  let r := max 1 (max r₁ r₂) + 1
  have hr : 0 < r := by dsimp [r]; linarith [le_max_left (1 : ℝ) (max r₁ r₂)]
  have hr₁r : r₁ ≤ r := by
    dsimp [r]; linarith [(le_max_left r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))]
  have hr₂r : r₂ ≤ r := by
    dsimp [r]; linarith [(le_max_right r₁ r₂).trans (le_max_right (1 : ℝ) (max r₁ r₂))]
  have hUr : U ⊆ ball (0 : ℂ) r := hr₁.trans (ball_subset_ball hr₁r)
  have hΛr : closure (Λ t) ⊆ ball (0 : ℂ) r := hr₂.trans (ball_subset_ball hr₂r)
  have hrepr := hΛ.2.2 t ht r hr hΛr r le_rfl
  have hcluster : closure (Λ t) = closure (cluster μ r z t) := by
    rw [hrepr, closure_regularizedCluster_eq_of_isOpen
      (isOpen_cluster_of_volumeGrowth hμ hV ht r hr (hUr hz))]
  have heq := clusterOn_eq_cluster_of_compact_disc_cluster_of_volumeGrowth
    hμ hU hr (hV r hr) hUr hz ht hboundary (hcluster ▸ hcl)
  rw [heq, ← hcluster]

/-- In an open intersection of discs, compact containment of the regularized
cluster implies compatibility without an admissibility hypothesis. -/
theorem regularizedFamily_closure_eq_clusterOn_of_disc_intersection
    {ι : Type*} {c : ι → ℂ} {r : ι → ℝ}
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ R : ℝ, 0 < R → VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hdisc : U = ⋂ i, ball (c i) (r i))
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U) :
    closure (Λ t) = closure (clusterOn μ U z t) := by
  exact regularizedFamily_closure_eq_clusterOn_of_boundary_of_volumeGrowth
    hμ hV hU hUb hz ht
    (tendsto_greenFunction_zero_of_enclosing_discs hz
      (exists_enclosing_disc_of_eq_iInter_ball hdisc)) hΛ hcl

#print axioms LaplacianLE.min_of_potential
#print axioms LaplacianLE.glue_of_open_cover
#print axioms exists_disc_supersolution_le_shift_of_compact_cluster
#print axioms leastSupersolutionOn_mem_of_compact_disc_cluster
#print axioms leastSupersolutionOn_mem_of_compact_disc_cluster_of_volumeGrowth
#print axioms clusterOn_eq_cluster_of_compact_disc_cluster_of_volumeGrowth
#print axioms regularizedFamily_closure_eq_clusterOn_of_boundary_of_volumeGrowth
#print axioms regularizedFamily_closure_eq_clusterOn_of_disc_intersection

end HarmonicBalls
