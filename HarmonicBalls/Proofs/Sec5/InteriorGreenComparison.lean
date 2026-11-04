import HarmonicBalls.Proofs.Sec5.GeneralDomainCompatibility

/-! # General-domain comparison from interior Green regularity

The gluing interface stays away from the boundary when the general-domain
cluster is compactly contained. Therefore the comparison in this direction
needs Green-difference regularity only inside the domain. -/

namespace HarmonicBalls

open Filter MeasureTheory Metric Set
open scoped Topology

/-- The Green-function difference is only needed on an open neighborhood of
the closed general-domain cluster, allowing irregularities elsewhere in the domain. -/
theorem cluster_subset_clusterOn_of_local_green_difference
    {μ : Measure ℂ} {U V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U) {r t : ℝ} {z : ℂ}
    (hsub : U ⊆ ball (0 : ℂ) r) (hz : z ∈ U)
    (hv : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    {h : ℂ → ℝ} (hh : InnerProductSpace.HarmonicOnNhd h V)
    (hG : ∀ x ∈ V, x ≠ z →
      greenFunction U z x - greenFunction (ball 0 r) z x = h x)
    (hcl : closure (clusterOn μ U z t) ⊆ V) :
    cluster μ r z t ⊆ clusterOn μ U z t := by
  classical
  have hzball := hsub hz
  have hzV : z ∈ V := hcl (subset_closure ⟨hz, Or.inl rfl⟩)
  have hVball : V ⊆ ball (0 : ℂ) r := hVU.trans hsub
  set v := leastSupersolutionOn μ U z t
  set GU := greenFunction U z
  set GR := greenFunction (ball (0 : ℂ) r) z
  set O := (closure (clusterOn μ U z t))ᶜ
  have hOo : IsOpen O := isClosed_closure.isOpen_compl
  have hzO : z ∉ O := fun h => h (subset_closure ⟨hz, Or.inl rfl⟩)
  have hvO : ∀ y ∈ U, y ∈ O → v y = -t * GU y := by
    intro y hy hyO
    have hyz : y ≠ z := fun e => hzO (e ▸ hyO)
    have hn : ¬ -t * GU y < v y := fun hp => hyO (subset_closure ⟨hy, Or.inr hp⟩)
    exact le_antisymm (not_lt.mp hn) (hv.2.2 y (subset_closure hy) hyz)
  set w : ℂ → ℝ := fun y => if y ∈ V then v y + t * h y else -t * GR y
  have hwin : ∀ y ∈ V, w y = v y + t * h y := fun y hy => ite_eq_left_iff.mpr (fun hn => absurd hy hn)
  have hwout : ∀ y, y ∉ V → w y = -t * GR y := fun y hy => ite_eq_right_iff.mpr (fun hp => absurd hp hy)
  have hwO : ∀ y ∈ O, w y = -t * GR y := by
    intro y hyO
    by_cases hy : y ∈ V
    · have hyz : y ≠ z := fun e => hzO (e ▸ hyO)
      rw [hwin y hy, hvO y (hVU hy) hyO, ← hG y hy hyz]
      ring
    · exact hwout y hy
  have houtO : ∀ y, y ∉ V → y ∈ O := fun y hy h => hy (hcl h)
  have hGRc : ContinuousOn GR {z}ᶜ := continuousOn_greenFunction_ball hzball
  have hwc : ContinuousOn w (closedBall 0 r) := by
    intro x _
    by_cases hx : x ∈ V
    · have hev : w =ᶠ[𝓝 x] fun y => v y + t * h y := by
        filter_upwards [hV.mem_nhds hx] with y hy using hwin y hy
      have hn : closure U ∈ 𝓝 x := mem_of_superset (hV.mem_nhds hx) (fun _ hy => subset_closure (hVU hy))
      have hcont : ContinuousAt (fun y => v y + t * h y) x :=
        (hv.1.continuousAt hn).add (continuousAt_const.mul (hh.continuousOn.continuousAt (hV.mem_nhds hx)))
      exact (hcont.congr hev.symm).continuousWithinAt
    · have hxO := houtO x hx
      have hxz : x ≠ z := fun e => hx (e ▸ hzV)
      have hev : w =ᶠ[𝓝 x] fun y => -t * GR y := by
        filter_upwards [hOo.mem_nhds hxO] with y hy using hwO y hy
      have hcont : ContinuousAt (fun y => -t * GR y) x :=
        continuousAt_const.mul (hGRc.continuousAt (isOpen_compl_singleton.mem_nhds hxz))
      exact (hcont.congr hev.symm).continuousWithinAt
  have hhL : HasLaplacian h 0 0 V := hasLaplacian_zero_of_harmonicOnNhd hV hh
  have hL₁ : LaplacianLE w μ V :=
    ((hv.2.1.mono_set hVU).add_const_mul_of_hasLaplacian_zero hhL t).congr_eqOn hV.measurableSet
      fun y hy => (hwin y hy).symm
  have hL₂ : LaplacianLE w μ (ball 0 r ∩ O) :=
    (laplacianLE_neg_mul_greenFunction_of_notMem (t := t) hzball inter_subset_left
      fun he => hzO he.2).congr_eqOn (measurableSet_ball.inter hOo.measurableSet)
        fun y hy => (hwO y hy.2).symm
  have hunion : V ∪ (ball (0 : ℂ) r ∩ O) = ball 0 r := by
    ext y
    constructor
    · rintro (hy | hy)
      · exact hVball hy
      · exact hy.1
    · intro hy
      by_cases hyU : y ∈ V
      · exact Or.inl hyU
      · exact Or.inr ⟨hy, houtO y hyU⟩
  have hL : LaplacianLE w μ (ball 0 r) :=
    hunion ▸ LaplacianLE.union hV (isOpen_ball.inter hOo) hL₁ hL₂
  have hwS : w ∈ supersolutions μ r z t := by
    refine ⟨hwc, hL, fun y _ hyz => ?_⟩
    change -t * GR y ≤ w y
    by_cases hy : y ∈ V
    · rw [hwin y hy]
      have hbound := hv.2.2 y (subset_closure (hVU hy)) hyz
      have he : t * h y = t * GU y - t * GR y := by
        rw [← hG y hy hyz]
        ring
      linarith
    · rw [hwout y hy]
  intro x hx
  by_cases hxz : x = z
  · exact ⟨hxz ▸ hz, Or.inl hxz⟩
  have hle := leastSupersolution_le hwS (ball_subset_closedBall hx.1) hxz
  have hxpos := hx.2.resolve_left hxz
  by_cases hxU : x ∈ V
  · refine ⟨hVU hxU, Or.inr ?_⟩
    rw [hwin x hxU] at hle
    have he : t * h x = t * GU x - t * GR x := by
      rw [← hG x hxU hxz]
      ring
    change -t * GU x < v x
    linarith
  · rw [hwout x hxU] at hle
    exact False.elim (not_lt_of_ge hle hxpos)


/-- In particular, interior harmonicity on the entire domain suffices for
this direction of comparison, with no boundary Green regularity. -/
theorem cluster_subset_clusterOn_of_interior_green_difference
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) {r t : ℝ} {z : ℂ}
    (hsub : U ⊆ ball (0 : ℂ) r) (hz : z ∈ U)
    (hv : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    {h : ℂ → ℝ} (hh : InnerProductSpace.HarmonicOnNhd h U)
    (hG : ∀ x ∈ U, x ≠ z →
      greenFunction U z x - greenFunction (ball 0 r) z x = h x)
    (hcl : closure (clusterOn μ U z t) ⊆ U) :
    cluster μ r z t ⊆ clusterOn μ U z t :=
  cluster_subset_clusterOn_of_local_green_difference hU Subset.rfl hsub hz hv hh hG hcl

end HarmonicBalls
