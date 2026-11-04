import HarmonicBalls.Proofs.Sec5.GeneralDomainMonotonicity

/-!
# Domain compatibility under Green-function boundary regularity

A compactly contained general-domain cluster can be compared with a disc
cluster by gluing its least supersolution to the disc obstacle. The
admissibility of the general-domain least supersolution and the continuous
harmonic extension of the Green-function difference are explicit hypotheses.
-/

namespace HarmonicBalls

open Filter MeasureTheory Metric Set
open scoped Topology

/-- If the general-domain cluster is compactly contained, its admissible least
supersolution glues to the disc obstacle and bounds the disc cluster. -/
theorem cluster_subset_clusterOn_of_green_difference
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) {r t : ℝ} {z : ℂ}
    (hsub : U ⊆ ball (0 : ℂ) r) (hz : z ∈ U)
    (hv : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    {h : ℂ → ℝ} (hc : ContinuousOn h (closure U))
    (hh : InnerProductSpace.HarmonicOnNhd h U)
    (hG : ∀ x ∈ closure U, x ≠ z →
      greenFunction U z x - greenFunction (ball 0 r) z x = h x)
    (hcl : closure (clusterOn μ U z t) ⊆ U) :
    cluster μ r z t ⊆ clusterOn μ U z t := by
  classical
  have hzball := hsub hz
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
  set w : ℂ → ℝ := fun y => if y ∈ U then v y + t * h y else -t * GR y
  have hwin : ∀ y ∈ U, w y = v y + t * h y := fun y hy => ite_eq_left_iff.mpr (fun hn => absurd hy hn)
  have hwout : ∀ y, y ∉ U → w y = -t * GR y := fun y hy => ite_eq_right_iff.mpr (fun hp => absurd hp hy)
  have hwO : ∀ y ∈ O, w y = -t * GR y := by
    intro y hyO
    by_cases hy : y ∈ U
    · have hyz : y ≠ z := fun e => hzO (e ▸ hyO)
      rw [hwin y hy, hvO y hy hyO, ← hG y (subset_closure hy) hyz]
      ring
    · exact hwout y hy
  have houtO : ∀ y, y ∉ U → y ∈ O := fun y hy h => hy (hcl h)
  have hGRc : ContinuousOn GR {z}ᶜ := continuousOn_greenFunction_ball hzball
  have hwc : ContinuousOn w (closedBall 0 r) := by
    intro x _
    by_cases hx : x ∈ U
    · have hev : w =ᶠ[𝓝 x] fun y => v y + t * h y := by
        filter_upwards [hU.mem_nhds hx] with y hy using hwin y hy
      have hn : closure U ∈ 𝓝 x := mem_of_superset (hU.mem_nhds hx) subset_closure
      have hcont : ContinuousAt (fun y => v y + t * h y) x :=
        (hv.1.continuousAt hn).add (continuousAt_const.mul (hc.continuousAt hn))
      exact (hcont.congr hev.symm).continuousWithinAt
    · have hxO := houtO x hx
      have hxz : x ≠ z := fun e => hx (e ▸ hz)
      have hev : w =ᶠ[𝓝 x] fun y => -t * GR y := by
        filter_upwards [hOo.mem_nhds hxO] with y hy using hwO y hy
      have hcont : ContinuousAt (fun y => -t * GR y) x :=
        continuousAt_const.mul (hGRc.continuousAt (isOpen_compl_singleton.mem_nhds hxz))
      exact (hcont.congr hev.symm).continuousWithinAt
  have hhL : HasLaplacian h 0 0 U := hasLaplacian_zero_of_harmonicOnNhd hU hh
  have hL₁ : LaplacianLE w μ U :=
    (hv.2.1.add_const_mul_of_hasLaplacian_zero hhL t).congr_eqOn hU.measurableSet
      fun y hy => (hwin y hy).symm
  have hL₂ : LaplacianLE w μ (ball 0 r ∩ O) :=
    (laplacianLE_neg_mul_greenFunction_of_notMem (t := t) hzball inter_subset_left
      fun he => hzO he.2).congr_eqOn (measurableSet_ball.inter hOo.measurableSet)
        fun y hy => (hwO y hy.2).symm
  have hunion : U ∪ (ball (0 : ℂ) r ∩ O) = ball 0 r := by
    ext y
    constructor
    · rintro (hy | hy)
      · exact hsub hy
      · exact hy.1
    · intro hy
      by_cases hyU : y ∈ U
      · exact Or.inl hyU
      · exact Or.inr ⟨hy, houtO y hyU⟩
  have hL : LaplacianLE w μ (ball 0 r) :=
    hunion ▸ LaplacianLE.union hU (isOpen_ball.inter hOo) hL₁ hL₂
  have hwS : w ∈ supersolutions μ r z t := by
    refine ⟨hwc, hL, fun y _ hyz => ?_⟩
    change -t * GR y ≤ w y
    by_cases hy : y ∈ U
    · rw [hwin y hy]
      have hbound := hv.2.2 y (subset_closure hy) hyz
      have he : t * h y = t * GU y - t * GR y := by
        rw [← hG y (subset_closure hy) hyz]
        ring
      linarith
    · rw [hwout y hy]
  intro x hx
  by_cases hxz : x = z
  · exact ⟨hxz ▸ hz, Or.inl hxz⟩
  have hle := leastSupersolution_le hwS (ball_subset_closedBall hx.1) hxz
  have hxpos := hx.2.resolve_left hxz
  by_cases hxU : x ∈ U
  · refine ⟨hxU, Or.inr ?_⟩
    rw [hwin x hxU] at hle
    have he : t * h x = t * GU x - t * GR x := by
      rw [← hG x (subset_closure hxU) hxz]
      ring
    change -t * GU x < v x
    linarith
  · rw [hwout x hxU] at hle
    exact False.elim (not_lt_of_ge hle hxpos)

/-- Under the same regularity and admissibility hypotheses, compact containment
of the general-domain cluster gives equality with the disc cluster. -/
theorem clusterOn_eq_cluster_of_green_difference
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U : Set ℂ}
    (hU : IsOpen U) {r βm βp : ℝ} (hr : 0 < r)
    (hV : VolumeGrowth μ r βm βp) (hsub : U ⊆ ball (0 : ℂ) r)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hv : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    {h : ℂ → ℝ} (hc : ContinuousOn h (closure U))
    (hh : InnerProductSpace.HarmonicOnNhd h U)
    (hG : ∀ x ∈ closure U, x ≠ z →
      greenFunction U z x - greenFunction (ball 0 r) z x = h x)
    (hcl : closure (clusterOn μ U z t) ⊆ U) :
    clusterOn μ U z t = cluster μ r z t :=
  Subset.antisymm
    (clusterOn_subset_cluster_of_green_difference hμ hU hr hV hsub hz ht hc hh hG)
    (cluster_subset_clusterOn_of_green_difference hU hsub hz hv hc hh hG hcl)


/-- The same equality follows if the disc cluster is compactly contained in
the smaller domain. -/
theorem clusterOn_eq_cluster_of_cluster_closure_subset
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U : Set ℂ}
    (hU : IsOpen U) {r βm βp : ℝ} (hr : 0 < r)
    (hV : VolumeGrowth μ r βm βp) (hsub : U ⊆ ball (0 : ℂ) r)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hv : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    {h : ℂ → ℝ} (hc : ContinuousOn h (closure U))
    (hh : InnerProductSpace.HarmonicOnNhd h U)
    (hG : ∀ x ∈ closure U, x ≠ z →
      greenFunction U z x - greenFunction (ball 0 r) z x = h x)
    (hcl : closure (cluster μ r z t) ⊆ U) :
    clusterOn μ U z t = cluster μ r z t := by
  apply clusterOn_eq_cluster_of_green_difference hμ hU hr hV hsub hz ht hv hc hh hG
  exact (closure_mono
    (clusterOn_subset_cluster_of_green_difference hμ hU hr hV hsub hz ht hc hh hG)).trans hcl

end HarmonicBalls
