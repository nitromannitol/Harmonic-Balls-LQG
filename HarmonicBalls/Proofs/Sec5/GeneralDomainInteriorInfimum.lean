import HarmonicBalls.Proofs.Sec5.PoleInfimumCharacterization

/-! # Interior properties of the general-domain infimum

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open Filter MeasureTheory Metric Set
open scoped Topology

/-- Values of all general-domain competitors have a common lower bound at each
interior point, including the pole. -/
theorem bddBelow_supersolutionsOn_values_interior
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} {x : ℂ} (hx : x ∈ U) :
    BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ U z t) := by
  refine ⟨-greenPotentialBall μ R x, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact neg_greenPotentialBall_le_supersolutionOn hμ hR hV hU hsub hz hw hx

/-- Every competitor dominates the actual infimum at each interior point. -/
theorem leastSupersolutionOn_le_of_mem_interior
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} {x : ℂ} (hx : x ∈ U)
    {w : ℂ → ℝ} (hw : w ∈ supersolutionsOn μ U z t) :
    leastSupersolutionOn μ U z t x ≤ w x := by
  exact csInf_le (bddBelow_supersolutionsOn_values_interior hμ hR hV hU hsub hz hx)
    ⟨w, hw, rfl⟩

/-- The frozen infimum is upper semicontinuous in the interior, also at the
pole. This uses the continuous competitors and no boundary regularity. -/
theorem upperSemicontinuousAt_leastSupersolutionOn_interior
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t) {x : ℂ} (hx : x ∈ U) :
    UpperSemicontinuousAt (leastSupersolutionOn μ U z t) x := by
  intro a ha
  obtain ⟨w, hw, hwa⟩ := exists_supersolutionOn_lt_of_leastSupersolutionOn_lt
    (isBounded_ball.subset hsub) ht ha
  have hwc : ContinuousAt w x := (hw.1.mono subset_closure).continuousAt (hU.mem_nhds hx)
  filter_upwards [hU.mem_nhds hx, hwc.eventually (Iio_mem_nhds hwa)] with y hy hwy
  exact (leastSupersolutionOn_le_of_mem_interior hμ hR hV hU hsub hz hy hw).trans_lt hwy

/-- At an interior contact point, continuity follows from the continuous
obstacle and upper semicontinuity of the infimum. -/
theorem continuousAt_leastSupersolutionOn_of_contact
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t) {x : ℂ}
    (hx : x ∈ U) (hxz : x ≠ z)
    (hcontact : leastSupersolutionOn μ U z t x = -t * greenFunction U z x) :
    ContinuousAt (leastSupersolutionOn μ U z t) x := by
  obtain ⟨h, hh, hG⟩ :=
    exists_harmonicOnNhd_greenFunction_difference hU (isBounded_ball.subset hsub) hsub hz
  have hGc : ContinuousAt (greenFunction U z) x := by
    have hc := ((hh x hx).1.continuousAt).add
      ((continuousOn_greenFunction_ball (hsub hz)).continuousAt
        (isOpen_compl_singleton.mem_nhds hxz))
    apply hc.congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx, isOpen_compl_singleton.mem_nhds hxz] with y hy hyz
    have he := hG y hy hyz
    change greenFunction U z y = h y + greenFunction (ball 0 R) z y
    linarith
  have hlsc : LowerSemicontinuousAt (leastSupersolutionOn μ U z t) x := by
    intro a ha
    have ha' : a < -t * greenFunction U z x := by rwa [← hcontact]
    filter_upwards [hU.mem_nhds hx, isOpen_compl_singleton.mem_nhds hxz,
      (hGc.const_mul (-t)).eventually (Ioi_mem_nhds ha')] with y hy hyz hya
    have hb := (isGLB_supersolutionsOn_values_of_ne_pole (μ := μ)
      (isBounded_ball.subset hsub) ht (subset_closure hy) hyz).2
      (by rintro _ ⟨w, hw, rfl⟩; exact hw.2.2 y (subset_closure hy) hyz)
    exact hya.trans_le hb
  exact continuousAt_iff_lower_upperSemicontinuousAt.2
    ⟨hlsc, upperSemicontinuousAt_leastSupersolutionOn_interior hμ hR hV hU hsub hz ht hx⟩

/-- Superharmonicity of the shifted frozen infimum is sufficient for both
interior conclusions. This isolates the local envelope step. -/
theorem interior_regularity_of_shifted_superharmonic
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t)
    (hsh : IsSuperharmonicOn U (fun x => leastSupersolutionOn μ U z t x +
      greenPotentialBall μ R x)) :
    ContinuousOn (leastSupersolutionOn μ U z t) U ∧
      LaplacianLE (leastSupersolutionOn μ U z t) μ U := by
  let v := leastSupersolutionOn μ U z t
  let q := greenPotentialBall μ R
  have hq := enclosingDisc_potential_shift_on_domain hμ hR hV hsub
  have hfc : ContinuousOn (fun x => v x + q x) U := by
    intro x hx
    have hl : LowerSemicontinuousAt (fun x => v x + q x) x := by
      intro a ha
      have he := hsh.1 x hx a ha
      rwa [nhdsWithin_eq_nhds.2 (hU.mem_nhds hx)] at he
    have hu : UpperSemicontinuousAt (fun x => v x + q x) x :=
      (upperSemicontinuousAt_leastSupersolutionOn_interior hμ hR hV hU hsub hz ht hx).add
        ((hq.1.mono subset_closure).continuousAt (hU.mem_nhds hx)).upperSemicontinuousAt
    exact (continuousAt_iff_lower_upperSemicontinuousAt.2 ⟨hl, hu⟩).continuousWithinAt
  have hvc : ContinuousOn v U := by
    have hc := hfc.sub (hq.1.mono subset_closure)
    have heq : (fun x => (v x + q x) - q x) = v := by
      funext x
      exact add_sub_cancel_right _ _
    change ContinuousOn (fun x => (v x + q x) - q x) U at hc
    rwa [heq] at hc
  refine ⟨hvc, ?_⟩
  apply (laplacianLE_iff_add_potential hμ hq.2).mpr
  exact laplacianLEOfSuperharmonicStep_holds U _ hU hfc hsh

#print axioms interior_regularity_of_shifted_superharmonic

#print axioms continuousAt_leastSupersolutionOn_of_contact

#print axioms bddBelow_supersolutionsOn_values_interior
#print axioms leastSupersolutionOn_le_of_mem_interior
#print axioms upperSemicontinuousAt_leastSupersolutionOn_interior

end HarmonicBalls
