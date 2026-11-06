import HarmonicBalls.Proofs.Sec5.PoleInfimumCharacterization
import HarmonicBalls.Proofs.Sec5.MinimumLaplacianGluing

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

/-- The shifted frozen infimum is nonnegative throughout the domain. -/
theorem shifted_leastSupersolutionOn_nonneg
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t) {x : ℂ} (hx : x ∈ U) :
    0 ≤ leastSupersolutionOn μ U z t x + greenPotentialBall μ R x := by
  have h : -greenPotentialBall μ R x ≤ leastSupersolutionOn μ U z t x := by
    change -greenPotentialBall μ R x ≤ sInf ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ U z t)
    apply le_csInf
    · exact ⟨0, 0, zero_mem_supersolutionsOn (isBounded_ball.subset hsub) ht, rfl⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact neg_greenPotentialBall_le_supersolutionOn hμ hR hV hU hsub hz hw hx
  linarith

/-- The regularization agrees with the shifted frozen infimum at every
interior off-pole contact point. -/
theorem lscRegularization_shifted_infimum_eq_of_contact
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t) {x : ℂ}
    (hx : x ∈ U) (hxz : x ≠ z)
    (hcontact : leastSupersolutionOn μ U z t x = -t * greenFunction U z x) :
    lscRegularization U (fun y => leastSupersolutionOn μ U z t y +
      greenPotentialBall μ R y) x =
      leastSupersolutionOn μ U z t x + greenPotentialBall μ R x := by
  let f := fun y => leastSupersolutionOn μ U z t y + greenPotentialBall μ R y
  have hnonneg : ∀ y ∈ U, 0 ≤ f y := fun y hy =>
    shifted_leastSupersolutionOn_nonneg hμ hR hV hU hsub hz ht hy
  have hfc : ContinuousAt f x :=
    (continuousAt_leastSupersolutionOn_of_contact hμ hR hV hU hsub hz ht hx hxz hcontact).add
      (((enclosingDisc_potential_shift_on_domain hμ hR hV hsub).1.mono subset_closure).continuousAt
        (hU.mem_nhds hx))
  apply le_antisymm (lscRegularization_le hnonneg hx)
  apply le_lscRegularization hnonneg hx
  intro ε hε
  filter_upwards [hfc.eventually (Ioi_mem_nhds (show f x - ε < f x by linarith))] with y hy _
  exact hy.le

#print axioms shifted_leastSupersolutionOn_nonneg
#print axioms lscRegularization_shifted_infimum_eq_of_contact

/-- Away from the pole, the regularized shifted infimum still dominates the
shifted Green obstacle. -/
theorem shifted_obstacle_le_lscRegularization_shifted_infimum
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t) {x : ℂ}
    (hx : x ∈ U) (hxz : x ≠ z) :
    -t * greenFunction U z x + greenPotentialBall μ R x ≤
      lscRegularization U (fun y => leastSupersolutionOn μ U z t y +
        greenPotentialBall μ R y) x := by
  let f := fun y => leastSupersolutionOn μ U z t y + greenPotentialBall μ R y
  let β := fun y => -t * greenFunction U z y + greenPotentialBall μ R y
  have hnonneg : ∀ y ∈ U, 0 ≤ f y := fun y hy =>
    shifted_leastSupersolutionOn_nonneg hμ hR hV hU hsub hz ht hy
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
  have hβc : ContinuousAt β x := (hGc.const_mul (-t)).add
    (((enclosingDisc_potential_shift_on_domain hμ hR hV hsub).1.mono subset_closure).continuousAt
      (hU.mem_nhds hx))
  apply le_lscRegularization hnonneg hx
  intro ε hε
  filter_upwards [hU.mem_nhds hx, isOpen_compl_singleton.mem_nhds hxz,
    hβc.eventually (Ioi_mem_nhds (show β x - ε < β x by linarith))] with y hy hyz hβy _
  have hb := (isGLB_supersolutionsOn_values_of_ne_pole (μ := μ)
    (isBounded_ball.subset hsub) ht (subset_closure hy) hyz).2
    (by rintro _ ⟨w, hw, rfl⟩; exact hw.2.2 y (subset_closure hy) hyz)
  dsimp [β, f] at *
  linarith

#print axioms shifted_obstacle_le_lscRegularization_shifted_infimum

/-- The pointwise minimum of two general-domain competitors is again a
competitor. -/
theorem min_mem_supersolutionsOn
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} {t : ℝ} {w₁ w₂ : ℂ → ℝ}
    (h₁ : w₁ ∈ supersolutionsOn μ U z t) (h₂ : w₂ ∈ supersolutionsOn μ U z t) :
    (fun x => min (w₁ x) (w₂ x)) ∈ supersolutionsOn μ U z t := by
  have hq := enclosingDisc_potential_shift_on_domain hμ hR hV hsub
  refine ⟨(fun x hx => (h₁.1 x hx).min (h₂.1 x hx)), ?_, ?_⟩
  · exact h₁.2.1.min_of_potential hμ hU (h₁.1.mono subset_closure)
      (h₂.1.mono subset_closure) (hq.1.mono subset_closure) hq.2 h₂.2.1
  · intro x hx hxz
    exact le_min (h₁.2.2 x hx hxz) (h₂.2.2 x hx hxz)

#print axioms min_mem_supersolutionsOn

/-- The lower semicontinuous regularization of the shifted frozen infimum is
superharmonic, even when the domain boundary is irregular. -/
theorem isSuperharmonicOn_lscRegularization_shifted_infimum
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t) :
    IsSuperharmonicOn U (lscRegularization U
      (fun x => leastSupersolutionOn μ U z t x + greenPotentialBall μ R x)) := by
  let q := greenPotentialBall μ R
  let f := fun x => leastSupersolutionOn μ U z t x + q x
  let F := (fun w : ℂ → ℝ => fun x => w x + q x) '' supersolutionsOn μ U z t
  have hw0 : (0 : ℂ → ℝ) ∈ supersolutionsOn μ U z t :=
    zero_mem_supersolutionsOn (isBounded_ball.subset hsub) ht
  have hmem : (fun x => (0 : ℂ → ℝ) x + q x) ∈ F := ⟨0, hw0, rfl⟩
  have hfs : ∀ g ∈ F, IsSuperharmonicOn U g := by
    rintro g ⟨w, hw, rfl⟩
    exact (shifted_supersolution_mem_nonnegativeSuperharmonicMajorants
      hμ hR hV hU hsub hz hw).1
  have hle : ∀ g ∈ F, ∀ x ∈ U, f x ≤ g x := by
    rintro g ⟨w, hw, rfl⟩ x hx
    dsimp [f]
    have h := leastSupersolutionOn_le_of_mem_interior hμ hR hV hU hsub hz hx hw
    linarith
  have hge : ∀ x ∈ U, ∀ a : ℝ, (∀ g ∈ F, a ≤ g x) → a ≤ f x := by
    intro x hx a ha
    have he : a - q x ≤ leastSupersolutionOn μ U z t x := by
      change a - q x ≤ sInf ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ U z t)
      apply le_csInf
      · exact ⟨0, 0, hw0, rfl⟩
      · rintro _ ⟨w, hw, rfl⟩
        have h := ha (fun y => w y + q y) ⟨w, hw, rfl⟩
        linarith
    dsimp [f]
    linarith
  have hnonneg : ∀ x ∈ U, 0 ≤ f x := by
    intro x hx
    apply hge x hx 0
    rintro g ⟨w, hw, rfl⟩
    exact (shifted_supersolution_mem_nonnegativeSuperharmonicMajorants
      hμ hR hV hU hsub hz hw).2.1 x hx
  exact isSuperharmonicOn_lscRegularization hU hfs hmem hle hge hnonneg

/-- If the shifted frozen infimum is lower semicontinuous, then the
regularization theorem makes it superharmonic. -/
theorem isSuperharmonicOn_shifted_infimum_of_lowerSemicontinuous
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t)
    (hlsc : LowerSemicontinuousOn (fun x => leastSupersolutionOn μ U z t x +
      greenPotentialBall μ R x) U) :
    IsSuperharmonicOn U (fun x => leastSupersolutionOn μ U z t x +
      greenPotentialBall μ R x) := by
  let f := fun x => leastSupersolutionOn μ U z t x + greenPotentialBall μ R x
  have hnonneg : ∀ y ∈ U, 0 ≤ f y := fun y hy =>
    shifted_leastSupersolutionOn_nonneg hμ hR hV hU hsub hz ht hy
  have heq : EqOn (lscRegularization U f) f U := by
    intro x hx
    apply le_antisymm (lscRegularization_le hnonneg hx)
    apply le_lscRegularization hnonneg hx
    intro ε hε
    have h := hlsc x hx (f x - ε) (by linarith)
    rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hx)] at h
    filter_upwards [h] with y hy _
    exact hy.le
  exact (isSuperharmonicOn_lscRegularization_shifted_infimum hμ hR hV hU hsub hz ht).congr heq

#print axioms isSuperharmonicOn_shifted_infimum_of_lowerSemicontinuous

#print axioms isSuperharmonicOn_lscRegularization_shifted_infimum

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
