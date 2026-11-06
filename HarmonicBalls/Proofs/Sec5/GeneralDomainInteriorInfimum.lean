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

/-- The Poisson kernel admits the classical lower Harnack bound in a disc. -/
theorem poissonKernel_ge_harnack_factor {c x ζ : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hx : x ∈ ball c ρ) (hζ : ζ ∈ sphere c ρ) :
    (ρ - ‖x - c‖) / (ρ + ‖x - c‖) ≤ poissonKernel c x ζ := by
  have hζc : ‖ζ - c‖ = ρ := by simpa [dist_eq_norm] using hζ
  have hxc : ‖x - c‖ < ρ := by simpa [dist_eq_norm] using hx
  have hnorm : ‖ζ - x‖ ≤ ρ + ‖x - c‖ := by
    have hh := dist_triangle ζ c x
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, hζc, norm_sub_rev c x] at hh
    exact hh
  have hne : ζ - x ≠ 0 := by
    intro he
    have heq : ζ = x := sub_eq_zero.mp he
    rw [heq] at hζc
    linarith
  have hden : 0 < ‖ζ - x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hsum : 0 < ρ + ‖x - c‖ := by positivity
  have hfac : 0 ≤ ρ - ‖x - c‖ := by linarith
  have hsq : ‖ζ - x‖ ^ 2 ≤ (ρ + ‖x - c‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [poissonKernel_def]
  have he : ζ - c - (x - c) = ζ - x := by ring
  rw [hζc, he]
  apply (div_le_div_iff₀ hsum hden).2
  have hh := mul_le_mul_of_nonneg_left hsq hfac
  nlinarith [sq_nonneg (ρ + ‖x - c‖)]

#print axioms poissonKernel_ge_harnack_factor

/-- Harnack's lower estimate for a Poisson integral whose boundary values
are bounded below by a constant. -/
theorem discPoissonIntegral_sub_lower_bound {φ : ℂ → ℝ} {c x : ℂ} {ρ L : ℝ}
    (hρ : 0 < ρ) (hφ : CircleIntegrable φ c ρ)
    (hbound : ∀ ζ ∈ sphere c ρ, L ≤ φ ζ) (hx : x ∈ ball c ρ) :
    ((ρ - ‖x - c‖) / (ρ + ‖x - c‖)) * (discPoissonIntegral φ c ρ c - L) ≤
      discPoissonIntegral φ c ρ x - L := by
  let ψ : ℂ → ℝ := fun ζ => φ ζ - L
  let k := (ρ - ‖x - c‖) / (ρ + ‖x - c‖)
  have hψ : CircleIntegrable ψ c ρ := hφ.sub continuousOn_const.circleIntegrable'
  have hki : CircleIntegrable (fun ζ => k * ψ ζ) c ρ := by
    change CircleIntegrable (k • ψ) c ρ
    exact CircleIntegrable.const_smul hψ
  have hPi : CircleIntegrable (poissonKernel c x • ψ) c ρ := CircleIntegrable.poissonKernel_smul hψ hx
  have hle : Real.circleAverage (fun ζ => k * ψ ζ) c ρ ≤ discPoissonIntegral ψ c ρ x := by
    apply Real.circleAverage_mono hki hPi
    intro ζ hζ
    rw [abs_of_pos hρ] at hζ
    change k * ψ ζ ≤ poissonKernel c x ζ * ψ ζ
    exact mul_le_mul_of_nonneg_right (poissonKernel_ge_harnack_factor hρ hx hζ)
      (sub_nonneg.mpr (hbound ζ hζ))
  have havg : Real.circleAverage (fun ζ => k * ψ ζ) c ρ = k * discPoissonIntegral ψ c ρ c := by
    rw [show (fun ζ => k * ψ ζ) = k • ψ by ext ζ; simp]
    rw [Real.circleAverage_smul, smul_eq_mul, discPoissonIntegral_center hρ.ne']
  have hdiff (y : ℂ) (hy : y ∈ ball c ρ) :
      discPoissonIntegral ψ c ρ y = discPoissonIntegral φ c ρ y - L := by
    have he : (poissonKernel c y • ψ) =
        (poissonKernel c y • φ) - (L • poissonKernel c y) := by
      ext ζ
      change poissonKernel c y ζ * (φ ζ - L) = poissonKernel c y ζ * φ ζ - L * poissonKernel c y ζ
      ring
    change Real.circleAverage (poissonKernel c y • ψ) c ρ = _
    rw [he]
    change Real.circleAverage (fun ζ => (poissonKernel c y • φ) ζ - (L • poissonKernel c y) ζ) c ρ = _
    rw [Real.circleAverage_fun_sub (CircleIntegrable.poissonKernel_smul hφ hy)
      (CircleIntegrable.const_smul (a := L) (circleIntegrable_poissonKernel hy)), Real.circleAverage_smul,
      circleAverage_poissonKernel hy]
    simp only [smul_eq_mul, mul_one, discPoissonIntegral]
  rw [havg, hdiff c (mem_ball_self hρ), hdiff x hx] at hle
  exact hle

#print axioms discPoissonIntegral_sub_lower_bound

/-- A Poisson modification of a shifted competitor remains admissible when
a constant majorizes the obstacle in the disc and is below its boundary data. -/
theorem exists_poisson_modified_supersolutionOn
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} {w : ℂ → ℝ}
    (hw : w ∈ supersolutionsOn μ U z t) {c : ℂ} {ρ L : ℝ}
    (hρ : 0 < ρ) (hdisc : closedBall c ρ ⊆ U)
    (hboundary : ∀ y ∈ sphere c ρ, L ≤ w y + greenPotentialBall μ R y)
    (hobs : ∀ y ∈ ball c ρ, y ≠ z →
      -t * greenFunction U z y + greenPotentialBall μ R y ≤ L) :
    ∃ v ∈ supersolutionsOn μ U z t,
      EqOn (fun y => v y + greenPotentialBall μ R y)
        (discPoissonIntegral (fun y => w y + greenPotentialBall μ R y) c ρ) (ball c ρ) := by
  let q := greenPotentialBall μ R
  let f := fun y => w y + q y
  let g := poissonModification f c ρ
  let p := fun y => g y - q y
  let O := (closedBall c ρ)ᶜ
  have hq := enclosingDisc_potential_shift_on_domain hμ hR hV hsub
  have hfc : ContinuousOn f U := (hw.1.mono subset_closure).add (hq.1.mono subset_closure)
  have hfsh : IsSuperharmonicOn U f :=
    (shifted_supersolution_mem_nonnegativeSuperharmonicMajorants hμ hR hV hU hsub hz hw).1
  have hgsh : IsSuperharmonicOn U g := (isSuperharmonicOn_poissonModification hU hfsh hρ hdisc).1
  have hD : IsSweepDisc U c ρ := ⟨hρ, hdisc⟩
  have heq : discSweep U c ρ f = g := by
    funext y
    change discSweep U c ρ f y = poissonModification f c ρ y
    by_cases hy : y ∈ ball c ρ
    · rw [discSweep_of_mem hD hy, poissonModification_of_mem hy]
    · rw [discSweep_of_not (fun h => hy h.2), poissonModification_of_notMem hy]
  have hgc : ContinuousOn g U := heq ▸ continuousOn_discSweep hU hfc
  have hpc : ContinuousOn p U := hgc.sub (hq.1.mono subset_closure)
  have hL : LaplacianLE p μ U := by
    apply (laplacianLE_iff_add_potential hμ hq.2).mpr
    have he : (fun y => p y + q y) = g := by funext y; dsimp [p]; ring
    rw [he]
    exact laplacianLEOfSuperharmonicStep_holds U g hU hgc hgsh
  have hO : IsOpen O := isClosed_closedBall.isOpen_compl
  have hcover : closure U ⊆ U ∪ O := by
    intro y hy
    by_cases hyU : y ∈ U
    · exact Or.inl hyU
    · exact Or.inr (fun hyc => hyU (hdisc hyc))
  have hagree : EqOn p w (U ∩ O) := by
    intro y hy
    have hyb : y ∉ ball c ρ := fun h => hy.2 (ball_subset_closedBall h)
    dsimp [p, g, f]
    rw [poissonModification_of_notMem hyb]
    ring
  obtain ⟨v, hvc, hvL, hvU, hvO⟩ := LaplacianLE.glue_of_open_cover
    hU hU hO (Subset.refl U) hcover hpc hw.1 hL hw.2.1 hagree
  have hui : CircleIntegrable f c ρ := hD.circleIntegrable hfc
  have hvobs : ∀ y ∈ closure U, y ≠ z → -t * greenFunction U z y ≤ v y := by
    intro y hy hyz
    by_cases hyb : y ∈ ball c ρ
    · have hyU := hdisc (ball_subset_closedBall hyb)
      rw [hvU hyU]
      have hp : p y = discPoissonIntegral f c ρ y - q y := by
        dsimp [p, g]; rw [poissonModification_of_mem hyb]
      rw [hp]
      have hl := le_discPoissonIntegral hui hyb hboundary
      have ho := hobs y hyb hyz
      dsimp [q] at *
      linarith
    · by_cases hyU : y ∈ U
      · rw [hvU hyU]
        have hp : p y = w y := by
          dsimp [p, g, f]; rw [poissonModification_of_notMem hyb]; ring
        rw [hp]
        exact hw.2.2 y hy hyz
      · have hyO : y ∈ O := fun hyc => hyU (hdisc hyc)
        rw [hvO hyO]
        exact hw.2.2 y hy hyz
  refine ⟨v, ⟨hvc, hvL, hvobs⟩, ?_⟩
  intro y hy
  have hyU := hdisc (ball_subset_closedBall hy)
  change v y + q y = discPoissonIntegral f c ρ y
  rw [hvU hyU]
  dsimp [p, g]
  rw [poissonModification_of_mem hy]
  ring

#print axioms exists_poisson_modified_supersolutionOn

/-- On a disc with a constant barrier, the shifted frozen infimum is the
greatest lower bound of the Poisson integrals of shifted competitors. -/
theorem isGLB_poissonIntegrals_shifted_supersolutionsOn
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t) {c : ℂ} {ρ L : ℝ}
    (hρ : 0 < ρ) (hdisc : closedBall c ρ ⊆ U)
    (hboundary : ∀ y ∈ sphere c ρ,
      L ≤ leastSupersolutionOn μ U z t y + greenPotentialBall μ R y)
    (hobs : ∀ y ∈ ball c ρ, y ≠ z →
      -t * greenFunction U z y + greenPotentialBall μ R y ≤ L)
    {x : ℂ} (hx : x ∈ ball c ρ) :
    IsGLB ((fun w : ℂ → ℝ => discPoissonIntegral
      (fun y => w y + greenPotentialBall μ R y) c ρ x) '' supersolutionsOn μ U z t)
      (leastSupersolutionOn μ U z t x + greenPotentialBall μ R x) := by
  let q := greenPotentialBall μ R
  let f := fun y => leastSupersolutionOn μ U z t y + q y
  have hxU : x ∈ U := hdisc (ball_subset_closedBall hx)
  have hb (w : ℂ → ℝ) (hw : w ∈ supersolutionsOn μ U z t) :
      ∀ y ∈ sphere c ρ, L ≤ w y + q y := by
    intro y hy
    have hyU := hdisc (sphere_subset_closedBall hy)
    have hle := leastSupersolutionOn_le_of_mem_interior hμ hR hV hU hsub hz hyU hw
    have h := hboundary y hy
    dsimp [q] at *
    linarith
  constructor
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨v, hv, hvP⟩ := exists_poisson_modified_supersolutionOn hμ hR hV hU hsub hz
      hw hρ hdisc (hb w hw) hobs
    have hle := leastSupersolutionOn_le_of_mem_interior hμ hR hV hU hsub hz hxU hv
    have he := hvP hx
    dsimp [q] at *
    linarith
  · intro a ha
    have ha' : a - q x ≤ leastSupersolutionOn μ U z t x := by
      change a - q x ≤ sInf ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ U z t)
      apply le_csInf
      · exact ⟨0, 0, zero_mem_supersolutionsOn (isBounded_ball.subset hsub) ht, rfl⟩
      · rintro _ ⟨w, hw, rfl⟩
        let g := fun y => w y + q y
        have hg : IsSuperharmonicOn U g :=
          (shifted_supersolution_mem_nonnegativeSuperharmonicMajorants hμ hR hV hU hsub hz hw).1
        have hgc : ContinuousOn g U := (hw.1.mono subset_closure).add
          ((enclosingDisc_potential_shift_on_domain hμ hR hV hsub).1.mono subset_closure)
        have hgi : CircleIntegrable g c ρ := (show IsSweepDisc U c ρ from ⟨hρ, hdisc⟩).circleIntegrable hgc
        have hP := discPoissonIntegral_le hg.1 (hg.localSuperMean hU) hρ hdisc hgi x hx
        have h := ha ⟨w, hw, rfl⟩
        dsimp [g] at hP
        linarith
    change a ≤ leastSupersolutionOn μ U z t x + q x
    linarith

#print axioms isGLB_poissonIntegrals_shifted_supersolutionsOn

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

/-- Strict separation of the regularized envelope from the obstacle gives a
constant barrier on a sufficiently small disc. -/
theorem exists_constant_barrier_of_strict_regularized_noncontact
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t) {x : ℂ}
    (hx : x ∈ U) (hxz : x ≠ z)
    (hstrict : -t * greenFunction U z x + greenPotentialBall μ R x <
      lscRegularization U (fun y => leastSupersolutionOn μ U z t y +
        greenPotentialBall μ R y) x) :
    ∃ ρ L : ℝ, 0 < ρ ∧ closedBall x ρ ⊆ U ∧
      (∀ y ∈ sphere x ρ, L ≤ leastSupersolutionOn μ U z t y + greenPotentialBall μ R y) ∧
      ∀ y ∈ ball x ρ, y ≠ z → -t * greenFunction U z y + greenPotentialBall μ R y ≤ L := by
  let f := fun y => leastSupersolutionOn μ U z t y + greenPotentialBall μ R y
  let β := fun y => -t * greenFunction U z y + greenPotentialBall μ R y
  let g := lscRegularization U f
  let L := (β x + g x) / 2
  have hβL : β x < L := by dsimp [L]; linarith
  have hLg : L < g x := by dsimp [L]; linarith
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
  have hg := (isSuperharmonicOn_lscRegularization_shifted_infimum hμ hR hV hU hsub hz ht).1 x hx L hLg
  rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hx)] at hg
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ U ∧ β y < L ∧ L < g y := by
    filter_upwards [hU.mem_nhds hx, hβc.eventually (Iio_mem_nhds hβL), hg] with y hy hby hgy
    exact ⟨hy, hby, hgy⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  let ρ := δ / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hcb : closedBall x ρ ⊆ ball x δ := closedBall_subset_ball (by dsimp [ρ]; linarith)
  refine ⟨ρ, L, hρ, fun y hy => (hδsub (hcb hy)).1, ?_, ?_⟩
  · intro y hy
    have hy' := hδsub (hcb (sphere_subset_closedBall hy))
    exact hy'.2.2.le.trans (lscRegularization_le hnonneg hy'.1)
  · intro y hy _
    exact (hδsub (hcb (ball_subset_closedBall hy))).2.1.le

#print axioms exists_constant_barrier_of_strict_regularized_noncontact

/-- The shifted obstacle tends to minus infinity at the pole, so a constant
barrier exists there without assuming regularity of the infimum. -/
theorem exists_constant_barrier_at_pole
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) :
    ∃ ρ L : ℝ, 0 < ρ ∧ closedBall z ρ ⊆ U ∧
      (∀ y ∈ sphere z ρ, L ≤ leastSupersolutionOn μ U z t y + greenPotentialBall μ R y) ∧
      ∀ y ∈ ball z ρ, y ≠ z → -t * greenFunction U z y + greenPotentialBall μ R y ≤ L := by
  have hbot := (tendsto_greenRegular_shifted_obstacle_atBot hμ hR hV hU hsub hz ht).eventually
    (eventually_lt_atBot (0 : ℝ))
  rw [eventually_nhdsWithin_iff] at hbot
  have hnear : ∀ᶠ y in 𝓝 z, y ∈ U ∧
      (y ≠ z → -t * greenFunction U z y + greenPotentialBall μ R y < 0) := by
    filter_upwards [hU.mem_nhds hz, hbot] with y hy hyb
    exact ⟨hy, hyb⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  let ρ := δ / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hcb : closedBall z ρ ⊆ ball z δ := closedBall_subset_ball (by dsimp [ρ]; linarith)
  refine ⟨ρ, 0, hρ, fun y hy => (hδsub (hcb hy)).1, ?_, ?_⟩
  · intro y hy
    exact shifted_leastSupersolutionOn_nonneg hμ hR hV hU hsub hz ht.le
      (hδsub (hcb (sphere_subset_closedBall hy))).1
  · intro y hy hyz
    exact ((hδsub (hcb (ball_subset_closedBall hy))).2 hyz).le

#print axioms exists_constant_barrier_at_pole

/-- The shifted frozen infimum has a Poisson-integral representation on a
small disc about the pole. -/
theorem exists_poisson_infimum_disc_at_pole
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) :
    ∃ ρ : ℝ, 0 < ρ ∧ closedBall z ρ ⊆ U ∧ ∀ x ∈ ball z ρ,
      IsGLB ((fun w : ℂ → ℝ => discPoissonIntegral
        (fun y => w y + greenPotentialBall μ R y) z ρ x) '' supersolutionsOn μ U z t)
        (leastSupersolutionOn μ U z t x + greenPotentialBall μ R x) := by
  obtain ⟨ρ, L, hρ, hdisc, hb, ho⟩ := exists_constant_barrier_at_pole hμ hR hV hU hsub hz ht
  exact ⟨ρ, hρ, hdisc, fun x hx =>
    isGLB_poissonIntegrals_shifted_supersolutionsOn hμ hR hV hU hsub hz ht.le hρ hdisc hb ho hx⟩

#print axioms exists_poisson_infimum_disc_at_pole

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

/-- A constant barrier gives continuity of the shifted infimum at the centre
of a disc, by the Harnack inequality for its Poisson modifications. -/
theorem continuousAt_shifted_infimum_of_constant_barrier
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t) {c : ℂ} {ρ L : ℝ}
    (hρ : 0 < ρ) (hdisc : closedBall c ρ ⊆ U)
    (hb : ∀ y ∈ sphere c ρ, L ≤ leastSupersolutionOn μ U z t y + greenPotentialBall μ R y)
    (ho : ∀ y ∈ ball c ρ, y ≠ z →
      -t * greenFunction U z y + greenPotentialBall μ R y ≤ L) :
    ContinuousAt (fun y => leastSupersolutionOn μ U z t y + greenPotentialBall μ R y) c := by
  let q := greenPotentialBall μ R
  let f := fun y => leastSupersolutionOn μ U z t y + q y
  have hcU : c ∈ U := hdisc (mem_closedBall_self hρ.le)
  have hc := isGLB_poissonIntegrals_shifted_supersolutionsOn hμ hR hV hU hsub hz ht
    hρ hdisc hb ho (mem_ball_self hρ)
  let lo := fun y : ℂ => L + ((ρ - ‖y - c‖) / (ρ + ‖y - c‖)) * (f c - L)
  have hlo : ContinuousAt lo c := by
    dsimp [lo]
    fun_prop (disch := positivity)
  have hloc : lo c = f c := by simp [lo, hρ.ne']
  have hbound : ∀ y ∈ ball c ρ, lo y ≤ f y := by
    intro y hy
    have hg := isGLB_poissonIntegrals_shifted_supersolutionsOn hμ hR hV hU hsub hz ht
      hρ hdisc hb ho hy
    apply hg.2
    rintro _ ⟨w, hw, rfl⟩
    have hφ : CircleIntegrable (fun y => w y + q y) c ρ :=
      (show IsSweepDisc U c ρ from ⟨hρ, hdisc⟩).circleIntegrable
        ((hw.1.mono subset_closure).add
          ((enclosingDisc_potential_shift_on_domain hμ hR hV hsub).1.mono subset_closure))
    have hwb : ∀ y ∈ sphere c ρ, L ≤ w y + q y := by
      intro y hy'
      have hle := leastSupersolutionOn_le_of_mem_interior hμ hR hV hU hsub hz
        (hdisc (sphere_subset_closedBall hy')) hw
      have := hb y hy'
      dsimp [q] at *
      linarith
    have hp := discPoissonIntegral_sub_lower_bound hρ hφ hwb hy
    have hcenter := hc.1 ⟨w, hw, rfl⟩
    have hk : 0 ≤ (ρ - ‖y - c‖) / (ρ + ‖y - c‖) := by
      apply div_nonneg
      · have := (mem_ball.mp hy); rw [dist_eq_norm] at this; linarith
      · positivity
    have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hcenter L) hk
    dsimp [lo, f, q] at *
    linarith
  have hl : LowerSemicontinuousAt f c := by
    intro a ha
    have ha' : a < lo c := by rwa [hloc]
    filter_upwards [hlo.eventually (Ioi_mem_nhds ha'), isOpen_ball.mem_nhds (mem_ball_self hρ)] with y hy hyb
    exact hy.trans_le (hbound y hyb)
  have hu : UpperSemicontinuousAt f c :=
    (upperSemicontinuousAt_leastSupersolutionOn_interior hμ hR hV hU hsub hz ht hcU).add
      (((enclosingDisc_potential_shift_on_domain hμ hR hV hsub).1.mono subset_closure).continuousAt
        (hU.mem_nhds hcU)).upperSemicontinuousAt
  exact continuousAt_iff_lower_upperSemicontinuousAt.2 ⟨hl, hu⟩

#print axioms continuousAt_shifted_infimum_of_constant_barrier

/-- At every off-pole point the shifted obstacle admits an arbitrarily small
constant barrier error against the shifted infimum. -/
theorem exists_approximate_constant_barrier_off_pole
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t) {x : ℂ}
    (hx : x ∈ U) (hxz : x ≠ z) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ L : ℝ, 0 < ρ ∧ closedBall x ρ ⊆ U ∧
      (∀ y ∈ sphere x ρ, L ≤ leastSupersolutionOn μ U z t y + greenPotentialBall μ R y + ε) ∧
      ∀ y ∈ ball x ρ, y ≠ z → -t * greenFunction U z y + greenPotentialBall μ R y ≤ L := by
  let f := fun y => leastSupersolutionOn μ U z t y + greenPotentialBall μ R y
  let β := fun y => -t * greenFunction U z y + greenPotentialBall μ R y
  let g := lscRegularization U f
  let L := β x + ε / 2
  have hβL : β x < L := by dsimp [L]; linarith
  have hLg : L - ε < g x := by
    have h := shifted_obstacle_le_lscRegularization_shifted_infimum hμ hR hV hU hsub hz ht hx hxz
    dsimp [L, β, g, f] at *
    linarith
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
  have hg := (isSuperharmonicOn_lscRegularization_shifted_infimum hμ hR hV hU hsub hz ht).1 x hx (L - ε) hLg
  rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hx)] at hg
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ U ∧ β y < L ∧ L - ε < g y := by
    filter_upwards [hU.mem_nhds hx, hβc.eventually (Iio_mem_nhds hβL), hg] with y hy hby hgy
    exact ⟨hy, hby, hgy⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  let ρ := δ / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hcb : closedBall x ρ ⊆ ball x δ := closedBall_subset_ball (by dsimp [ρ]; linarith)
  refine ⟨ρ, L, hρ, fun y hy => (hδsub (hcb hy)).1, ?_, ?_⟩
  · intro y hy
    have hy' := hδsub (hcb (sphere_subset_closedBall hy))
    have hle := lscRegularization_le hnonneg hy'.1
    dsimp [f] at hle
    linarith [hy'.2.2]
  · intro y hy _
    exact (hδsub (hcb (ball_subset_closedBall hy))).2.1.le

#print axioms exists_approximate_constant_barrier_off_pole

/-- The shifted infimum is continuous at the pole. -/
theorem continuousAt_shifted_infimum_at_pole
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun y => leastSupersolutionOn μ U z t y + greenPotentialBall μ R y) z := by
  obtain ⟨ρ, L, hρ, hd, hb, ho⟩ := exists_constant_barrier_at_pole hμ hR hV hU hsub hz ht
  exact continuousAt_shifted_infimum_of_constant_barrier hμ hR hV hU hsub hz ht.le hρ hd hb ho

#print axioms continuousAt_shifted_infimum_at_pole

/-- A nonnegative constant may be added to a supersolution. -/
theorem supersolutionsOn_add_nonneg_const {μ : Measure ℂ} {U : Set ℂ}
    (hU : IsOpen U) {z : ℂ} {t ε : ℝ} (hε : 0 ≤ ε)
    {w : ℂ → ℝ} (hw : w ∈ supersolutionsOn μ U z t) :
    (fun y => w y + ε) ∈ supersolutionsOn μ U z t := by
  refine ⟨hw.1.add continuousOn_const, ?_, ?_⟩
  · have hc := hasLaplacian_zero_of_harmonicOnNhd (U := U) hU (InnerProductSpace.harmonicOnNhd_const (1 : ℝ))
    simpa only [mul_one] using hw.2.1.add_const_mul_of_hasLaplacian_zero hc ε
  · intro y hy hyz
    linarith [hw.2.2 y hy hyz]

/-- An approximate constant barrier gives a Harnack lower bound for the
actual shifted infimum, with an error equal to the barrier error. -/
theorem shifted_infimum_lower_bound_of_approximate_barrier
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t) {c : ℂ} {ρ L ε : ℝ}
    (hε : 0 ≤ ε) (hρ : 0 < ρ) (hd : closedBall c ρ ⊆ U)
    (hb : ∀ y ∈ sphere c ρ, L ≤ leastSupersolutionOn μ U z t y + greenPotentialBall μ R y + ε)
    (ho : ∀ y ∈ ball c ρ, y ≠ z →
      -t * greenFunction U z y + greenPotentialBall μ R y ≤ L)
    {x : ℂ} (hx : x ∈ ball c ρ) :
    L + ((ρ - ‖x - c‖) / (ρ + ‖x - c‖)) *
      (leastSupersolutionOn μ U z t c + greenPotentialBall μ R c - L) - ε ≤
        leastSupersolutionOn μ U z t x + greenPotentialBall μ R x := by
  let q := greenPotentialBall μ R
  let f := fun y => leastSupersolutionOn μ U z t y + q y
  let k := (ρ - ‖x - c‖) / (ρ + ‖x - c‖)
  have hk : 0 ≤ k := by
    apply div_nonneg
    · have := mem_ball.mp hx; rw [dist_eq_norm] at this; linarith
    · positivity
  have hxU : x ∈ U := hd (ball_subset_closedBall hx)
  have hcU : c ∈ U := hd (mem_closedBall_self hρ.le)
  have hgoal : L + k * (f c - L) - ε - q x ≤ leastSupersolutionOn μ U z t x := by
    change _ ≤ sInf ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ U z t)
    apply le_csInf
    · exact ⟨0, 0, zero_mem_supersolutionsOn (isBounded_ball.subset hsub) ht, rfl⟩
    · rintro _ ⟨w, hw, rfl⟩
      let wε := fun y => w y + ε
      have hwε : wε ∈ supersolutionsOn μ U z t := supersolutionsOn_add_nonneg_const hU hε hw
      have hwb : ∀ y ∈ sphere c ρ, L ≤ wε y + q y := by
        intro y hy
        have hle := leastSupersolutionOn_le_of_mem_interior hμ hR hV hU hsub hz
          (hd (sphere_subset_closedBall hy)) hw
        have := hb y hy
        dsimp [wε, q] at *
        linarith
      obtain ⟨v, hv, hvP⟩ := exists_poisson_modified_supersolutionOn hμ hR hV hU hsub hz
        hwε hρ hd hwb ho
      have hcenter := leastSupersolutionOn_le_of_mem_interior hμ hR hV hU hsub hz hcU hv
      have hcenterP := hvP (mem_ball_self hρ)
      have hφ : CircleIntegrable (fun y => wε y + q y) c ρ :=
        (show IsSweepDisc U c ρ from ⟨hρ, hd⟩).circleIntegrable
          ((hwε.1.mono subset_closure).add
            ((enclosingDisc_potential_shift_on_domain hμ hR hV hsub).1.mono subset_closure))
      have hp := discPoissonIntegral_sub_lower_bound hρ hφ hwb hx
      have hfcenter : f c ≤ discPoissonIntegral (fun y => wε y + q y) c ρ c := by
        dsimp [f, q] at *
        linarith
      have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hfcenter L) hk
      have hsh := (shifted_supersolution_mem_nonnegativeSuperharmonicMajorants hμ hR hV hU hsub hz hwε).1
      have hP := discPoissonIntegral_le hsh.1 (hsh.localSuperMean hU) hρ hd hφ x hx
      dsimp [f, q, wε, k] at *
      linarith
  dsimp [f, q, k] at *
  linarith

#print axioms shifted_infimum_lower_bound_of_approximate_barrier

/-- The shifted general-domain infimum is lower semicontinuous in the interior. -/
theorem lowerSemicontinuousOn_shifted_infimum
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) :
    LowerSemicontinuousOn (fun y => leastSupersolutionOn μ U z t y + greenPotentialBall μ R y) U := by
  intro x hx
  by_cases hxz : x = z
  · subst x
    exact (continuousAt_shifted_infimum_at_pole hμ hR hV hU hsub hz ht).lowerSemicontinuousAt.lowerSemicontinuousWithinAt U
  · intro a ha
    let f := fun y => leastSupersolutionOn μ U z t y + greenPotentialBall μ R y
    let ε := (f x - a) / 2
    have hε : 0 < ε := by dsimp [ε, f]; linarith
    obtain ⟨ρ, L, hρ, hd, hb, ho⟩ :=
      exists_approximate_constant_barrier_off_pole hμ hR hV hU hsub hz ht.le hx hxz hε
    let lo := fun y : ℂ => L + ((ρ - ‖y - x‖) / (ρ + ‖y - x‖)) * (f x - L) - ε
    have hlo : ContinuousAt lo x := by
      dsimp [lo]
      fun_prop (disch := positivity)
    have hloc : lo x = f x - ε := by simp [lo, hρ.ne']
    have ha' : a < lo x := by rw [hloc]; dsimp [ε, f]; linarith
    have he : ∀ᶠ y in 𝓝 x, a < f y := by
      filter_upwards [hlo.eventually (Ioi_mem_nhds ha'), isOpen_ball.mem_nhds (mem_ball_self hρ)] with y hy hyb
      have hbound := shifted_infimum_lower_bound_of_approximate_barrier hμ hR hV hU hsub hz ht.le
        hε.le hρ hd hb ho hyb
      exact hy.trans_le hbound
    exact he.filter_mono nhdsWithin_le_nhds

/-- Interior continuity and the distributional Laplacian bound for the
general-domain least supersolution. -/
theorem general_domain_interior_infimum_regularity
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) :
    ContinuousOn (leastSupersolutionOn μ U z t) U ∧
      LaplacianLE (leastSupersolutionOn μ U z t) μ U := by
  apply interior_regularity_of_shifted_superharmonic hμ hR hV hU hsub hz ht.le
  exact isSuperharmonicOn_shifted_infimum_of_lowerSemicontinuous hμ hR hV hU hsub hz ht.le
    (lowerSemicontinuousOn_shifted_infimum hμ hR hV hU hsub hz ht)

#print axioms lowerSemicontinuousOn_shifted_infimum
#print axioms general_domain_interior_infimum_regularity

#print axioms interior_regularity_of_shifted_superharmonic

#print axioms continuousAt_leastSupersolutionOn_of_contact

#print axioms bddBelow_supersolutionsOn_values_interior
#print axioms leastSupersolutionOn_le_of_mem_interior
#print axioms upperSemicontinuousAt_leastSupersolutionOn_interior

end HarmonicBalls
