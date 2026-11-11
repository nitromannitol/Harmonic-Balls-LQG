import HarmonicBalls.Audit.Section5InfimumSemantics
import HarmonicBalls.Proofs.Sec5.GreenRegularDomainAdmissibility

/-! # Infimum and noncontact near the pole

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- The enclosing-disc potential bounds every competitor from below in the domain. -/
theorem neg_greenPotentialBall_le_supersolutionOn
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} {w : ℂ → ℝ}
    (hw : w ∈ supersolutionsOn μ U z t) {x : ℂ} (hx : x ∈ U) :
    -greenPotentialBall μ R x ≤ w x := by
  have h := (shifted_supersolution_mem_nonnegativeSuperharmonicMajorants
    hμ hR hV hU hsub hz hw).2.1 x hx
  linarith

/-- Competitor values at the pole are bounded below. -/
theorem bddBelow_supersolutionsOn_values_pole
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} :
    BddBelow ((fun w : ℂ → ℝ => w z) '' supersolutionsOn μ U z t) := by
  refine ⟨-greenPotentialBall μ R z, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact neg_greenPotentialBall_le_supersolutionOn hμ hR hV hU hsub hz hw hz

/-- The real infimum at the pole is the greatest lower bound. -/
theorem isGLB_supersolutionsOn_values_pole
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t) :
    IsGLB ((fun w : ℂ → ℝ => w z) '' supersolutionsOn μ U z t)
      (leastSupersolutionOn μ U z t z) := by
  apply isGLB_csInf
  · exact ⟨0, 0, zero_mem_supersolutionsOn (isBounded_ball.subset hsub) ht, rfl⟩
  · exact bddBelow_supersolutionsOn_values_pole hμ hR hV hU hsub hz

/-- The real and extended-real infima agree at the pole. -/
theorem coe_leastSupersolutionOn_eq_sInf_ereal_pole
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 ≤ t) :
    (leastSupersolutionOn μ U z t z : EReal) =
      sInf ((fun w : ℂ → ℝ => (w z : EReal)) '' supersolutionsOn μ U z t) := by
  let S := (fun w : ℂ → ℝ => (w z : EReal)) '' supersolutionsOn μ U z t
  have hglb := isGLB_supersolutionsOn_values_pole hμ hR hV hU hsub hz ht
  have hlo : (leastSupersolutionOn μ U z t z : EReal) ≤ sInf S := by
    apply le_sInf
    rintro _ ⟨w, hw, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (hglb.1 ⟨w, hw, rfl⟩)
  have hup : sInf S ≤ (0 : EReal) := by
    apply sInf_le
    exact ⟨0, zero_mem_supersolutionsOn (isBounded_ball.subset hsub) ht, rfl⟩
  have htop : sInf S ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hup EReal.zero_lt_top)
  have hbot : sInf S ≠ ⊥ := ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe _) hlo)
  have hreal : (sInf S).toReal ≤ leastSupersolutionOn μ U z t z := by
    apply hglb.2
    rintro _ ⟨w, hw, rfl⟩
    apply EReal.coe_le_coe_iff.mp
    rw [EReal.coe_toReal htop hbot]
    exact sInf_le ⟨w, hw, rfl⟩
  exact le_antisymm hlo (by
    rw [← EReal.coe_toReal htop hbot]
    exact EReal.coe_le_coe_iff.mpr hreal)

/-- The strict off-pole noncontact set contains a punctured neighborhood of the pole. -/
theorem eventually_strict_noncontact_nhdsWithin_pole
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ x in 𝓝[≠] z, x ∈ U ∧ x ≠ z ∧
      -t * greenFunction U z x < leastSupersolutionOn μ U z t x := by
  have hnear := (tendsto_greenRegular_shifted_obstacle_atBot hμ hR hV hU hsub hz ht).eventually
    (eventually_lt_atBot (0 : ℝ))
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hz), self_mem_nhdsWithin, hnear] with x hx hxz hlt
  have hlo : -greenPotentialBall μ R x ≤ leastSupersolutionOn μ U z t x := by
    apply le_csInf
    · exact ⟨0, 0, zero_mem_supersolutionsOn (isBounded_ball.subset hsub) ht.le, rfl⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact neg_greenPotentialBall_le_supersolutionOn hμ hR hV hU hsub hz hw hx
  exact ⟨hx, hxz, by linarith⟩

/-- The pole is in the closure of the strict off-pole noncontact set. -/
theorem pole_mem_closure_strict_noncontact
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) :
    z ∈ closure {x ∈ U | x ≠ z ∧
      -t * greenFunction U z x < leastSupersolutionOn μ U z t x} := by
  apply mem_closure_iff_frequently.mpr
  exact (eventually_strict_noncontact_nhdsWithin_pole hμ hR hV hU hsub hz ht).frequently.filter_mono
    nhdsWithin_le_nhds

/-- Inserting the pole does not change the closure of the strict noncontact set. -/
theorem closure_clusterOn_eq_closure_strict_noncontact
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) :
    closure (clusterOn μ U z t) = closure {x ∈ U | x ≠ z ∧
      -t * greenFunction U z x < leastSupersolutionOn μ U z t x} := by
  rw [closure_clusterOn_eq_insert_pole hz,
    insert_eq_of_mem (pole_mem_closure_strict_noncontact hμ hR hV hU hsub hz ht)]

end HarmonicBalls
