import HarmonicBalls.Proofs.Sec3.ClusterCompatibility
import HarmonicBalls.Draft.Section5

/-!
# Domain monotonicity under a Green-function boundary hypothesis

The usual obstacle comparison applies to an open subset of a disc when the
difference of the two Green functions extends continuously to the closure of
the subset. The extension hypothesis is explicit: it is not established here
for domains with irregular boundary points.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- The general-domain least supersolution is bounded above by each admissible
supersolution at an off-pole point of the closure. -/
theorem leastSupersolutionOn_le_of_mem {μ : Measure ℂ} {U : Set ℂ} {z x : ℂ} {t : ℝ}
    {w : ℂ → ℝ} (hw : w ∈ supersolutionsOn μ U z t)
    (hx : x ∈ closure U) (hxz : x ≠ z) :
    leastSupersolutionOn μ U z t x ≤ w x := by
  have hbdd : BddBelow ((fun v : ℂ → ℝ => v x) '' supersolutionsOn μ U z t) :=
    ⟨-t * greenFunction U z x, by
      rintro _ ⟨v, hv, rfl⟩
      exact hv.2.2 x hx hxz⟩
  exact csInf_le hbdd ⟨w, hw, rfl⟩

/-- A disc supersolution gives a general-domain supersolution after shifting
by the harmonic difference of the Green functions. -/
theorem shifted_supersolutionOn_of_green_difference
    {μ : Measure ℂ} {U : Set ℂ} {r t : ℝ} {z : ℂ} {w h : ℂ → ℝ}
    (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) r)
    (hw : w ∈ supersolutions μ r z t)
    (hc : ContinuousOn h (closure U)) (hh : InnerProductSpace.HarmonicOnNhd h U)
    (hG : ∀ x ∈ closure U, x ≠ z →
      greenFunction U z x - greenFunction (ball 0 r) z x = h x) :
    (fun x => w x + (-t) * h x) ∈ supersolutionsOn μ U z t := by
  have hcl : closure U ⊆ closedBall (0 : ℂ) r :=
    closure_minimal (hsub.trans ball_subset_closedBall) isClosed_closedBall
  refine ⟨(hw.1.mono hcl).add (continuousOn_const.mul hc), ?_, ?_⟩
  · exact (hw.2.1.mono_set hsub).add_const_mul_of_hasLaplacian_zero
      (hasLaplacian_zero_of_harmonicOnNhd hU hh) (-t)
  · intro x hx hxz
    have h1 := hw.2.2 x (hcl hx) hxz
    have h2 := hG x hx hxz
    have heq : t * h x = t * greenFunction U z x -
        t * greenFunction (ball 0 r) z x := by rw [← h2]; ring
    change -t * greenFunction U z x ≤ w x + (-t) * h x
    linarith

/-- A continuous extension of the Green difference forces the general-domain
Green function to be continuous on the closed domain away from the pole.
This makes the boundary regularity required by the comparison explicit. -/
theorem continuousOn_greenFunction_of_continuous_difference
    {U : Set ℂ} {r : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) r)
    {h : ℂ → ℝ} (hc : ContinuousOn h (closure U))
    (hG : ∀ x ∈ closure U, x ≠ z →
      greenFunction U z x - greenFunction (ball 0 r) z x = h x) :
    ContinuousOn (greenFunction U z) (closure U \ {z}) := by
  have hball : ContinuousOn (greenFunction (ball 0 r) z) (closure U \ {z}) :=
    (continuousOn_greenFunction_ball hz).mono (fun _ hx => hx.2)
  apply ((hc.mono sdiff_subset).add hball).congr
  intro x hx
  have heq := hG x hx.1 (by simpa only [mem_singleton_iff] using hx.2)
  change greenFunction U z x = h x + greenFunction (ball 0 r) z x
  linarith

/-- The general-domain cluster lies in the disc cluster when the Green
function difference has the stated continuous harmonic extension. -/
theorem clusterOn_subset_cluster_of_green_difference
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U : Set ℂ}
    (hU : IsOpen U) {r βm βp : ℝ} (hr : 0 < r)
    (hV : VolumeGrowth μ r βm βp) (hsub : U ⊆ ball (0 : ℂ) r)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) {h : ℂ → ℝ}
    (hc : ContinuousOn h (closure U)) (hh : InnerProductSpace.HarmonicOnNhd h U)
    (hG : ∀ x ∈ closure U, x ≠ z →
      greenFunction U z x - greenFunction (ball 0 r) z x = h x) :
    clusterOn μ U z t ⊆ cluster μ r z t := by
  have hzball := hsub hz
  obtain ⟨_, _, hv⟩ := leastSupersolution_mem_of_general
    obstacleLeastSuperharmonicMajorantGeneral_holds obstacleCompatibilityShiftStep_holds
    hμ hr hV hzball ht
  have hcomp := shifted_supersolutionOn_of_green_difference hU hsub hv hc hh hG
  intro x hx
  refine ⟨hsub hx.1, ?_⟩
  rcases hx.2 with hxz | hxpos
  · exact Or.inl hxz
  · by_cases hxz : x = z
    · exact Or.inl hxz
    · right
      have hle := leastSupersolutionOn_le_of_mem hcomp (subset_closure hx.1) hxz
      have heq := hG x (subset_closure hx.1) hxz
      have heq' : t * h x = t * greenFunction U z x -
          t * greenFunction (ball 0 r) z x := by rw [← heq]; ring
      change leastSupersolutionOn μ U z t x ≤
        leastSupersolution μ r z t x + (-t) * h x at hle
      linarith

end HarmonicBalls
