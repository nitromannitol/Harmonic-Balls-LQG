import HarmonicBalls.Proofs.Sec5.GeneralDomainClusterOpen
import HarmonicBalls.Steps.Sec11.PinchGreenMeasurable

/-! # Green boundary regularity from supporting discs -/

namespace HarmonicBalls

open Filter MeasureTheory Metric Set
open scoped Topology

/-- A bounded open set has vanishing Green function at a boundary point
where it is contained in a disc tangent at that point. -/
theorem tendsto_greenFunction_zero_of_enclosing_disc
    {U : Set ℂ} {z y c : ℂ} {r : ℝ} (hz : z ∈ U)
    (hsub : U ⊆ ball c r) (hy : y ∈ sphere c r) :
    Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0) := by
  have hzball : z ∈ ball c r := hsub hz
  have hzc : z - c ∈ ball (0 : ℂ) r := by
    simpa only [mem_ball, dist_eq_norm, sub_zero] using hzball
  have hynot : y ∉ ball c r := by
    intro h
    exact (ne_of_lt (mem_ball.mp h)) (mem_sphere.mp hy)
  have hyz : y ≠ z := fun h => hynot (h ▸ hzball)
  have hyzc : y - c ≠ z - c := by
    intro h
    apply hyz
    simpa only [sub_add_cancel] using congrArg (fun w : ℂ => w + c) h
  have hc := (continuousOn_greenFunction_ball hzc).continuousAt
    (isOpen_compl_singleton.mem_nhds hyzc)
  have hzero : greenFunction (ball (0 : ℂ) r) (z - c) (y - c) = 0 := by
    rw [← greenFunction_ball_translate c z y r]
    exact greenFunction_of_notMem_right hynot z
  have hlim : Tendsto (greenFunction (ball c r) z) (𝓝[U] y) (𝓝 0) := by
    have hcomp := hc.tendsto.comp ((continuous_id.sub continuous_const).tendsto y)
    rw [hzero] at hcomp
    have hcomp := hcomp.mono_left (nhdsWithin_le_nhds (s := U))
    apply hcomp.congr'
    filter_upwards with x
    exact (greenFunction_ball_translate c z x r).symm
  have hlower : Tendsto (fun _ : ℂ => (0 : ℝ)) (𝓝[U] y) (𝓝 0) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hlim
  · exact Filter.Eventually.of_forall (greenFunction_nonneg (isBounded_ball.subset hsub) z)
  · exact Filter.Eventually.of_forall (Section6.greenFunction_le_of_subset hsub isBounded_ball z)

/-- Disc support at every boundary point supplies Green boundary regularity. -/
theorem tendsto_greenFunction_zero_of_enclosing_discs
    {U : Set ℂ} {z : ℂ} (hz : z ∈ U)
    (hsupport : ∀ y ∈ closure U, y ∉ U →
      ∃ c : ℂ, ∃ r : ℝ, U ⊆ ball c r ∧ y ∈ sphere c r) :
    ∀ y ∈ closure U, y ∉ U → Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0) := by
  intro y hy hyU
  obtain ⟨c, r, hsub, hyball⟩ := hsupport y hy hyU
  exact tendsto_greenFunction_zero_of_enclosing_disc hz hsub hyball

/-- Every boundary point of an intersection of open discs is supported by
one of those discs. No finiteness assumption is needed. -/
theorem exists_enclosing_disc_of_eq_iInter_ball
    {ι : Type*} {U : Set ℂ} {c : ι → ℂ} {r : ι → ℝ}
    (hU : U = ⋂ i, ball (c i) (r i)) :
    ∀ y ∈ closure U, y ∉ U →
      ∃ c : ℂ, ∃ r : ℝ, U ⊆ ball c r ∧ y ∈ sphere c r := by
  classical
  intro y hy hyU
  rw [hU, mem_iInter] at hyU
  push Not at hyU
  obtain ⟨i, hi⟩ := hyU
  have hsub : U ⊆ ball (c i) (r i) := by
    rw [hU]
    exact iInter_subset _ i
  have hyclosed : y ∈ closedBall (c i) (r i) :=
    (closure_minimal (hsub.trans ball_subset_closedBall) isClosed_closedBall) hy
  have hle : dist y (c i) ≤ r i := mem_closedBall.mp hyclosed
  have hge : r i ≤ dist y (c i) := le_of_not_gt hi
  exact ⟨c i, r i, hsub, mem_sphere.mpr (le_antisymm hle hge)⟩

/-- Strong compatibility follows when the pole component has supporting
discs at its boundary, subject to least-supersolution admissibility. -/
theorem regularizedFamily_strongCompatibility_of_component_enclosing_discs
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z : ℂ} (hz : z ∈ U) {t : ℝ} (ht : 0 < t)
    (hv : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t)
    (hsupport : ∀ y ∈ closure (connectedComponentIn U z),
      y ∉ connectedComponentIn U z →
      ∃ c : ℂ, ∃ r : ℝ, connectedComponentIn U z ⊆ ball c r ∧ y ∈ sphere c r)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hopen : ∀ r : ℝ, 0 < r → IsOpen (cluster μ r z t))
    (hcl : closure (Λ t) ⊆ U ∨ closure (clusterOn μ U z t) ⊆ U) :
    closure (Λ t) = closure (clusterOn μ U z t) := by
  exact regularizedFamily_strongCompatibility_of_component_boundary hU hUb hz ht hv
    (tendsto_greenFunction_zero_of_enclosing_discs (mem_connectedComponentIn hz) hsupport)
    hΛ hopen hcl

/-- Strong compatibility survives relatively countable deletions from a domain
whose pole component is an intersection of discs. -/
theorem regularizedFamily_strongCompatibility_of_countable_on_disc_intersection_component
    {ι : Type*} {c : ι → ℂ} {r : ι → ℝ}
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ R : ℝ, 0 < R → VolumeGrowth μ R βm βp)
    {U K : Set ℂ} (hU : IsOpen U) (hUK : IsOpen (U \ K))
    (hUb : Bornology.IsBounded U) {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hz : z ∈ U \ K) (hK : (K ∩ connectedComponentIn U z).Countable)
    (hcomp : connectedComponentIn U z = ⋂ i, ball (c i) (r i))
    (hw : leastSupersolutionOn μ (connectedComponentIn U z) z t ∈
      supersolutionsOn μ (connectedComponentIn U z) z t)
    {Λ : ℝ → Set ℂ} (hΛ : IsRegularizedClusterFamily μ Λ z)
    (hcl : closure (Λ t) ⊆ U \ K ∨
      closure (clusterOn μ (U \ K) z t) ⊆ U \ K) :
    closure (Λ t) = closure (clusterOn μ (U \ K) z t) := by
  apply regularizedFamily_strongCompatibility_of_countable_on_component_of_volumeGrowth
    hμ hV hU hUK hUb ht hz hK hw
  · exact tendsto_greenFunction_zero_of_enclosing_discs (mem_connectedComponentIn hz.1)
      (exists_enclosing_disc_of_eq_iInter_ball hcomp)
  · exact hΛ
  · exact hcl

#print axioms tendsto_greenFunction_zero_of_enclosing_disc
#print axioms exists_enclosing_disc_of_eq_iInter_ball
#print axioms regularizedFamily_strongCompatibility_of_component_enclosing_discs
#print axioms regularizedFamily_strongCompatibility_of_countable_on_disc_intersection_component

end HarmonicBalls
