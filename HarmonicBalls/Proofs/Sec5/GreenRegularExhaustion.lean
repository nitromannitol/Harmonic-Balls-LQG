import HarmonicBalls.Proofs.Sec5.CompactGeneralDomainCompatibility
import HarmonicBalls.Proofs.Sec5.GreenRegularDomainAdmissibility

/-! # Comparison with a relatively compact Green-regular domain

These results use the potential-theoretic infrastructure of Leonardo Bonanno.
The larger domain need not be Green-regular and its infimum need not be admissible.
-/

namespace HarmonicBalls

open Filter MeasureTheory Metric Set InnerProductSpace
open scoped Topology

/-- A regular smaller domain has a continuous harmonic Green correction relative
 to any bounded open larger domain containing its closure. -/
theorem exists_green_difference_of_compactly_contained_regular
    {V U : Set ℂ} (hV : IsOpen V) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hVU : closure V ⊆ U) {z : ℂ} (hz : z ∈ V)
    (hboundary : ∀ y ∈ closure V, y ∉ V →
      Tendsto (greenFunction V z) (𝓝[V] y) (𝓝 0)) :
    ∃ h : ℂ → ℝ, ContinuousOn h (closure V) ∧ HarmonicOnNhd h V ∧
      ∀ x ∈ closure V, x ≠ z → greenFunction V z x - greenFunction U z x = h x := by
  obtain ⟨r, hr⟩ := hUb.subset_ball (0 : ℂ)
  have hsub : V ⊆ ball (0 : ℂ) r := subset_closure.trans (hVU.trans hr)
  have hzU : z ∈ U := hVU (subset_closure hz)
  obtain ⟨a, hac, hah, ha⟩ :=
    exists_continuousOn_green_difference_of_boundary_limits hV hsub hz hboundary
  obtain ⟨b, hbh, hb⟩ := exists_harmonicOnNhd_greenFunction_difference hU hUb hr hzU
  refine ⟨fun x => a x - b x, hac.sub (hbh.continuousOn.mono hVU),
    hah.sub (hbh.mono (subset_closure.trans hVU)), ?_⟩
  intro x hx hxz
  have h₁ := ha x hx hxz
  have h₂ := hb x (hVU hx) hxz
  linarith

/-- The obstacle-subtracted infimum increases with the domain. This comparison
uses no admissibility or boundary continuity for the larger-domain infimum. -/
theorem odometerOn_le_of_compactly_contained_regular
    {μ : Measure ℂ} {V U : Set ℂ} (hV : IsOpen V) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hVU : closure V ⊆ U)
    {z x : ℂ} (hz : z ∈ V) (hx : x ∈ V) (hxz : x ≠ z)
    {t : ℝ} (ht : 0 ≤ t)
    (hboundary : ∀ y ∈ closure V, y ∉ V →
      Tendsto (greenFunction V z) (𝓝[V] y) (𝓝 0)) :
    leastSupersolutionOn μ V z t x + t * greenFunction V z x ≤
      leastSupersolutionOn μ U z t x + t * greenFunction U z x := by
  obtain ⟨h, hc, hh, hG⟩ :=
    exists_green_difference_of_compactly_contained_regular hV hU hUb hVU hz hboundary
  have hsub : V ⊆ U := subset_closure.trans hVU
  have hle : leastSupersolutionOn μ V z t x + t * greenFunction V z x -
      t * greenFunction U z x ≤ leastSupersolutionOn μ U z t x := by
    unfold leastSupersolutionOn
    apply le_csInf
    · exact ⟨_, ⟨0, zero_mem_supersolutionsOn hUb ht, rfl⟩⟩
    · rintro _ ⟨w, hw, rfl⟩
      have hw' : (fun y => w y + (-t) * h y) ∈ supersolutionsOn μ V z t := by
        refine ⟨(hw.1.mono (hVU.trans subset_closure)).add
          (continuousOn_const.mul hc), ?_, ?_⟩
        · exact (hw.2.1.mono_set hsub).add_const_mul_of_hasLaplacian_zero
            (hasLaplacian_zero_of_harmonicOnNhd hV hh) (-t)
        · intro y hy hyz
          have hwbound := hw.2.2 y (subset_closure (hVU hy)) hyz
          have heq := hG y hy hyz
          nlinarith
      have hwle := leastSupersolutionOn_le_of_mem hw' (subset_closure hx) hxz
      have heq := hG x (subset_closure hx) hxz
      unfold leastSupersolutionOn at hwle
      dsimp only at hwle ⊢
      nlinarith
  linarith

/-- The cluster in a relatively compact regular domain is contained in the
cluster of the larger bounded open domain. -/
theorem clusterOn_subset_of_compactly_contained_regular
    {μ : Measure ℂ} {V U : Set ℂ} (hV : IsOpen V) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hVU : closure V ⊆ U)
    {z : ℂ} (hz : z ∈ V) {t : ℝ} (ht : 0 ≤ t)
    (hboundary : ∀ y ∈ closure V, y ∉ V →
      Tendsto (greenFunction V z) (𝓝[V] y) (𝓝 0)) :
    clusterOn μ V z t ⊆ clusterOn μ U z t := by
  intro x hx
  refine ⟨hVU (subset_closure hx.1), ?_⟩
  rcases hx.2 with h | h
  · exact Or.inl h
  · by_cases hxz : x = z
    · exact Or.inl hxz
    · right
      have hle := odometerOn_le_of_compactly_contained_regular (μ := μ) hV hU hUb hVU hz hx.1 hxz ht hboundary
      linarith

#print axioms exists_green_difference_of_compactly_contained_regular
#print axioms odometerOn_le_of_compactly_contained_regular
#print axioms clusterOn_subset_of_compactly_contained_regular

end HarmonicBalls
