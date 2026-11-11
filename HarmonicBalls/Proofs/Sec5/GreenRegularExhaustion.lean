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

/-- The odometer comparison follows from a continuous harmonic Green
correction, including when the two domains share boundary points. -/
theorem odometerOn_le_of_green_difference
    {μ : Measure ℂ} {V U : Set ℂ} (hV : IsOpen V)
    (hUb : Bornology.IsBounded U) (hVU : V ⊆ U)
    {z x : ℂ} (hx : x ∈ V) (hxz : x ≠ z) {t : ℝ} (ht : 0 ≤ t)
    {h : ℂ → ℝ} (hc : ContinuousOn h (closure V)) (hh : HarmonicOnNhd h V)
    (hG : ∀ y ∈ closure V, y ≠ z → greenFunction V z y - greenFunction U z y = h y) :
    leastSupersolutionOn μ V z t x + t * greenFunction V z x ≤
      leastSupersolutionOn μ U z t x + t * greenFunction U z x := by
  have hle : leastSupersolutionOn μ V z t x + t * greenFunction V z x -
      t * greenFunction U z x ≤ leastSupersolutionOn μ U z t x := by
    unfold leastSupersolutionOn
    apply le_csInf
    · exact ⟨_, ⟨0, zero_mem_supersolutionsOn hUb ht, rfl⟩⟩
    · rintro _ ⟨w, hw, rfl⟩
      have hw' : (fun y => w y + (-t) * h y) ∈ supersolutionsOn μ V z t := by
        refine ⟨(hw.1.mono (closure_mono hVU)).add (continuousOn_const.mul hc), ?_, ?_⟩
        · exact (hw.2.1.mono_set hVU).add_const_mul_of_hasLaplacian_zero
            (hasLaplacian_zero_of_harmonicOnNhd hV hh) (-t)
        · intro y hy hyz
          have hwbound := hw.2.2 y (closure_mono hVU hy) hyz
          have heq := hG y hy hyz
          nlinarith
      have hwle := leastSupersolutionOn_le_of_mem hw' (subset_closure hx) hxz
      have heq := hG x (subset_closure hx) hxz
      unfold leastSupersolutionOn at hwle
      dsimp only at hwle ⊢
      nlinarith
  linarith

/-- Nested bounded Green-regular domains have a Green correction continuous
on the smaller closure, even when their boundaries meet. -/
theorem exists_green_difference_of_nested_regular
    {V U : Set ℂ} (hV : IsOpen V) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hVU : V ⊆ U) {z : ℂ} (hz : z ∈ V)
    (hVboundary : ∀ y ∈ closure V, y ∉ V →
      Tendsto (greenFunction V z) (𝓝[V] y) (𝓝 0))
    (hUboundary : ∀ y ∈ closure U, y ∉ U →
      Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0)) :
    ∃ h : ℂ → ℝ, ContinuousOn h (closure V) ∧ HarmonicOnNhd h V ∧
      ∀ x ∈ closure V, x ≠ z → greenFunction V z x - greenFunction U z x = h x := by
  obtain ⟨r, hr⟩ := hUb.subset_ball (0 : ℂ)
  obtain ⟨a, hac, hah, ha⟩ := exists_continuousOn_green_difference_of_boundary_limits
    hV (hVU.trans hr) hz hVboundary
  obtain ⟨b, hbc, hbh, hb⟩ := exists_continuousOn_green_difference_of_boundary_limits
    hU hr (hVU hz) hUboundary
  refine ⟨fun x => a x - b x, hac.sub (hbc.mono (closure_mono hVU)),
    hah.sub (hbh.mono hVU), ?_⟩
  intro x hx hxz
  have h₁ := ha x hx hxz
  have h₂ := hb x (closure_mono hVU hx) hxz
  linarith

/-- The odometer increases under inclusion of bounded Green-regular domains. -/
theorem odometerOn_le_of_nested_regular
    {μ : Measure ℂ} {V U : Set ℂ} (hV : IsOpen V) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hVU : V ⊆ U) {z x : ℂ}
    (hz : z ∈ V) (hx : x ∈ V) (hxz : x ≠ z) {t : ℝ} (ht : 0 ≤ t)
    (hVboundary : ∀ y ∈ closure V, y ∉ V →
      Tendsto (greenFunction V z) (𝓝[V] y) (𝓝 0))
    (hUboundary : ∀ y ∈ closure U, y ∉ U →
      Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0)) :
    leastSupersolutionOn μ V z t x + t * greenFunction V z x ≤
      leastSupersolutionOn μ U z t x + t * greenFunction U z x := by
  obtain ⟨h, hc, hh, hG⟩ :=
    exists_green_difference_of_nested_regular hV hU hUb hVU hz hVboundary hUboundary
  exact odometerOn_le_of_green_difference hV hUb hVU hx hxz ht hc hh hG

/-- Clusters increase under inclusion of bounded Green-regular domains. -/
theorem clusterOn_subset_of_nested_regular
    {μ : Measure ℂ} {V U : Set ℂ} (hV : IsOpen V) (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hVU : V ⊆ U)
    {z : ℂ} (hz : z ∈ V) {t : ℝ} (ht : 0 ≤ t)
    (hVboundary : ∀ y ∈ closure V, y ∉ V →
      Tendsto (greenFunction V z) (𝓝[V] y) (𝓝 0))
    (hUboundary : ∀ y ∈ closure U, y ∉ U →
      Tendsto (greenFunction U z) (𝓝[U] y) (𝓝 0)) :
    clusterOn μ V z t ⊆ clusterOn μ U z t := by
  intro x hx
  refine ⟨hVU hx.1, ?_⟩
  rcases hx.2 with h | h
  · exact Or.inl h
  · by_cases hxz : x = z
    · exact Or.inl hxz
    · right
      have hle := odometerOn_le_of_nested_regular (μ := μ) hV hU hUb hVU hz hx.1 hxz
        ht hVboundary hUboundary
      linarith

/-- Away from the pole, the obstacle-subtracted infimum is nonnegative. -/
theorem odometerOn_nonneg {μ : Measure ℂ} {U : Set ℂ}
    (hUb : Bornology.IsBounded U) {z x : ℂ} (hx : x ∈ U) (hxz : x ≠ z)
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ leastSupersolutionOn μ U z t x + t * greenFunction U z x := by
  have hle : -t * greenFunction U z x ≤ leastSupersolutionOn μ U z t x := by
    unfold leastSupersolutionOn
    apply le_csInf
    · exact ⟨_, ⟨0, zero_mem_supersolutionsOn hUb ht, rfl⟩⟩
    · rintro _ ⟨w, hw, rfl⟩
      exact hw.2.2 x (subset_closure hx) hxz
  linarith

/-- Along a nested relatively compact regular exhaustion, the nonnegative
odometer values converge monotonically to a finite limit bounded by the
odometer of the union. Equality with the latter is not asserted. -/
theorem exists_tendsto_odometerOn_of_regular_exhaustion
    {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (hsub : ∀ n, closure (V n) ⊆ U) {z x : ℂ} (hz : ∀ n, z ∈ V n)
    (hx : x ∈ U) (hxz : x ≠ z) {t : ℝ} (ht : 0 ≤ t)
    (hboundary : ∀ n y, y ∈ closure (V n) → y ∉ V n →
      Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0)) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ leastSupersolutionOn μ U z t x + t * greenFunction U z x ∧
      let f := fun n => (V n).indicator (fun _ =>
        leastSupersolutionOn μ (V n) z t x + t * greenFunction (V n) z x) x
      Monotone f ∧ (∀ n, f n ≤ a) ∧ Tendsto f atTop (𝓝 a) := by
  classical
  let f : ℕ → ℝ := fun n => (V n).indicator (fun _ =>
    leastSupersolutionOn μ (V n) z t x + t * greenFunction (V n) z x) x
  have hVb (n : ℕ) : Bornology.IsBounded (V n) :=
    hUb.subset (subset_closure.trans (hsub n))
  have hfnonneg (n : ℕ) : 0 ≤ f n := by
    by_cases hn : x ∈ V n
    · simpa only [f, Set.indicator_of_mem hn] using odometerOn_nonneg (μ := μ) (hVb n) hn hxz ht
    · simp only [f, Set.indicator_of_notMem hn, le_refl]
  have hfmono : Monotone f := by
    intro n m hnm
    by_cases hn : x ∈ V n
    · have hm := hmono hnm hn
      simpa only [f, Set.indicator_of_mem hn, Set.indicator_of_mem hm] using
        (odometerOn_le_of_nested_regular (μ := μ) (hopen n) (hopen m) (hVb m)
          (hmono hnm) (hz n) hn hxz ht (hboundary n) (hboundary m))
    · simpa only [f, Set.indicator_of_notMem hn] using hfnonneg m
  have hfupper (n : ℕ) : f n ≤
      leastSupersolutionOn μ U z t x + t * greenFunction U z x := by
    by_cases hn : x ∈ V n
    · simpa only [f, Set.indicator_of_mem hn] using
        (odometerOn_le_of_compactly_contained_regular (μ := μ) (hopen n) hU hUb
          (hsub n) (hz n) hn hxz ht (hboundary n))
    · simpa only [f, Set.indicator_of_notMem hn] using odometerOn_nonneg (μ := μ) hUb hx hxz ht
  have hbounded : BddAbove (Set.range f) := ⟨_, fun _ ⟨n, hn⟩ => hn ▸ hfupper n⟩
  refine ⟨⨆ n, f n, ?_, ciSup_le hfupper, hfmono, ?_, ?_⟩
  · exact (hfnonneg 0).trans (le_ciSup hbounded 0)
  · exact fun n => le_ciSup hbounded n
  · exact tendsto_atTop_ciSup hfmono hbounded

end HarmonicBalls
