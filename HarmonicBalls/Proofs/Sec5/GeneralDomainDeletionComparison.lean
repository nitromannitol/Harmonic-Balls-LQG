import HarmonicBalls.Proofs.Sec5.LocallyFiniteRankDiscCompatibility

/-! # Comparison on general domains after locally finite-rank deletion -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace

/-- A locally finite accumulation rank restricts to a smaller domain. -/
theorem LocallyFiniteRankOn.mono_domain {U V K : Set ℂ}
    (hK : LocallyFiniteRankOn U K) (hVU : V ⊆ U) : LocallyFiniteRankOn V K := by
  intro C hC hCV
  obtain ⟨n, hn⟩ := hK C hC (hCV.trans hVU)
  exact ⟨n, hn.mono_domain hVU⟩

/-- If deletion preserves the Green function, capped barriers turn any
full-domain supersolution into an arbitrarily close punctured competitor. -/
theorem leastSupersolutionOn_locallyFiniteRankOn_punctured_le_supersolution
    {μ : Measure ℂ} {U K : Set ℂ} {R t : ℝ} {z x : ℂ} {w : ℂ → ℝ}
    (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hG : ∀ y ∈ U \ K, y ≠ z → greenFunction (U \ K) z y = greenFunction U z y)
    (hx : x ∈ U \ K) (hxz : x ≠ z) (hw : w ∈ supersolutionsOn μ U z t) :
    leastSupersolutionOn μ (U \ K) z t x ≤ w x := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨B, hB⟩ := hUb.isCompact_closure.exists_bound_of_continuousOn hw.1
  let M := max B 0
  have hM : 0 ≤ M := le_max_right B 0
  obtain ⟨b, hbc, hbΔ, hbn, hsmall, hcover⟩ :=
    exists_capped_barrier_of_locallyFiniteRankOn hKc hK hUb.isCompact_closure hUR hx.2 hM hε
  have hcl : closure (U \ K) ⊆ closure U := closure_mono sdiff_subset
  let v : ℂ → ℝ := fun y => w y + b y
  have hv : v ∈ supersolutionsOn μ (U \ K) z t := by
    refine ⟨(hw.1.add (hbc.mono (hUR.trans ball_subset_closedBall))).mono hcl, ?_, ?_⟩
    · exact (hw.2.1.add_of_nonpos (hbΔ.mono_set (subset_closure.trans hUR))).mono_set sdiff_subset
    · intro y hy hyz
      have hycl := hcl hy
      by_cases hyK : y ∈ K
      · have hynot : y ∉ U \ K := fun h => h.2 hyK
        rw [greenFunction_of_notMem_right hynot, mul_zero]
        have hcov := hcover y ⟨hyK, hycl⟩
        have hbound : ‖w y‖ ≤ M := (hB y hycl).trans (le_max_left B 0)
        have habs : -‖w y‖ ≤ w y := by simpa only [Real.norm_eq_abs] using neg_abs_le (w y)
        dsimp [v]
        linarith
      · by_cases hyU : y ∈ U
        · rw [hG y ⟨hyU, hyK⟩ hyz]
          dsimp [v]
          linarith [hw.2.2 y hycl hyz, hbn y]
        · have hynot : y ∉ U \ K := fun h => hyU h.1
          have hwbound := hw.2.2 y hycl hyz
          rw [greenFunction_of_notMem_right hyU, mul_zero] at hwbound
          rw [greenFunction_of_notMem_right hynot, mul_zero]
          dsimp [v]
          linarith [hbn y]
  have hle := leastSupersolutionOn_le_of_mem hv (subset_closure hx) hxz
  dsimp [v] at hle
  linarith

/-- Under Green invariance and existence of a full-domain least supersolution,
the two least supersolutions coincide away from the deletion and pole. -/
theorem leastSupersolutionOn_locallyFiniteRankOn_punctured_eq_of_green_eq
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ} {R t : ℝ} {z x : ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t)
    (hG : ∀ y ∈ U \ K, y ≠ z → greenFunction (U \ K) z y = greenFunction U z y)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hx : x ∈ U \ K) (hxz : x ≠ z) :
    leastSupersolutionOn μ (U \ K) z t x = leastSupersolutionOn μ U z t x := by
  apply le_antisymm
  · exact leastSupersolutionOn_locallyFiniteRankOn_punctured_le_supersolution
      hUb hUR hKc hK hG hx hxz hw
  · exact leastSupersolutionOn_le_locallyFiniteRankOn_punctured hμ hU hUb
      (hK.mono_domain (subset_closure.trans hUR)) hqc hq ht (subset_closure hx.1) hxz

/-- Under Green invariance, deletion removes exactly the deleted points from the
cluster of the full domain. -/
theorem clusterOn_locallyFiniteRankOn_punctured_eq_sdiff_of_green_eq
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ} {R t : ℝ} {z : ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t)
    (hG : ∀ y ∈ U \ K, y ≠ z → greenFunction (U \ K) z y = greenFunction U z y)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t) :
    clusterOn μ (U \ K) z t = clusterOn μ U z t \ K := by
  ext x
  constructor
  · rintro ⟨hx, hxz | hxpos⟩
    · exact ⟨⟨hx.1, Or.inl hxz⟩, hx.2⟩
    · refine ⟨⟨hx.1, ?_⟩, hx.2⟩
      by_cases hxz : x = z
      · exact Or.inl hxz
      · right
        rw [hG x hx hxz,
          leastSupersolutionOn_locallyFiniteRankOn_punctured_eq_of_green_eq
            hμ hU hUb hUR hKc hK hqc hq ht hG hw hx hxz] at hxpos
        exact hxpos
  · rintro ⟨⟨hx, hxz | hxpos⟩, hxK⟩
    · exact ⟨⟨hx, hxK⟩, Or.inl hxz⟩
    · refine ⟨⟨hx, hxK⟩, ?_⟩
      by_cases hxz : x = z
      · exact Or.inl hxz
      · right
        rw [hG x ⟨hx, hxK⟩ hxz,
          leastSupersolutionOn_locallyFiniteRankOn_punctured_eq_of_green_eq
            hμ hU hUb hUR hKc hK hqc hq ht hG hw ⟨hx, hxK⟩ hxz]
        exact hxpos

/-- If the full-domain cluster is open, its closure is unaffected by the deletion. -/
theorem closure_clusterOn_locallyFiniteRankOn_punctured_eq_of_green_eq
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ} {R t : ℝ} {z : ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R)
    (hKc : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t)
    (hG : ∀ y ∈ U \ K, y ≠ z → greenFunction (U \ K) z y = greenFunction U z y)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopen : IsOpen (clusterOn μ U z t)) :
    closure (clusterOn μ (U \ K) z t) = closure (clusterOn μ U z t) := by
  rw [clusterOn_locallyFiniteRankOn_punctured_eq_sdiff_of_green_eq
    hμ hU hUb hUR hKc hK hqc hq ht hG hw]
  apply closure_sdiff_countable_inter hopen
  exact (countable_inter_open_of_locallyFiniteRankOn hU
    (hK.mono_domain (subset_closure.trans hUR))).mono
      (show K ∩ clusterOn μ U z t ⊆ K ∩ U from
        fun _ hx => ⟨hx.1, hx.2.1⟩)



end HarmonicBalls
