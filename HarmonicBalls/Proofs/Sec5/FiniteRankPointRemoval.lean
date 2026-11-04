import HarmonicBalls.Proofs.Sec5.AccumulatingPointRemoval

/-! # Removal of finite-rank locally finite point sets -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Laplacian

/-- Iterated local finiteness: at each successor rank, the set is locally
finite outside a closed set of smaller rank. -/
def LocallyFiniteRank (U : Set ℂ) : ℕ → Set ℂ → Prop
  | 0, K => ∀ C : Set ℂ, IsCompact C → C ⊆ U → (K ∩ C).Finite
  | n + 1, K => ∃ L : Set ℂ, IsClosed L ∧ LocallyFiniteRank U n L ∧
      ∀ C : Set ℂ, IsCompact C → C ⊆ U \ L → (K ∩ C).Finite

/-- A finite-rank locally finite set is countable inside the open domain. -/
theorem countable_inter_open_of_locallyFiniteRank {U K : Set ℂ}
    (hU : IsOpen U) {n : ℕ} (hK : LocallyFiniteRank U n K) :
    (K ∩ U).Countable := by
  induction n generalizing K with
  | zero => exact countable_inter_open_of_locally_finite hU hK
  | succ n ih =>
    obtain ⟨L, hLc, hL, hK⟩ := hK
    have hk := countable_inter_open_of_locally_finite (hU.sdiff hLc) hK
    have hl := ih hL
    apply (hk.union hl).mono
    intro x hx
    by_cases hxL : x ∈ L
    · exact Or.inr ⟨hxL, hx.2⟩
    · exact Or.inl ⟨hx.1, hx.2, hxL⟩

/-- A continuous weak supersolution extends across a finite-rank locally
finite set. -/
theorem laplacianLE_zero_of_locallyFiniteRank_removal {U K : Set ℂ}
    (hU : IsOpen U) {n : ℕ} (hK : LocallyFiniteRank U n K)
    {w : ℂ → ℝ} (hwc : ContinuousOn w U) (hw : LaplacianLE w 0 (U \ K)) :
    LaplacianLE w 0 U := by
  induction n generalizing K with
  | zero => exact laplacianLE_zero_of_locally_finite_removal hU hK hwc hw
  | succ n ih =>
    obtain ⟨L, hLc, hL, hK⟩ := hK
    have hremoveK : LaplacianLE w 0 (U \ L) :=
      laplacianLE_zero_of_locally_finite_removal (hU.sdiff hLc) hK
        (hwc.mono sdiff_subset) (hw.mono_set (fun _ hx => ⟨hx.1.1, hx.2⟩))
    exact ih hL hremoveK

/-- Removal also holds for a measure-valued weak Laplacian when the measure
has a continuous potential. -/
theorem laplacianLE_of_locallyFiniteRank_removal {μ : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ} (hU : IsOpen U)
    {n : ℕ} (hK : LocallyFiniteRank U n K) {w q : ℂ → ℝ}
    (hwc : ContinuousOn w U) (hqc : ContinuousOn q U)
    (hq : HasLaplacian q 0 μ U) (hw : LaplacianLE w μ (U \ K)) :
    LaplacianLE w μ U := by
  have hp := (laplacianLE_iff_add_potential hμ (hq.mono_domain sdiff_subset)).mp hw
  exact (laplacianLE_iff_add_potential hμ hq).mpr
    (laplacianLE_zero_of_locallyFiniteRank_removal hU hK (hwc.add hqc) hp)

/-- A supersolution on a bounded open domain minus a finite-rank locally
finite set extends to the whole domain. -/
theorem finiteRank_punctured_supersolution_mem_domain
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) {n : ℕ}
    (hK : LocallyFiniteRank U n K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    {z : ℂ} {t : ℝ} (ht : 0 ≤ t) {w : ℂ → ℝ}
    (hw : w ∈ supersolutionsOn μ (U \ K) z t) : w ∈ supersolutionsOn μ U z t := by
  have hcl : closure (U \ K) = closure U :=
    closure_sdiff_countable_inter hU (countable_inter_open_of_locallyFiniteRank hU hK)
  refine ⟨by simpa only [hcl] using hw.1, ?_, ?_⟩
  · exact laplacianLE_of_locallyFiniteRank_removal hμ hU hK
      (hw.1.mono (by rw [hcl]; exact subset_closure)) hqc hq hw.2.1
  · intro x hx hxz
    have hwx := hw.2.2 x (hcl ▸ hx) hxz
    have hG := Section6.greenFunction_le_of_subset (show U \ K ⊆ U from sdiff_subset) hUb z x
    nlinarith

/-- The original-domain infimum bounds the punctured-domain infimum from
below, away from the pole. -/
theorem leastSupersolutionOn_le_finiteRank_punctured
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) {n : ℕ}
    (hK : LocallyFiniteRank U n K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    {z x : ℂ} {t : ℝ} (ht : 0 ≤ t) (hx : x ∈ closure U) (hxz : x ≠ z) :
    leastSupersolutionOn μ U z t x ≤ leastSupersolutionOn μ (U \ K) z t x := by
  apply le_csInf
  · exact ⟨_, ⟨0, zero_mem_supersolutionsOn (hUb.subset sdiff_subset) ht, rfl⟩⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact leastSupersolutionOn_le_of_mem
      (finiteRank_punctured_supersolution_mem_domain hμ hU hUb hK hqc hq ht hw) hx hxz

/-- All-scales volume growth supplies the potential for any bounded open
planar domain. -/
theorem leastSupersolutionOn_le_finiteRank_punctured_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp) {U K : Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) {n : ℕ}
    (hK : LocallyFiniteRank U n K)
    {z x : ℂ} {t : ℝ} (ht : 0 ≤ t) (hx : x ∈ closure U) (hxz : x ≠ z) :
    leastSupersolutionOn μ U z t x ≤ leastSupersolutionOn μ (U \ K) z t x := by
  obtain ⟨r, hr⟩ := hUb.subset_ball (0 : ℂ)
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right r 1)
  have hsub : U ⊆ ball (0 : ℂ) R := hr.trans (ball_subset_ball (le_max_left r 1))
  exact leastSupersolutionOn_le_finiteRank_punctured hμ hU hUb hK
    ((greenPotentialBallContinuousStep_holds μ hμ R βm βp hR (hV R hR)).mono
      (hsub.trans ball_subset_closedBall))
    ((greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR (hV R hR)).mono_domain hsub)
    ht hx hxz

#print axioms countable_inter_open_of_locallyFiniteRank
#print axioms laplacianLE_of_locallyFiniteRank_removal
#print axioms finiteRank_punctured_supersolution_mem_domain
#print axioms leastSupersolutionOn_le_finiteRank_punctured
#print axioms leastSupersolutionOn_le_finiteRank_punctured_of_volumeGrowth

end HarmonicBalls
