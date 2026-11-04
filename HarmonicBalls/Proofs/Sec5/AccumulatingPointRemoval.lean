import HarmonicBalls.Proofs.Sec5.LocallyFinitePointRemoval
import HarmonicBalls.Proofs.Sec5.GeneralDomainMonotonicity

/-! # Removal of point sets with locally finite accumulation -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Laplacian

/-- A locally finite point set is countable in an open planar domain. -/
theorem countable_inter_open_of_locally_finite {U K : Set ℂ} (hU : IsOpen U)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ U → (K ∩ C).Finite) :
    (K ∩ U).Countable := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  have hσ : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  obtain ⟨C, hC, hcover⟩ := hσ
  have hCU : ∀ n, C n ⊆ U := by
    intro n x hx
    rw [← hcover]
    exact mem_iUnion.mpr ⟨n, hx⟩
  apply (Set.countable_iUnion fun n => (hK (C n) (hC n) (hCU n)).countable).mono
  intro x hx
  have hxU : x ∈ ⋃ n, C n := hcover.symm ▸ hx.2
  obtain ⟨n, hn⟩ := mem_iUnion.mp hxU
  exact mem_iUnion.mpr ⟨n, hx.1, hn⟩

/-- A set locally finite away from locally finite accumulation points is
countable in the domain. -/
theorem countable_inter_open_of_locally_finite_accumulation {U K L : Set ℂ}
    (hU : IsOpen U) (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ U → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ U \ L → (K ∩ C).Finite) :
    (K ∩ U).Countable := by
  have hk := countable_inter_open_of_locally_finite (hU.sdiff hLclosed) hK
  have hl := countable_inter_open_of_locally_finite hU hL
  apply (hk.union hl).mono
  intro x hx
  by_cases hxL : x ∈ L
  · exact Or.inr ⟨hxL, hx.2⟩
  · exact Or.inl ⟨hx.1, hx.2, hxL⟩

/-- A continuous weak supersolution extends across a set that is locally
finite away from a closed, locally finite set of possible accumulation points. -/
theorem laplacianLE_zero_of_locally_finite_accumulation_removal
    {U K L : Set ℂ} (hU : IsOpen U) (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ U → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ U \ L → (K ∩ C).Finite)
    {w : ℂ → ℝ} (hwc : ContinuousOn w U) (hw : LaplacianLE w 0 (U \ K)) :
    LaplacianLE w 0 U := by
  have hUL : IsOpen (U \ L) := hU.sdiff hLclosed
  have hremoveK : LaplacianLE w 0 (U \ L) :=
    laplacianLE_zero_of_locally_finite_removal hUL hK (hwc.mono sdiff_subset)
      (hw.mono_set (fun _ hx => ⟨hx.1.1, hx.2⟩))
  exact laplacianLE_zero_of_locally_finite_removal hU hL hwc hremoveK

/-- The same removal principle applies to a measure-valued weak Laplacian
when the measure has a continuous potential. -/
theorem laplacianLE_of_locally_finite_accumulation_removal
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K L : Set ℂ}
    (hU : IsOpen U) (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ U → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ U \ L → (K ∩ C).Finite)
    {w q : ℂ → ℝ} (hwc : ContinuousOn w U) (hqc : ContinuousOn q U)
    (hq : HasLaplacian q 0 μ U) (hw : LaplacianLE w μ (U \ K)) :
    LaplacianLE w μ U := by
  have hp := (laplacianLE_iff_add_potential hμ (hq.mono_domain sdiff_subset)).mp hw
  exact (laplacianLE_iff_add_potential hμ hq).mpr
    (laplacianLE_zero_of_locally_finite_accumulation_removal hU hLclosed hL hK
      (hwc.add hqc) hp)

/-- A countable deletion does not change the closure of an open planar set. -/
theorem closure_sdiff_countable_inter {U K : Set ℂ} (hU : IsOpen U)
    (hK : (K ∩ U).Countable) : closure (U \ K) = closure U := by
  apply Subset.antisymm (closure_mono sdiff_subset)
  apply closure_minimal _ isClosed_closure
  have hd : Dense (K ∩ U)ᶜ := hK.dense_compl ℂ
  intro x hx
  have hxcl := hd.open_subset_closure_inter hU hx
  apply closure_mono (show U ∩ (K ∩ U)ᶜ ⊆ U \ K from ?_) hxcl
  intro y hy
  exact ⟨hy.1, fun hyK => hy.2 ⟨hyK, hy.1⟩⟩

/-- A supersolution on a punctured bounded open set extends to the whole set
when its measure admits a continuous potential there. -/
theorem accumulating_punctured_supersolution_mem_domain
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K L : Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ U → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ U \ L → (K ∩ C).Finite)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    {z : ℂ} {t : ℝ} (ht : 0 ≤ t) {w : ℂ → ℝ}
    (hw : w ∈ supersolutionsOn μ (U \ K) z t) : w ∈ supersolutionsOn μ U z t := by
  have hcl : closure (U \ K) = closure U :=
    closure_sdiff_countable_inter hU
      (countable_inter_open_of_locally_finite_accumulation hU hLclosed hL hK)
  refine ⟨by simpa only [hcl] using hw.1, ?_, ?_⟩
  · exact laplacianLE_of_locally_finite_accumulation_removal hμ hU hLclosed hL hK
      (hw.1.mono (by rw [hcl]; exact subset_closure)) hqc hq hw.2.1
  · intro x hx hxz
    have hwx := hw.2.2 x (hcl ▸ hx) hxz
    have hG := Section6.greenFunction_le_of_subset (show U \ K ⊆ U from sdiff_subset) hUb z x
    nlinarith

/-- The least supersolution on the original domain bounds the punctured
least supersolution from below. -/
theorem leastSupersolutionOn_le_accumulating_punctured
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K L : Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ U → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ U \ L → (K ∩ C).Finite)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    {z x : ℂ} {t : ℝ} (ht : 0 ≤ t) (hx : x ∈ closure U) (hxz : x ≠ z) :
    leastSupersolutionOn μ U z t x ≤ leastSupersolutionOn μ (U \ K) z t x := by
  apply le_csInf
  · exact ⟨_, ⟨0, zero_mem_supersolutionsOn (hUb.subset sdiff_subset) ht, rfl⟩⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact leastSupersolutionOn_le_of_mem
      (accumulating_punctured_supersolution_mem_domain hμ hU hUb hLclosed hL hK hqc hq ht hw)
      hx hxz

/-- All-scales volume growth supplies the continuous potential needed for
the comparison on an arbitrary bounded open domain. -/
theorem leastSupersolutionOn_le_accumulating_punctured_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV : ∀ r : ℝ, 0 < r → VolumeGrowth μ r βm βp) {U K L : Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ U → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ U \ L → (K ∩ C).Finite)
    {z x : ℂ} {t : ℝ} (ht : 0 ≤ t) (hx : x ∈ closure U) (hxz : x ≠ z) :
    leastSupersolutionOn μ U z t x ≤ leastSupersolutionOn μ (U \ K) z t x := by
  obtain ⟨r, hr⟩ := hUb.subset_ball (0 : ℂ)
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right r 1)
  have hsub : U ⊆ ball (0 : ℂ) R := hr.trans (ball_subset_ball (le_max_left r 1))
  exact leastSupersolutionOn_le_accumulating_punctured hμ hU hUb hLclosed hL hK
    ((greenPotentialBallContinuousStep_holds μ hμ R βm βp hR (hV R hR)).mono
      (hsub.trans ball_subset_closedBall))
    ((greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR (hV R hR)).mono_domain hsub)
    ht hx hxz

/-- Continuous supersolutions on a countably punctured disc remain
supersolutions on the disc when the possible accumulation points are locally
finite. -/
theorem accumulating_punctured_disc_supersolution_mem_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (ht : 0 ≤ t)
    {K L : Set ℂ} (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ L → (K ∩ C).Finite)
    {z : ℂ} {w : ℂ → ℝ}
    (hw : w ∈ supersolutionsOn μ (ball (0 : ℂ) R \ K) z t) :
    w ∈ supersolutions μ R z t := by
  have hcl : closure (ball (0 : ℂ) R \ K) = closedBall 0 R := by
    rw [closure_sdiff_countable_inter isOpen_ball
      (countable_inter_open_of_locally_finite_accumulation isOpen_ball hLclosed hL hK),
      closure_ball (0 : ℂ) hR.ne']
  refine ⟨by simpa only [hcl] using hw.1, ?_, ?_⟩
  · exact laplacianLE_of_locally_finite_accumulation_removal hμ isOpen_ball hLclosed hL hK
      (hw.1.mono (by rw [hcl]; exact ball_subset_closedBall))
      ((greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV).mono ball_subset_closedBall)
      (greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR hV) hw.2.1
  · intro x hx hxz
    have hwx := hw.2.2 x (hcl ▸ hx) hxz
    have hG := Section6.greenFunction_le_of_subset
      (show ball (0 : ℂ) R \ K ⊆ ball 0 R from sdiff_subset) isBounded_ball z x
    nlinarith

/-- The full-disc least supersolution bounds from below the least
supersolution after such a deletion. -/
theorem leastSupersolution_le_accumulating_punctured_disc
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (ht : 0 ≤ t)
    {K L : Set ℂ} (hLclosed : IsClosed L)
    (hL : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R → (L ∩ C).Finite)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ L → (K ∩ C).Finite)
    {z x : ℂ} (hx : x ∈ closedBall (0 : ℂ) R) (hxz : x ≠ z) :
    leastSupersolution μ R z t x ≤ leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t x := by
  apply le_csInf
  · exact ⟨_, ⟨0, zero_mem_supersolutionsOn (isBounded_ball.subset sdiff_subset) ht, rfl⟩⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact leastSupersolution_le
      (accumulating_punctured_disc_supersolution_mem_disc hμ hR hV ht hLclosed hL hK hw)
      hx hxz

/-- A countable family of punctures with at most one accumulation point has
the same lower comparison with the full-disc least supersolution. -/
theorem leastSupersolution_le_punctured_disc_of_single_accumulation
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (ht : 0 ≤ t)
    {K : Set ℂ} (a : ℂ)
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ ball (0 : ℂ) R \ {a} → (K ∩ C).Finite)
    {z x : ℂ} (hx : x ∈ closedBall (0 : ℂ) R) (hxz : x ≠ z) :
    leastSupersolution μ R z t x ≤ leastSupersolutionOn μ (ball (0 : ℂ) R \ K) z t x := by
  apply leastSupersolution_le_accumulating_punctured_disc hμ hR hV ht
    (L := {a}) isClosed_singleton _ hK hx hxz
  intro C _ _
  exact (Set.finite_singleton a).subset inter_subset_left

#print axioms countable_inter_open_of_locally_finite
#print axioms countable_inter_open_of_locally_finite_accumulation
#print axioms laplacianLE_zero_of_locally_finite_accumulation_removal
#print axioms laplacianLE_of_locally_finite_accumulation_removal
#print axioms closure_sdiff_countable_inter
#print axioms accumulating_punctured_supersolution_mem_domain
#print axioms leastSupersolutionOn_le_accumulating_punctured
#print axioms leastSupersolutionOn_le_accumulating_punctured_of_volumeGrowth
#print axioms accumulating_punctured_disc_supersolution_mem_disc
#print axioms leastSupersolution_le_accumulating_punctured_disc
#print axioms leastSupersolution_le_punctured_disc_of_single_accumulation

end HarmonicBalls
