import HarmonicBalls.Proofs.Sec5.LocalCountableDeletion

/-! # Admissibility after relatively countable deletions

The punctured infimum is admissible precisely when the full-domain infimum
vanishes at every deleted interior point. -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- The full-domain least supersolution remains admissible after a relatively
closed countable deletion if it vanishes on the deleted interior points. -/
theorem supersolution_mem_sdiff_of_relative_countable_interior_zero
    {μ : Measure ℂ} {U K : Set ℂ} {R t : ℝ} {z : ℂ} {w : ℂ → ℝ}
    (hU : IsOpen U) (hUR : U ⊆ ball (0 : ℂ) R)
    (hD : IsOpen (U \ K)) (hK : (K ∩ U).Countable)
    (hz : z ∈ U \ K) (hw : w ∈ supersolutionsOn μ U z t)
    (hzero : ∀ a ∈ K, a ∈ U → w a = 0) :
    w ∈ supersolutionsOn μ (U \ K) z t := by
  have hcl : closure (U \ K) ⊆ closure U := closure_mono sdiff_subset
  refine ⟨hw.1.mono hcl, hw.2.1.mono_set sdiff_subset, ?_⟩
  intro y hy hyz
  by_cases hyD : y ∈ U \ K
  · rw [greenFunction_sdiff_of_relative_countable hU hUR hD hK hz hyD hyz]
    exact hw.2.2 y (hcl hy) hyz
  · rw [greenFunction_of_notMem_right hyD, mul_zero]
    by_cases hyU : y ∈ U
    · have hyK : y ∈ K := by simpa [hyU] using hyD
      rw [hzero y hyK hyU]
    · have h := hw.2.2 y (hcl hy) hyz
      rwa [greenFunction_of_notMem_right hyU, mul_zero] at h

/-- Admissibility after a relatively countable deletion forces the original
least supersolution to vanish at every deleted interior point. -/
theorem leastSupersolutionOn_eq_zero_of_relative_countable_admissible
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R) (hD : IsOpen (U \ K))
    (hK : (K ∩ U).Countable) (hz : z ∈ U \ K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t) (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hadm : leastSupersolutionOn μ (U \ K) z t ∈ supersolutionsOn μ (U \ K) z t)
    {a : ℂ} (haK : a ∈ K) (haU : a ∈ U) :
    leastSupersolutionOn μ U z t a = 0 := by
  let L := closure (U ∩ K)
  have heq : U \ L = U \ K := sdiff_closure_inter_eq_of_isOpen_sdiff hD
  have hcount : (L ∩ U).Countable := by
    dsimp [L]
    simpa only [closure_inter_eq_inter_of_isOpen_sdiff hD] using hK
  have haL : a ∈ L := subset_closure ⟨haU, haK⟩
  have hzL : z ∈ U \ L := by rwa [heq]
  have hclU : closure (U \ L) = closure U := closure_sdiff_countable_inter hU hcount
  let V : Set ℂ := U \ {z}
  have hVo : IsOpen V := hU.sdiff isClosed_singleton
  have hclV : closure (V \ L) = closure V := closure_sdiff_countable_inter hVo
    (hcount.mono (show L ∩ V ⊆ L ∩ U from fun _ hy => ⟨hy.1, hy.2.1⟩))
  have haz : a ≠ z := fun h => hz.2 (h ▸ haK)
  have heqV : EqOn (leastSupersolutionOn μ (U \ L) z t)
      (leastSupersolutionOn μ U z t) (V \ L) := by
    intro y hy
    exact leastSupersolutionOn_sdiff_eq_of_local_countable hμ hU hUb hUR
      isClosed_closure hcount hqc hq ht hzL hw ⟨hy.1.1, hy.2⟩ (by simpa using hy.1.2)
  have hadmL : leastSupersolutionOn μ (U \ L) z t ∈ supersolutionsOn μ (U \ L) z t := by
    simpa only [heq] using hadm
  have hext := heqV.of_subset_closure
    (hadmL.1.mono (by rw [hclU]; exact sdiff_subset.trans subset_closure))
    (hw.1.mono (sdiff_subset.trans subset_closure)) sdiff_subset
    (by rw [hclV]; exact subset_closure)
  have haCl : a ∈ closure (U \ L) := by rw [hclU]; exact subset_closure haU
  have hzero := leastSupersolutionOn_eq_zero_of_boundary (μ := μ)
    (hUb.subset (show U \ L ⊆ U from sdiff_subset)) ht haCl
    (show a ∉ U \ L from fun ha => ha.2 haL) haz
  exact (hext ⟨haU, by simpa using haz⟩).symm.trans hzero

/-- The punctured-domain infimum is admissible exactly when the full-domain
infimum vanishes at the deleted points, for relatively closed countable deletions. -/
theorem leastSupersolutionOn_mem_sdiff_iff_relative_countable_interior_zero
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R) (hD : IsOpen (U \ K))
    (hK : (K ∩ U).Countable) (hz : z ∈ U \ K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t) (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t) :
    leastSupersolutionOn μ (U \ K) z t ∈ supersolutionsOn μ (U \ K) z t ↔
      ∀ a ∈ K, a ∈ U → leastSupersolutionOn μ U z t a = 0 := by
  constructor
  · intro hadm a haK haU
    exact leastSupersolutionOn_eq_zero_of_relative_countable_admissible
      hμ hU hUb hUR hD hK hz hqc hq ht hw hadm haK haU
  · intro hzero
    have hv := supersolution_mem_sdiff_of_relative_countable_interior_zero
      hU (subset_closure.trans hUR) hD hK hz hw hzero
    let L := closure (U ∩ K)
    have heq : U \ L = U \ K := sdiff_closure_inter_eq_of_isOpen_sdiff hD
    have hcount : (L ∩ U).Countable := by
      dsimp [L]
      simpa only [closure_inter_eq_inter_of_isOpen_sdiff hD] using hK
    have hcl : closure (U \ K) = closure U := by
      rw [← heq]
      exact closure_sdiff_countable_inter hU hcount
    have hbound : ∀ x ∈ closure U, ∀ w ∈ supersolutionsOn μ (U \ K) z t,
        leastSupersolutionOn μ U z t x ≤ w x := by
      intro x hx w hw'
      have hwU := local_countable_punctured_supersolution_mem_domain hμ hU hUb
        isClosed_closure hcount hqc hq ht
          (show w ∈ supersolutionsOn μ (U \ L) z t from by rw [heq]; exact hw')
      by_cases hxz : x = z
      · subst x
        have hcv : ContinuousAt (leastSupersolutionOn μ U z t) z :=
          (hw.1.mono subset_closure).continuousAt (hU.mem_nhds hz.1)
        have hcw : ContinuousAt w z :=
          (hwU.1.mono subset_closure).continuousAt (hU.mem_nhds hz.1)
        have : (𝓝[{z}ᶜ] z).NeBot := by
          apply mem_closure_iff_nhdsWithin_neBot.mp
          exact (dense_compl_singleton z) z
        apply le_of_tendsto_of_tendsto (b := 𝓝[{z}ᶜ] z)
          (hcv.tendsto.mono_left nhdsWithin_le_nhds)
          (hcw.tendsto.mono_left nhdsWithin_le_nhds)
        filter_upwards [(show ∀ᶠ y in 𝓝 z, y ∈ U from hU.mem_nhds hz.1).filter_mono nhdsWithin_le_nhds,
          self_mem_nhdsWithin] with y hyU hyz
        exact leastSupersolutionOn_le_of_mem hwU (subset_closure hyU) (by simpa using hyz)
      · exact leastSupersolutionOn_le_of_mem hwU hx hxz
    have heq' : EqOn (leastSupersolutionOn μ (U \ K) z t)
        (leastSupersolutionOn μ U z t) (closure U) := by
      intro x hx
      have hbdd : BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ (U \ K) z t) := by
        refine ⟨leastSupersolutionOn μ U z t x, ?_⟩
        rintro _ ⟨w, hw', rfl⟩
        exact hbound x hx w hw'
      apply le_antisymm
      · exact csInf_le hbdd ⟨_, hv, rfl⟩
      · apply le_csInf (show ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ (U \ K) z t).Nonempty from ⟨_, ⟨_, hv, rfl⟩⟩)
        rintro _ ⟨w, hw', rfl⟩
        exact hbound x hx w hw'
    refine ⟨hv.1.congr (heq'.mono (by rw [hcl])), ?_, ?_⟩
    · exact hv.2.1.congr_eqOn hD.measurableSet
        (heq'.symm.mono (sdiff_subset.trans subset_closure))
    · intro x hx hxz
      rw [heq' (hcl ▸ hx)]
      exact hv.2.2 x hx hxz

/-- If the punctured infimum is admissible, every deleted point with
positive Green function lies in the original cluster. -/
theorem mem_clusterOn_of_relative_countable_admissible_of_green_pos
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z a : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R) (hD : IsOpen (U \ K))
    (hK : (K ∩ U).Countable) (hz : z ∈ U \ K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hadm : leastSupersolutionOn μ (U \ K) z t ∈ supersolutionsOn μ (U \ K) z t)
    (haK : a ∈ K) (haU : a ∈ U) (hpos : 0 < greenFunction U z a) :
    a ∈ clusterOn μ U z t := by
  have hzero := leastSupersolutionOn_eq_zero_of_relative_countable_admissible
    hμ hU hUb hUR hD hK hz hqc hq ht.le hw hadm haK haU
  refine ⟨haU, Or.inr ?_⟩
  rw [hzero]
  have := mul_pos ht hpos
  linarith

/-- A deleted point of positive Green function outside the original cluster
prevents admissibility of the punctured infimum. -/
theorem not_mem_supersolutionsOn_sdiff_of_relative_countable_green_pos
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z a : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R) (hD : IsOpen (U \ K))
    (hK : (K ∩ U).Countable) (hz : z ∈ U \ K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (haK : a ∈ K) (haU : a ∈ U) (hpos : 0 < greenFunction U z a)
    (ha : a ∉ clusterOn μ U z t) :
    leastSupersolutionOn μ (U \ K) z t ∉ supersolutionsOn μ (U \ K) z t := by
  intro hadm
  exact ha (mem_clusterOn_of_relative_countable_admissible_of_green_pos
    hμ hU hUb hUR hD hK hz hqc hq ht hw hadm haK haU hpos)

/-- If the punctured cluster is compactly contained in the punctured domain,
a deleted interior point of positive Green function prevents admissibility. -/
theorem not_mem_supersolutionsOn_sdiff_of_relative_countable_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z a : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R) (hD : IsOpen (U \ K))
    (hK : (K ∩ U).Countable) (hz : z ∈ U \ K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t) (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopen : IsOpen (clusterOn μ U z t))
    (hcl : closure (clusterOn μ (U \ K) z t) ⊆ U \ K)
    (haK : a ∈ K) (haU : a ∈ U) (hpos : 0 < greenFunction U z a) :
    leastSupersolutionOn μ (U \ K) z t ∉ supersolutionsOn μ (U \ K) z t := by
  intro hadm
  have ha := mem_clusterOn_of_relative_countable_admissible_of_green_pos
    hμ hU hUb hUR hD hK hz hqc hq ht hw hadm haK haU hpos
  have hc := closure_clusterOn_sdiff_of_relative_countable hμ hU hUb hUR
    hD hK hqc hq ht.le hz hw hopen
  have ha' : a ∈ closure (clusterOn μ (U \ K) z t) := by
    rw [hc]
    exact subset_closure ha
  exact (hcl ha').2 haK

#print axioms supersolution_mem_sdiff_of_relative_countable_interior_zero
#print axioms leastSupersolutionOn_eq_zero_of_relative_countable_admissible
#print axioms leastSupersolutionOn_mem_sdiff_iff_relative_countable_interior_zero
#print axioms mem_clusterOn_of_relative_countable_admissible_of_green_pos
#print axioms not_mem_supersolutionsOn_sdiff_of_relative_countable_green_pos
#print axioms not_mem_supersolutionsOn_sdiff_of_relative_countable_compact_containment

end HarmonicBalls
