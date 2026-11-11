import HarmonicBalls.Proofs.Sec5.GeneralDomainGreenExtension
import HarmonicBalls.Proofs.Potential.GreenPositivity

/-! # Compact containment after a thin deletion -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

/-- If the punctured least supersolution is admissible, a deleted interior
point with positive Green function belongs to the full-domain cluster. -/
theorem mem_clusterOn_of_sdiff_admissible_of_green_pos
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z a : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R) (hKc : IsClosed K)
    (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K) (hz : z ∈ U \ K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hadm : leastSupersolutionOn μ (U \ K) z t ∈ supersolutionsOn μ (U \ K) z t)
    (haK : a ∈ K) (haU : a ∈ U) (hpos : 0 < greenFunction U z a) :
    a ∈ clusterOn μ U z t := by
  have hzero := leastSupersolutionOn_eq_zero_of_sdiff_admissible
    hμ hU hUb hUR hKc hK hz hqc hq ht.le hw hadm haK haU
  refine ⟨haU, Or.inr ?_⟩
  rw [hzero]
  have := mul_pos ht hpos
  linarith

/-- A deleted point with positive Green function obstructs admissibility
when the punctured cluster is compactly contained in the punctured domain. -/
theorem not_mem_supersolutionsOn_sdiff_of_green_pos_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z a : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R) (hKc : IsClosed K)
    (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K) (hz : z ∈ U \ K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopen : IsOpen (clusterOn μ U z t))
    (hcl : closure (clusterOn μ (U \ K) z t) ⊆ U \ K)
    (haK : a ∈ K) (haU : a ∈ U) (hpos : 0 < greenFunction U z a) :
    leastSupersolutionOn μ (U \ K) z t ∉ supersolutionsOn μ (U \ K) z t := by
  intro hadm
  have ha := mem_clusterOn_of_sdiff_admissible_of_green_pos
    hμ hU hUb hUR hKc hK hz hqc hq ht hw hadm haK haU hpos
  have heq := closure_clusterOn_sdiff_of_locallyFiniteRankOn
    hμ hU hUb hUR hKc hK hz hqc hq ht.le hw hopen
  have ha' : a ∈ closure (clusterOn μ (U \ K) z t) := by
    rw [heq]
    exact subset_closure ha
  exact (hcl ha').2 haK

/-- The obstruction applies in particular when the deleted point and the
pole lie sufficiently close inside a disc contained in the domain. -/
theorem not_mem_supersolutionsOn_sdiff_of_near_pole_compact_containment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t r : ℝ} {z a : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R) (hKc : IsClosed K)
    (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K) (hz : z ∈ U \ K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (hopen : IsOpen (clusterOn μ U z t))
    (hcl : closure (clusterOn μ (U \ K) z t) ⊆ U \ K)
    (haK : a ∈ K) (hr : 0 < r) (hball : closedBall a r ⊆ U)
    (hza : ‖z - a‖ < r) :
    leastSupersolutionOn μ (U \ K) z t ∉ supersolutionsOn μ (U \ K) z t := by
  have haz : z ≠ a := fun h => hz.2 (h.symm ▸ haK)
  have haU : a ∈ U := hball (mem_closedBall_self hr.le)
  have hpos : 0 < greenFunction U z a :=
    greenFunction_pos hUb hr hball (norm_pos_iff.mpr (sub_ne_zero.mpr haz)) hza
  exact not_mem_supersolutionsOn_sdiff_of_green_pos_compact_containment
    hμ hU hUb hUR hKc hK hz hqc hq ht hw hopen hcl haK haU hpos

/-- A deleted point outside the full-domain cluster obstructs admissibility
whenever the Green function is positive there. -/
theorem not_mem_supersolutionsOn_sdiff_of_green_pos_of_not_mem_clusterOn
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z a : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R) (hKc : IsClosed K)
    (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K) (hz : z ∈ U \ K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 < t)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t)
    (haK : a ∈ K) (haU : a ∈ U) (hpos : 0 < greenFunction U z a)
    (ha : a ∉ clusterOn μ U z t) :
    leastSupersolutionOn μ (U \ K) z t ∉ supersolutionsOn μ (U \ K) z t := by
  intro hadm
  exact ha (mem_clusterOn_of_sdiff_admissible_of_green_pos
    hμ hU hUb hUR hKc hK hz hqc hq ht hw hadm haK haU hpos)

/-- In this setting admissibility is equivalent to continuity of the
punctured infimum on the closure of the punctured domain. -/
theorem leastSupersolutionOn_mem_sdiff_iff_continuousOn
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {U K : Set ℂ}
    {R t : ℝ} {z : ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUR : closure U ⊆ ball (0 : ℂ) R) (hKc : IsClosed K)
    (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K) (hz : z ∈ U \ K)
    {q : ℂ → ℝ} (hqc : ContinuousOn q U) (hq : HasLaplacian q 0 μ U)
    (ht : 0 ≤ t)
    (hw : leastSupersolutionOn μ U z t ∈ supersolutionsOn μ U z t) :
    leastSupersolutionOn μ (U \ K) z t ∈ supersolutionsOn μ (U \ K) z t ↔
      ContinuousOn (leastSupersolutionOn μ (U \ K) z t) (closure (U \ K)) := by
  constructor
  · exact fun hadm => hadm.1
  · intro hcont
    apply (leastSupersolutionOn_mem_sdiff_iff_interior_zero
      hμ hU hUb hUR hKc hK hz hqc hq ht hw).mpr
    intro a haK haU
    have haz : a ≠ z := fun h => hz.2 (h ▸ haK)
    let V : Set ℂ := U \ {z}
    have hVo : IsOpen V := hU.sdiff isClosed_singleton
    have hcount : (K ∩ V).Countable :=
      (countable_inter_open_of_locallyFiniteRankOn hU
        (hK.mono_domain (subset_closure.trans hUR))).mono
        (show K ∩ V ⊆ K ∩ U from fun _ hy => ⟨hy.1, hy.2.1⟩)
    have hclV : closure (V \ K) = closure V := closure_sdiff_countable_inter hVo hcount
    have hclU : closure (U \ K) = closure U := closure_sdiff_countable_inter hU
      (countable_inter_open_of_locallyFiniteRankOn hU
        (hK.mono_domain (subset_closure.trans hUR)))
    have heq : EqOn (leastSupersolutionOn μ (U \ K) z t)
        (leastSupersolutionOn μ U z t) (V \ K) := by
      intro y hy
      exact leastSupersolutionOn_locallyFiniteRankOn_punctured_eq_of_green_eq
        hμ hU hUb hUR hKc hK hqc hq ht
        (fun w hw hwz => greenFunction_sdiff_of_locallyFiniteRankOn hU
          (subset_closure.trans hUR) hKc hK hz hw hwz)
        hw ⟨hy.1.1, hy.2⟩ (by simpa using hy.1.2)
    have heqV := heq.of_subset_closure
      (hcont.mono (by rw [hclU]; exact sdiff_subset.trans subset_closure))
      (hw.1.mono (sdiff_subset.trans subset_closure)) sdiff_subset
      (by rw [hclV]; exact subset_closure)
    have haV : a ∈ V := ⟨haU, by simpa using haz⟩
    have haCl : a ∈ closure (U \ K) := by rw [hclU]; exact subset_closure haU
    have hzero := leastSupersolutionOn_eq_zero_of_boundary (μ := μ)
      (hUb.subset (show U \ K ⊆ U from sdiff_subset)) ht haCl
      (show a ∉ U \ K from fun ha => ha.2 haK) haz
    exact (heqV haV).symm.trans hzero



end HarmonicBalls
