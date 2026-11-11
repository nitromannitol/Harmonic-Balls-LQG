import HarmonicBalls.Proofs.Sec5.IrregularLeastSupersolution

/-! # General-domain infimum semantics

The underlying potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Set

/-- At every non-pole point of the closed domain the real infimum is the
actual greatest lower bound of the competitor values. -/
theorem isGLB_supersolutionsOn_values_of_ne_pole
    {μ : Measure ℂ} {U : Set ℂ} (hUb : Bornology.IsBounded U)
    {z x : ℂ} {t : ℝ} (ht : 0 ≤ t) (hx : x ∈ closure U) (hxz : x ≠ z) :
    IsGLB ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ U z t)
      (leastSupersolutionOn μ U z t x) := by
  apply isGLB_csInf
  · exact ⟨0, 0, zero_mem_supersolutionsOn hUb ht, rfl⟩
  · exact ⟨-t * greenFunction U z x, by
      rintro _ ⟨w, hw, rfl⟩
      exact hw.2.2 x hx hxz⟩

/-- A real number lies below the least supersolution precisely when it bounds
all competitor values below. -/
theorem le_leastSupersolutionOn_iff_of_ne_pole
    {μ : Measure ℂ} {U : Set ℂ} (hUb : Bornology.IsBounded U)
    {z x : ℂ} {t a : ℝ} (ht : 0 ≤ t) (hx : x ∈ closure U) (hxz : x ≠ z) :
    a ≤ leastSupersolutionOn μ U z t x ↔
      ∀ w ∈ supersolutionsOn μ U z t, a ≤ w x := by
  constructor
  · intro ha w hw
    exact ha.trans (leastSupersolutionOn_le_of_mem hw hx hxz)
  · intro ha
    apply (isGLB_supersolutionsOn_values_of_ne_pole hUb ht hx hxz).2
    rintro _ ⟨w, hw, rfl⟩
    exact ha w hw

/-- Strictly above the infimum there is a competitor with a smaller value. -/
theorem exists_supersolutionOn_lt_of_leastSupersolutionOn_lt
    {μ : Measure ℂ} {U : Set ℂ} (hUb : Bornology.IsBounded U)
    {z x : ℂ} {t a : ℝ} (ht : 0 ≤ t)
    (h : leastSupersolutionOn μ U z t x < a) :
    ∃ w ∈ supersolutionsOn μ U z t, w x < a := by
  obtain ⟨_, ⟨w, hw, rfl⟩, hwlt⟩ := exists_lt_of_csInf_lt
    (show ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ U z t).Nonempty from
      ⟨0, 0, zero_mem_supersolutionsOn hUb ht, rfl⟩) h
  exact ⟨w, hw, hwlt⟩

/-- The complete extended-real infimum agrees with the frozen real infimum
at every off-pole point of the closed domain. -/
theorem coe_leastSupersolutionOn_eq_sInf_ereal_of_ne_pole
    {μ : Measure ℂ} {U : Set ℂ} (hUb : Bornology.IsBounded U)
    {z x : ℂ} {t : ℝ} (ht : 0 ≤ t) (hx : x ∈ closure U) (hxz : x ≠ z) :
    (leastSupersolutionOn μ U z t x : EReal) =
      sInf ((fun w : ℂ → ℝ => (w x : EReal)) '' supersolutionsOn μ U z t) := by
  let S := (fun w : ℂ → ℝ => (w x : EReal)) '' supersolutionsOn μ U z t
  have hlo : (leastSupersolutionOn μ U z t x : EReal) ≤ sInf S := by
    apply le_sInf
    rintro _ ⟨w, hw, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (leastSupersolutionOn_le_of_mem hw hx hxz)
  have hup : sInf S ≤ (0 : EReal) := by
    apply sInf_le
    exact ⟨0, zero_mem_supersolutionsOn hUb ht, rfl⟩
  have htop : sInf S ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hup EReal.zero_lt_top)
  have hbot : sInf S ≠ ⊥ := ne_of_gt
    (lt_of_lt_of_le (EReal.bot_lt_coe _) hlo)
  have hreal : (sInf S).toReal ≤ leastSupersolutionOn μ U z t x := by
    apply (le_leastSupersolutionOn_iff_of_ne_pole hUb ht hx hxz).2
    intro w hw
    apply EReal.coe_le_coe_iff.mp
    rw [EReal.coe_toReal htop hbot]
    exact sInf_le ⟨w, hw, rfl⟩
  exact le_antisymm hlo (by
    rw [← EReal.coe_toReal htop hbot]
    exact EReal.coe_le_coe_iff.mpr hreal)

/-- Pole insertion affects closure only by adjoining the pole to the closure
of the strict off-pole noncontact set. -/
theorem closure_clusterOn_eq_insert_pole {μ : Measure ℂ} {U : Set ℂ}
    {z : ℂ} {t : ℝ} (hz : z ∈ U) :
    closure (clusterOn μ U z t) =
      insert z (closure {x ∈ U | x ≠ z ∧
        -t * greenFunction U z x < leastSupersolutionOn μ U z t x}) := by
  have heq : clusterOn μ U z t = {z} ∪ {x ∈ U | x ≠ z ∧
      -t * greenFunction U z x < leastSupersolutionOn μ U z t x} := by
    ext x
    simp only [clusterOn, mem_ofPred_eq, mem_union, mem_singleton_iff]
    by_cases h : x = z <;> simp [h, hz]
  rw [heq, closure_union, closure_singleton, singleton_union]

end HarmonicBalls
