import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstBumps
import HarmonicBalls.Proofs.Sec11.MassDiameterBudget

/-! # Smooth core contraction for the mass-diameter construction -/

namespace HarmonicBalls
open Set
open scoped ContDiff

/-- A compact core neighborhood can be contracted by a smooth Weyl weight
    supported in an open set that avoids the protected mass set. -/
theorem exists_smooth_core_contraction_weight
    {O₀ O S : Set ℂ} (hcompact : IsCompact (closure O₀))
    (hO : IsOpen O) (hinside : closure O₀ ⊆ O) (hdisjoint : Disjoint O S)
    {ξ B : ℝ} (hξ : 0 < ξ) (hB : B ≤ 0) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧
      (∀ z, f z ≤ 0) ∧ (∀ z, ξ * f z ≤ 0) ∧
      (∀ z ∈ O₀, ξ * f z = B) ∧
      (∀ z ∈ S, f z = 0) ∧ (∀ z ∉ O, f z = 0) := by
  obtain ⟨φ, hφsmooth, hφcompact, hφrange, hφone, hφzero⟩ :=
    exists_smooth_compact_cutoff hcompact hO hinside
  let a : ℝ := B / ξ
  let f : ℂ → ℝ := fun z => a * φ z
  have ha : a ≤ 0 := div_nonpos_of_nonpos_of_nonneg hB hξ.le
  have hf : IsTestFunction univ f := by
    refine ⟨contDiff_const.mul hφsmooth, hφcompact.mul_left, ?_⟩
    exact subset_univ _
  refine ⟨f, hf, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    exact mul_nonpos_of_nonpos_of_nonneg ha (hφrange z).1
  · intro z
    exact mul_nonpos_of_nonneg_of_nonpos hξ.le
      (mul_nonpos_of_nonpos_of_nonneg ha (hφrange z).1)
  · intro z hz
    simp only [f, hφone z (subset_closure hz), mul_one, a]
    field_simp
  · intro z hz
    have hzO : z ∉ O := fun hzO => disjoint_left.mp hdisjoint hzO hz
    simp [f, hφzero z hzO]
  · intro z hz
    simp [f, hφzero z hz]

/-- If the entrance costs leave a margin, one smooth interior weight supplies
    both the Weyl bounds and the strict core-gluing budget. -/
theorem exists_smooth_core_contraction_weight_with_budget
    {O₀ O S : Set ℂ} (hcompact : IsCompact (closure O₀))
    (hO : IsOpen O) (hinside : closure O₀ ⊆ O) (hdisjoint : Disjoint O S)
    {ξ a b ε : ℝ} (hξ : 0 < ξ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hmargin : a + a < ε) :
    ∃ (B : ℝ) (f : ℂ → ℝ), IsTestFunction univ f ∧
      (∀ z, f z ≤ 0) ∧ (∀ z, ξ * f z ≤ 0) ∧
      (∀ z ∈ O₀, ξ * f z = B) ∧ (∀ z ∈ S, f z = 0) ∧
      (∀ z ∉ O, f z = 0) ∧
      ENNReal.ofReal a + ENNReal.ofReal (Real.exp B) * ENNReal.ofReal b +
        ENNReal.ofReal a < ENNReal.ofReal ε := by
  obtain ⟨B, hB, hbudget⟩ := exists_negative_weyl_core_budget ha hb hmargin
  obtain ⟨f, hf, hnonpos, hglobal, hcore, hS, houtside⟩ :=
    exists_smooth_core_contraction_weight hcompact hO hinside hdisjoint hξ hB.le
  exact ⟨B, f, hf, hnonpos, hglobal, hcore, hS, houtside, hbudget⟩

end HarmonicBalls
