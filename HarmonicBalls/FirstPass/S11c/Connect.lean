import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Basic

/-!
# Proposition 11.10, connectivity of the exterior set (fp-S11c, owner n1)

FIRST-PASS NEW. The paper (corrected lines 3022-3024) asserts that `G = S₂ \ ⋃ Ŝ` is connected, with a reason that does
not imply it (separation of the squares alone). This file proves the connectivity from the grid structure: a box
`[a₁,a₂] × [b₁,b₂]` minus a product `Xs ×ˢ Ys` is connected when there are a free abscissa `xh ∉ Xs` and a free
ordinate `yh ∉ Ys` inside the box. Every point of the complement is joined to the hub `xh + i yh` by two segments
(vertical then horizontal, or horizontal then vertical), each staying in the complement.
-/

namespace HarmonicBalls

open Set

theorem isPreconnected_box_diff_prod {a₁ a₂ b₁ b₂ xh yh : ℝ} {Xs Ys : Set ℝ}
    (hxh : xh ∈ Icc a₁ a₂) (hxhX : xh ∉ Xs) (hyh : yh ∈ Icc b₁ b₂) (hyhY : yh ∉ Ys) :
    IsPreconnected ((Icc a₁ a₂ ×ℂ Icc b₁ b₂) \ {z : ℂ | z.re ∈ Xs ∧ z.im ∈ Ys}) := by
  have hcH : ∀ c : ℝ, Continuous (fun s : ℝ => (⟨s, c⟩ : ℂ)) := fun c =>
    Complex.equivRealProdCLM.symm.continuous.comp (continuous_id.prodMk continuous_const)
  have hcV : ∀ c : ℝ, Continuous (fun s : ℝ => (⟨c, s⟩ : ℂ)) := fun c =>
    Complex.equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_id)
  apply isPreconnected_of_forall (⟨xh, yh⟩ : ℂ)
  rintro y ⟨hyS, hyE⟩
  rw [Complex.mem_reProdIm] at hyS
  obtain ⟨hyr, hyi⟩ := hyS
  by_cases hA : y.re ∈ Xs
  · -- here `y.im ∉ Ys`: horizontal segment at height `y.im`, then vertical segment at abscissa `xh`
    have hyiY : y.im ∉ Ys := fun h => hyE ⟨hA, h⟩
    refine ⟨((fun s : ℝ => (⟨s, y.im⟩ : ℂ)) '' uIcc y.re xh) ∪
      ((fun s : ℝ => (⟨xh, s⟩ : ℂ)) '' uIcc y.im yh), ?_, ?_, ?_, ?_⟩
    · rintro z (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
      · exact ⟨Complex.mem_reProdIm.2 ⟨uIcc_subset_Icc hyr hxh hs, hyi⟩, fun h => hyiY h.2⟩
      · exact ⟨Complex.mem_reProdIm.2 ⟨hxh, uIcc_subset_Icc hyi hyh hs⟩, fun h => hxhX h.1⟩
    · exact Or.inr ⟨yh, right_mem_uIcc, rfl⟩
    · exact Or.inl ⟨y.re, left_mem_uIcc, Complex.eta y⟩
    · exact IsPreconnected.union (⟨xh, y.im⟩ : ℂ)
        ⟨xh, right_mem_uIcc, rfl⟩ ⟨y.im, left_mem_uIcc, rfl⟩
        ((isPreconnected_uIcc).image _ (hcH y.im).continuousOn)
        ((isPreconnected_uIcc).image _ (hcV xh).continuousOn)
  · -- here `y.re ∉ Xs`: vertical segment at abscissa `y.re`, then horizontal segment at height `yh`
    refine ⟨((fun s : ℝ => (⟨y.re, s⟩ : ℂ)) '' uIcc y.im yh) ∪
      ((fun s : ℝ => (⟨s, yh⟩ : ℂ)) '' uIcc y.re xh), ?_, ?_, ?_, ?_⟩
    · rintro z (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
      · exact ⟨Complex.mem_reProdIm.2 ⟨hyr, uIcc_subset_Icc hyi hyh hs⟩, fun h => hA h.1⟩
      · exact ⟨Complex.mem_reProdIm.2 ⟨uIcc_subset_Icc hyr hxh hs, hyh⟩, fun h => hyhY h.2⟩
    · exact Or.inr ⟨xh, right_mem_uIcc, rfl⟩
    · exact Or.inl ⟨y.im, left_mem_uIcc, Complex.eta y⟩
    · exact IsPreconnected.union (⟨y.re, yh⟩ : ℂ)
        ⟨yh, right_mem_uIcc, rfl⟩ ⟨y.re, left_mem_uIcc, rfl⟩
        ((isPreconnected_uIcc).image _ (hcV y.re).continuousOn)
        ((isPreconnected_uIcc).image _ (hcH yh).continuousOn)

end HarmonicBalls
