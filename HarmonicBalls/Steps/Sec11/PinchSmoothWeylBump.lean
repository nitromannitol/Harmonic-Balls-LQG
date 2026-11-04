import HarmonicBalls.Steps.Sec11.PinchWeylBump
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Smooth Weyl weights for the auxiliary pinch event

The compactly supported continuous cutoff can be replaced by a smooth one
with the same zero set and the same set where it equals one. -/

namespace HarmonicBalls

open Set Metric Function
open scoped ENNReal ContDiff

/-- A compactly supported continuous `[0,1]`-valued function has a smooth
compactly supported replacement with the same zero set and one set. -/
theorem exists_smooth_cutoff_with_same_zero_and_one (φ : C(ℂ, ℝ))
    (hφ : HasCompactSupport φ) :
    ∃ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (∀ x, ψ x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, φ x = 0 → ψ x = 0) ∧ (∀ x, φ x = 1 → ψ x = 1) := by
  let S : Set ℂ := {x | φ x ≠ 0}
  let K : Set ℂ := {x | φ x = 1}
  have hS : IsOpen S := (isClosed_eq φ.continuous continuous_const).isOpen_compl
  have hK : IsClosed K := isClosed_eq φ.continuous continuous_const
  have hKS : K ⊆ S := by
    intro x hx
    change φ x ≠ 0
    rw [hx]
    norm_num
  obtain ⟨ψ, hψsmooth, hψrange, hψsupp, hψone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hS hK hKS
  have hsupp : support ψ = support φ := hψsupp
  have hψcompact : HasCompactSupport ψ := by
    change IsCompact (closure (support ψ))
    rw [hsupp]
    exact hφ
  refine ⟨ψ, hψsmooth, hψcompact, fun x => hψrange (mem_range_self x), ?_, ?_⟩
  · intro x hx
    by_contra hn
    have hs : x ∈ support ψ := hn
    rw [hsupp] at hs
    exact hs hx
  · intro x hx
    exact (hψone x).1 hx

/-- The third-event bump can be chosen smooth and compactly supported. -/
theorem IsPinchPointProofConfiguration.exists_smooth_third_weyl_bump
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) :
    ∃ φ : ℂ → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      (∀ x ∈ thickening δ (thickening (3 * δ) W \ V), φ x = 1) ∧
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, φ x = 0) ∧
      ∀ x, φ x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨φ, hcompact, hone, hzero, hrange⟩ := h.exists_third_weyl_bump
  obtain ⟨ψ, hsmooth, hcompact, hrange, hzero', hone'⟩ :=
    exists_smooth_cutoff_with_same_zero_and_one φ hcompact
  exact ⟨ψ, hsmooth, hcompact, fun x hx => hone' x (hone x hx),
    fun x hx => hzero' x (hzero x hx), hrange⟩

/-- A prescribed contraction is realized by a smooth compactly supported
nonpositive weight, vanishing on the inner set and central closed disk. -/
theorem IsPinchPointProofConfiguration.exists_smooth_third_weyl_weight
    {U V W T Q' Q : Set ℂ} {δ ξ q : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hξ : 0 < ξ) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ x, f x ≤ 0) ∧
      (∀ x ∈ thickening δ (thickening (3 * δ) W \ V), ξ * f x = Real.log q) ∧
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) ∧
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) := by
  obtain ⟨φ, hφsmooth, hφcompact, hφone, hφzero, hφrange⟩ :=
    h.exists_smooth_third_weyl_bump
  let a : ℝ := Real.log q / ξ
  let f : ℂ → ℝ := fun x => a * φ x
  have ha : a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hq.le hq1) hξ.le
  have hfzero : ∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0 := by
    intro x hx
    simp [f, hφzero x hx]
  refine ⟨f, contDiff_const.mul hφsmooth, hφcompact.mul_left, ?_, ?_, hfzero, ?_⟩
  · intro x
    exact mul_nonpos_of_nonpos_of_nonneg ha (hφrange x).1
  · intro x hx
    simp only [f, hφone x hx, mul_one, a]
    field_simp
  · intro x hx
    apply hfzero x (Or.inr ?_)
    intro hxann
    have hxlarge : 1 < dist x (0 : ℂ) := lt_of_not_ge hxann.2
    have hxsmall : dist x (0 : ℂ) ≤ 3 * δ := hx
    linarith [h.δ₀_mem.2]

/-- A smooth weight gives the third auxiliary event from the strict original
margin and the explicit transformed-metric and sphere-gap hypotheses. -/
theorem IsPinchPointProofConfiguration.exists_smooth_weight_for_pinchThirdEvent
    {U V W T Q' Q : Set ℂ} {δ ξ q : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hξ : 0 < ξ) (hq : 0 < q) (hq1 : q ≤ 1)
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hzero : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hstrict : ENNReal.ofReal q * internalDiam D δ (thickening (3 * δ) W \ V) <
      ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧
      (∀ x, f x ≤ 0) ∧ (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) ∧
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) ∧
      ∀ E : ℂ → ℂ → ℝ, IsEuclideanLengthMetric E →
        (∀ x y, 0 ≤ E x y) →
        (∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y) →
        ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) ≤
          ENNReal.ofReal (setDist E (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) →
        pinchThirdEvent E V W δ := by
  obtain ⟨f, hfsmooth, hfsupp, hfneg, hweight, hfzero, hfdisk⟩ :=
    h.exists_smooth_third_weyl_weight hξ hq hq1
  refine ⟨f, ⟨hfsmooth, hfsupp, subset_univ _⟩, hfneg, hfzero, hfdisk, ?_⟩
  intro E hE hEnonneg hscale hgap
  apply hD.pinchThirdEvent_of_weylScaling hE hEnonneg V W hzero hscale
    (B := Real.log q)
  · intro z hz
    exact (hweight z hz).le
  · exact hgap
  · simpa only [Real.exp_log hq] using hstrict

end HarmonicBalls
