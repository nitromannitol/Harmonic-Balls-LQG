import HarmonicBalls.Steps.Sec11.PinchProofGeometry
import HarmonicBalls.Steps.Sec11.WeylLocalEdges
import Mathlib.Topology.UrysohnsLemma

/-! # A compactly supported Weyl bump for the third pinch event

The ten-scale geometric buffers provide room for a continuous bump equal to
one on the whole internal-metric neighborhood, and zero near the inner
auxiliary set and outside the annulus. -/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- The configuration admits a compactly supported bump which is one on the
neighborhood used by the third internal diameter, and vanishes on `closure U`
and outside the annulus from radius one to radius two. -/
theorem IsPinchPointProofConfiguration.exists_third_weyl_bump
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) :
    ∃ f : C(ℂ, ℝ), HasCompactSupport f ∧
      (∀ x ∈ thickening δ (thickening (3 * δ) W \ V), f x = 1) ∧
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) ∧
      ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  let A := thickening (3 * δ) W \ V
  let K := closure (thickening δ A)
  have hδ : 0 < δ := h.δ₀_mem.1
  have hKsub : K ⊆ thickening (2 * δ) A := by
    exact (closure_thickening_subset_cthickening δ A).trans
      (cthickening_subset_thickening' (by linarith) (by linarith) A)
  have hKann : K ⊆ annulus 0 1 2 := by
    apply hKsub.trans
    apply (thickening_subset_of_subset (2 * δ) sdiff_subset).trans
    apply (thickening_thickening_subset (2 * δ) (3 * δ) W).trans
    exact (thickening_mono (by linarith : 2 * δ + 3 * δ ≤ 10 * δ) W).trans
      (subset_closure.trans h.thickening_W)
  have hKcompact : IsCompact K := by
    apply isCompact_of_isClosed_isBounded isClosed_closure
    exact isBounded_ball.subset (hKann.trans (fun _ hx => hx.1))
  have hdisj : Disjoint K (closure U ∪ (annulus 0 1 2)ᶜ) := by
    apply disjoint_left.mpr
    intro x hx hy
    rcases hy with hxU | hxann
    · have hxU' : x ∈ thickening δ U := closure_subset_thickening hδ U hxU
      obtain ⟨y, hyA, hxy⟩ := mem_thickening_iff.mp (hKsub hx)
      obtain ⟨z, hzU, hxz⟩ := mem_thickening_iff.mp hxU'
      have hyU : y ∈ thickening (10 * δ) U := by
        apply mem_thickening_iff.mpr
        refine ⟨z, hzU, ?_⟩
        have htri := dist_triangle y x z
        rw [dist_comm y x] at htri
        linarith
      exact hyA.2 (h.thickening_U (subset_closure hyU))
    · exact hxann (hKann hx)
  obtain ⟨f, hfK, hfzero, hfcompact, hfrange⟩ :=
    exists_continuous_one_zero_of_isCompact hKcompact
      (isClosed_closure.union (isOpen_ball.sdiff isClosed_closedBall).isClosed_compl) hdisj
  refine ⟨f, hfcompact, ?_, ?_, hfrange⟩
  · intro x hx
    exact hfK (subset_closure hx)
  · exact hfzero

/-- A prescribed contraction factor is realized by a nonpositive compactly
supported continuous Weyl weight. The weight vanishes on the inner auxiliary
set and on the central closed disk. -/
theorem IsPinchPointProofConfiguration.exists_third_weyl_weight
    {U V W T Q' Q : Set ℂ} {δ ξ q : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hξ : 0 < ξ) (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ f : ℂ → ℝ, Continuous f ∧ HasCompactSupport f ∧
      (∀ x, f x ≤ 0) ∧
      (∀ x ∈ thickening δ (thickening (3 * δ) W \ V), ξ * f x = Real.log q) ∧
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) ∧
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) := by
  obtain ⟨φ, hφcompact, hφone, hφzero, hφrange⟩ := h.exists_third_weyl_bump
  let a : ℝ := Real.log q / ξ
  let f : ℂ → ℝ := fun x => a * φ x
  have ha : a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hq.le hq1) hξ.le
  have hfzero : ∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0 := by
    intro x hx
    simp [f, hφzero x hx]
  refine ⟨f, continuous_const.mul φ.continuous, hφcompact.mul_left, ?_, ?_, hfzero, ?_⟩
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

/-- With a strict original margin, the geometric weight produces the third
event whenever the transformed metric and sphere-gap comparison are available. -/
theorem IsPinchPointProofConfiguration.exists_weight_for_pinchThirdEvent
    {U V W T Q' Q : Set ℂ} {δ ξ q : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hξ : 0 < ξ) (hq : 0 < q) (hq1 : q ≤ 1)
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hzero : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hstrict : ENNReal.ofReal q * internalDiam D δ (thickening (3 * δ) W \ V) <
      ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))) :
    ∃ f : ℂ → ℝ, Continuous f ∧ HasCompactSupport f ∧
      (∀ x, f x ≤ 0) ∧ (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) ∧
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) ∧
      ∀ E : ℂ → ℂ → ℝ, IsEuclideanLengthMetric E →
        (∀ x y, 0 ≤ E x y) →
        (∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y) →
        ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) ≤
          ENNReal.ofReal (setDist E (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) →
        pinchThirdEvent E V W δ := by
  obtain ⟨f, hfcont, hfsupp, hfneg, hweight, hfzero, hfdisk⟩ :=
    h.exists_third_weyl_weight hξ hq hq1
  refine ⟨f, hfcont, hfsupp, hfneg, hfzero, hfdisk, ?_⟩
  intro E hE hEnonneg hscale hgap
  apply hD.pinchThirdEvent_of_weylScaling hE hEnonneg V W hzero hscale
    (B := Real.log q)
  · intro z hz
    exact (hweight z hz).le
  · exact hgap
  · simpa only [Real.exp_log hq] using hstrict

end HarmonicBalls
