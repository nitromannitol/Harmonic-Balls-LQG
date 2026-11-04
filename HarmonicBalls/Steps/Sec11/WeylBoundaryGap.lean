import HarmonicBalls.Steps.Sec11.WeylLocalEdges
import HarmonicBalls.Steps.Sec11.LocalPathLength
import HarmonicBalls.Steps.Sec11.PinchSmoothWeylBump

/-! # Boundary distances under inverse Weyl scaling

If an inverse Weyl representation is available, a weight vanishing on a
neighborhood of a domain gives a lower bound on the transformed distance to
its boundary. The inverse representation remains an explicit hypothesis. -/

namespace HarmonicBalls

open Set Metric MeasureTheory
open scoped ENNReal

/-- An inverse Weyl representation with zero weight on an open set bounds the
original internal metric by the transformed internal metric on that set. -/
theorem IsEuclideanLengthMetric.internalMetric_le_of_inverse_weylScaling
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) {ξ : ℝ} {f : ℂ → ℝ} {V : Set ℂ}
    (hV : IsOpen V) (hf : ∀ x ∈ V, f x = 0)
    (hzeroE : ∀ x y, weylScaling E ξ 0 x y = ENNReal.ofReal (E x y))
    (hreverse : ∀ x y, ENNReal.ofReal (D x y) =
      weylScaling E ξ (fun z => -f z) x y) (x y : ℂ) :
    internalMetric D V x y ≤ internalMetric E V x y := by
  have hnonnegD : ∀ x y, 0 ≤ D x y := by
    intro x y
    have ht := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at ht
    linarith
  have hnonnegE : ∀ x y, 0 ≤ E x y := by
    intro x y
    have ht := hE.triangle x y x
    rw [hE.self_eq_zero, hE.symm y x] at ht
    linarith
  have hlocal : ∀ x ∈ V, ∃ r : ℝ, 0 < r ∧ ∀ y z,
      E x y < r → E x z < r → D y z ≤ (1 : ℝ) * E y z := by
    intro x hx
    obtain ⟨R, hR, hball⟩ := (hE.isOpen_iff V).mp hV x hx
    have h := hE.weylScaling_local_edge_bound hnonnegE hzeroE hreverse (x := x) hR
      (B := 0) (fun z hz => by simp [hf z (hball z hz)])
    simpa using h
  have h := hE.internalMetric_le_const_mul_of_short_edges hD hnonnegD hV
    (show (0 : ℝ) < 1 by norm_num)
    (fun p hp => hE.path_short_edge_comparison_of_local 1 hlocal p hp) x y
  simpa using h

/-- Under inverse Weyl scaling, a zero-weight neighborhood preserves a lower
bound for the distance from an interior set to the boundary. -/
theorem ofReal_setDist_boundary_le_of_inverse_weylScaling
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) {ξ : ℝ} {f : ℂ → ℝ} {A U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hAU : A ⊆ U) (hUV : closure U ⊆ V)
    (hA : A.Nonempty) (hfront : (frontier U).Nonempty) (hf : ∀ x ∈ V, f x = 0)
    (hzeroE : ∀ x y, weylScaling E ξ 0 x y = ENNReal.ofReal (E x y))
    (hreverse : ∀ x y, ENNReal.ofReal (D x y) =
      weylScaling E ξ (fun z => -f z) x y) :
    ENNReal.ofReal (setDist D A (frontier U)) ≤
      ENNReal.ofReal (setDist E A (frontier U)) := by
  rw [ofReal_setDist_boundary_eq_internalMetric hD hU hAU hUV hA hfront,
    ofReal_setDist_boundary_eq_internalMetric hE hU hAU hUV hA hfront]
  apply iInf_mono
  intro x
  apply iInf_mono
  intro hx
  apply iInf_mono
  intro y
  apply iInf_mono
  intro hy
  exact hD.internalMetric_le_of_inverse_weylScaling hE hV hf hzeroE hreverse x y

/-- The third-event sphere gap cannot decrease when an inverse Weyl weight
vanishes on a ball containing the outer sphere. -/
theorem ofReal_setDist_pinch_spheres_le_of_inverse_weylScaling
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) {ξ δ R : ℝ} {f : ℂ → ℝ}
    (hδ : 0 < δ) (hR : 3 * δ < R) (hf : ∀ x ∈ ball 0 R, f x = 0)
    (hzeroE : ∀ x y, weylScaling E ξ 0 x y = ENNReal.ofReal (E x y))
    (hreverse : ∀ x y, ENNReal.ofReal (D x y) =
      weylScaling E ξ (fun z => -f z) x y) :
    ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) ≤
      ENNReal.ofReal (setDist E (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) := by
  have h3 : 0 < 3 * δ := by positivity
  have hfront : frontier (ball (0 : ℂ) (3 * δ)) = sphere 0 (3 * δ) :=
    frontier_ball 0 h3.ne'
  have hsub : sphere (0 : ℂ) (2 * δ) ⊆ ball 0 (3 * δ) := by
    intro x hx
    rw [mem_sphere] at hx
    rw [mem_ball]
    linarith
  have hclosure : closure (ball (0 : ℂ) (3 * δ)) ⊆ ball 0 R := by
    rw [closure_ball 0 h3.ne']
    intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball]
    linarith
  have hne : (sphere (0 : ℂ) (2 * δ)).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by positivity)
  have hnefront : (frontier (ball (0 : ℂ) (3 * δ))).Nonempty := by
    rw [hfront]
    exact NormedSpace.sphere_nonempty.mpr h3.le
  have h := ofReal_setDist_boundary_le_of_inverse_weylScaling hD hE isOpen_ball
    isOpen_ball hsub hclosure hne hnefront hf hzeroE hreverse
  simpa only [hfront] using h

/-- A single smooth weight yields the third event from a strict margin when
both the forward and inverse Weyl identities are available. -/
theorem IsPinchPointProofConfiguration.exists_smooth_weight_for_thirdEvent_of_inverse_weyl
    {U V W T Q' Q : Set ℂ} {δ ξ q : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hξ : 0 < ξ) (hq : 0 < q) (hq1 : q ≤ 1)
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hzeroD : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hstrict : ENNReal.ofReal q * internalDiam D δ (thickening (3 * δ) W \ V) <
      ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧ (∀ x, f x ≤ 0) ∧
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) ∧
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) ∧
      ∀ E : ℂ → ℂ → ℝ, IsEuclideanLengthMetric E →
        (∀ x y, 0 ≤ E x y) →
        (∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y) →
        (∀ x y, weylScaling E ξ 0 x y = ENNReal.ofReal (E x y)) →
        (∀ x y, ENNReal.ofReal (D x y) = weylScaling E ξ (fun z => -f z) x y) →
        pinchThirdEvent E V W δ := by
  obtain ⟨f, hfsmooth, hfcompact, hfneg, hweight, hfzero, hfdisk⟩ :=
    h.exists_smooth_third_weyl_weight hξ hq hq1
  have hfb : ∀ x ∈ ball (0 : ℂ) 1, f x = 0 := by
    intro x hx
    apply hfzero x (Or.inr ?_)
    intro hxann
    have hxsmall : dist x (0 : ℂ) < 1 := hx
    have hxlarge : 1 < dist x (0 : ℂ) := lt_of_not_ge hxann.2
    linarith
  refine ⟨f, ⟨hfsmooth, hfcompact, subset_univ _⟩, hfneg, hfzero, hfdisk, ?_⟩
  intro E hE hEnonneg hscale hzeroE hreverse
  have hgap := ofReal_setDist_pinch_spheres_le_of_inverse_weylScaling hD hE
    h.δ₀_mem.1 (show 3 * δ < 1 by linarith [h.δ₀_mem.2]) hfb hzeroE hreverse
  apply hD.pinchThirdEvent_of_weylScaling hE hEnonneg V W hzeroD hscale
    (B := Real.log q)
  · intro z hz
    exact (hweight z hz).le
  · exact hgap
  · simpa only [Real.exp_log hq] using hstrict

end HarmonicBalls
