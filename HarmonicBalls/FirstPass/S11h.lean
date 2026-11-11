import HarmonicBalls.Proofs.Sec11.WholePlanePinchThirdEvent
import HarmonicBalls.FirstPass.S11h.WeylShiftUniv
import HarmonicBalls.Steps.Sec11.PinchFirstWeylPreservation
import HarmonicBalls.Steps.Sec11.PinchMeasureWeylShift

/-!
# Section 11 third pinch event

Step 1 of Lemma 11.17 (`lemma:third-event-proof`, paper lines 3726-3756): the smooth Weyl shift that produces the third
pinch event, for a probability space in any universe.

`exists_positive_measure_wholePlane_shift_thirdEvent_univ` is the copy of the committed Type-level theorem
`IsPinchPointProofConfiguration.exists_positive_measure_wholePlane_shift_thirdEvent`
(`Proofs/Sec11/WholePlanePinchThirdEvent.lean:18`), with `Ω : Type u` and the metric axioms taken from the FROZEN `LQGMetricSatisfiesAxiomsUnivFrozen`. The proof is unchanged otherwise.

It does not transfer any set to the shifted field: the events `Ẽ₁`, `Ẽ₂` of the shifted field and the Cameron-Martin
transfer back to the unshifted field are NOT part of this statement (open).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter
open scoped ENNReal

universe u

/-- A deterministic smooth shift produces the third auxiliary pinch event on part of any positive-measure event, for a
whole-plane GFF metric on a probability space in any universe. -/
theorem IsPinchPointProofConfiguration.exists_positive_measure_wholePlane_shift_thirdEvent_univ
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (hU : LQGMetricSatisfiesAxiomsUnivFrozen.{u})
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (hA : 0 < P A) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧ (∀ x, f x ≤ 0) ∧
      (∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0) ∧
      (∀ x ∈ closedBall 0 (3 * δ), f x = 0) ∧
      0 < P {ω | ω ∈ A ∧ pinchThirdEvent (𝔇 (addFunPairing (hC ω) f)) V W δ} := by
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
    filter_upwards [ae_wholePlane_weylScaling_shift_univ hU P γ ξ hC hcirc 𝔇 h𝔇 hgff
      (fun _ _ => 0) (by intro ω; fun_prop) (by intro x; fun_prop)] with ω hω
    exact hω.1
  obtain ⟨q, hq, hq1, hp⟩ :=
    h.exists_positive_measure_third_contraction P A (fun ω => 𝔇 (hC ω)) hA hmetric
  obtain ⟨f, hfsmooth, hfcompact, hfneg, hweight, hfzero, hfdisk⟩ :=
    h.exists_smooth_third_weyl_weight hξ hq hq1
  have hfb : ∀ x ∈ ball (0 : ℂ) 1, f x = 0 := by
    intro x hx
    apply hfzero x (Or.inr ?_)
    intro hxann
    have hxsmall : dist x (0 : ℂ) < 1 := hx
    have hxlarge : 1 < dist x (0 : ℂ) := lt_of_not_ge hxann.2
    linarith
  let B : Set Ω := {ω | ω ∈ A ∧
    ENNReal.ofReal q * internalDiam (𝔇 (hC ω)) δ (thickening (3 * δ) W \ V) <
      ENNReal.ofReal (setDist (𝔇 (hC ω)) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))}
  let G : Set Ω := {ω | IsEuclideanLengthMetric (𝔇 (hC ω)) ∧
    IsEuclideanLengthMetric (𝔇 (addFunPairing (hC ω) f)) ∧
    (∀ x y, weylScaling (𝔇 (hC ω)) ξ 0 x y = ENNReal.ofReal (𝔇 (hC ω) x y)) ∧
    (∀ x y, ENNReal.ofReal (𝔇 (addFunPairing (hC ω) f) x y) =
      weylScaling (𝔇 (hC ω)) ξ f x y) ∧
    (∀ x y, weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ 0 x y =
      ENNReal.ofReal (𝔇 (addFunPairing (hC ω) f) x y)) ∧
    (∀ x y, ENNReal.ofReal (𝔇 (hC ω) x y) =
      weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -f z) x y)}
  have hG : ∀ᵐ ω ∂P, ω ∈ G := by
    exact ae_wholePlane_weylScaling_shift_univ hU P γ ξ hC hcirc 𝔇 h𝔇 hgff
      (fun _ => f) (by intro ω; exact hfsmooth.continuous) (by intro x; fun_prop)
  have heq : B =ᵐ[P] B ∩ G := by
    filter_upwards [hG] with ω hω
    simp only [mem_inter_iff, hω, and_true]
  have hp' : 0 < P (B ∩ G) := by rw [← measure_congr heq]; exact hp
  refine ⟨f, ⟨hfsmooth, hfcompact, subset_univ _⟩, hfneg, hfzero, hfdisk,
    hp'.trans_le (measure_mono ?_)⟩
  intro ω hω
  obtain ⟨hd, he, hz, hscale, hzeroE, hinverse⟩ := hω.2
  have henonneg : ∀ x y, 0 ≤ 𝔇 (addFunPairing (hC ω) f) x y := by
    intro x y
    have ht := he.triangle x y x
    rw [he.self_eq_zero, he.symm y x] at ht
    linarith
  have hgap := ofReal_setDist_pinch_spheres_le_of_inverse_weylScaling hd he
    h.δ₀_mem.1 (show 3 * δ < 1 by linarith [h.δ₀_mem.2]) hfb hzeroE hinverse
  refine ⟨hω.1.1, ?_⟩
  apply hd.pinchThirdEvent_of_weylScaling he henonneg V W hz hscale (B := Real.log q)
  · intro z hz'
    exact (hweight z hz').le
  · exact hgap
  · simpa only [Real.exp_log hq] using hω.1.2

/-- Deterministic persistence of the first and second pinch events under a nonpositive Weyl shift `f` (paper lines
3733-3756, "the upper quantities decrease, the masses are unchanged"; the lower quantities are first-exit crossing
distances, unchanged because `f` vanishes on `B_3`, on `U` and on `𝔸_{3,6}`). The first event of `D` gives the first event
of the shifted metric `E`, and the second event of `(μ, D)` gives the second event of `(μ.withDensity e^{γf}, E)`.
Both are the committed Steps lemmas `pinchFirstEvent_of_weylScaling` and `pinchSecondEvent_of_weighted_weylScaling`;
this is the only glue. -/
theorem IsPinchPointProofConfiguration.pinchFirst_and_second_of_shift
    {U V W T Q' Q : Set ℂ} {δ ξ γ M : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hξ : 0 ≤ ξ) {f : ℂ → ℝ}
    (hfneg : ∀ x, f x ≤ 0)
    (hf : ∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, f x = 0)
    (hzeroD : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hforward : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hzeroE : ∀ x y, weylScaling E ξ 0 x y = ENNReal.ofReal (E x y))
    (hreverse : ∀ x y, ENNReal.ofReal (D x y) = weylScaling E ξ (fun z => -f z) x y)
    {μ : Measure ℂ}
    (hE1 : pinchFirstEvent D W T Q' Q δ) (hE2 : pinchSecondEvent μ D U V δ M) :
    pinchFirstEvent E W T Q' Q δ ∧
      pinchSecondEvent (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x)))) E U V δ M := by
  have hfinner : ∀ x ∈ ball (0 : ℂ) 1, f x = 0 := by
    intro x hx
    apply hf x (Or.inr ?_)
    intro hxann
    have hxsmall : dist x (0 : ℂ) < 1 := hx
    have hxlarge : 1 < dist x (0 : ℂ) := lt_of_not_ge hxann.2
    linarith
  have hfouter : ∀ x ∈ (closedBall (0 : ℂ) 3)ᶜ, f x = 0 := by
    intro x hx
    apply hf x (Or.inr ?_)
    intro hxann
    have h23 : closedBall (0 : ℂ) 2 ⊆ closedBall (0 : ℂ) 3 := closedBall_subset_closedBall (by norm_num)
    exact hx (h23 (ball_subset_closedBall hxann.1))
  exact ⟨h.pinchFirstEvent_of_weylScaling hD hE hξ hfneg hfinner hfouter hzeroD hforward hzeroE hreverse hE1,
    h.pinchSecondEvent_of_weighted_weylScaling hD hE hξ hfneg hf hzeroD hforward hzeroE hreverse hE2⟩

end HarmonicBalls
