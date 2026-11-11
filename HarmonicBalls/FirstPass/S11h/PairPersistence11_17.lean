import HarmonicBalls.FirstPass.S11h.O2Bump
import HarmonicBalls.FirstPass.S11j.Corridor
import HarmonicBalls.Steps.Sec11.PinchFirstWeylPreservation
import HarmonicBalls.Steps.Sec11.PinchMeasureWeylShift
import HarmonicBalls.Steps.Sec11.WeylLocalEdges
import HarmonicBalls.Steps.Sec11.WeylBoundaryGap
import HarmonicBalls.Steps.Sec11.WeylInverse

/-!
# Lemma 11.17, Step 17.5: the three pinch events persist under the bump lowering

Deterministic part of Step 17.4-17.5, for a fixed bump
`φ` (paper eq:bump, corrected `[C42]`/`[C44]` geometry). With `k ∈ (0, 1]` and `f = ξ⁻¹ log k · φ` (so `e^{ξ f} = k^φ`
and `f ≤ 0`), the shifted metric `E = e^{ξ f} · D` (weylScaling, Fact 2.2 III) satisfies `Ẽ₁`, `Ẽ₂` (with the measure
`μ` reweighted by `e^{γ f}`, the Cameron-Martin density of `weylShiftPair`) and `Ẽ₃`, provided the original metric
satisfies `Ẽ₁`, `Ẽ₂` and the strict inequality `k · diam^δ(B_{3δ}(W) \ V) < D(∂B_{2δ}, ∂B_{3δ})`.
The Cameron-Martin transfer of this statement is a separate (frozen) step.

Reused (checked: no unproved placeholders, axioms only propext, Classical.choice, Quot.sound): `IsPinchPointProofConfiguration.pinchFirstEvent_of_weylScaling` (Steps/Sec11/PinchFirstWeylPreservation),
`IsPinchPointProofConfiguration.pinchSecondEvent_of_weighted_weylScaling` (Steps/Sec11/PinchMeasureWeylShift),
`IsEuclideanLengthMetric.pinchThirdEvent_of_weylScaling` (Steps/Sec11/WeylLocalEdges),
`ofReal_setDist_pinch_spheres_le_of_inverse_weylScaling` (Steps/Sec11/WeylBoundaryGap),
`IsEuclideanLengthMetric.inverse_weylScaling` (Steps/Sec11/WeylInverse), `IsEuclideanLengthMetric.weylScaling_zero`,
and the configuration bridge `IsBufferedPinchGeometry.toIsCorrectedPinchConfiguration` (FirstPass/S11j/Corridor).

Open hypotheses (both are almost-sure properties of the LQG metric, to be discharged in the probabilistic step):
`IsEuclideanLengthMetric` of the Weyl-scaled metric (`hE`) and finiteness of the Weyl scaling (`hfin`).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric

/-- The exponent `f = ξ⁻¹ log k · φ` of the bump shift (paper step 17.4, eq. (6.8) with `k = min{1, c₁/(2c₂)}`). -/
noncomputable def bumpExponent (ξ k : ℝ) (φ : ℂ → ℝ) : ℂ → ℝ :=
  fun z => ξ⁻¹ * Real.log k * φ z

/-- The Weyl-scaled metric `E = e^{ξ f} · D`, as the real-valued metric of the pair in `weylShiftPair`. -/
noncomputable def bumpShiftedMetric (D : ℂ → ℂ → ℝ) (ξ : ℝ) (f : ℂ → ℝ) : ℂ → ℂ → ℝ :=
  fun x y => (weylScaling D ξ f x y).toReal

/-- The three pinch events persist under the bump lowering (paper step 17.5, corrected geometry). -/
theorem pinchEvents_of_bumpShift {U V W T Q' Q : Set ℂ} {δ γ ξ k M : ℝ} {μ : Measure ℂ} {D : ℂ → ℂ → ℝ}
    {φ : ℂ → ℝ} (h : IsBufferedPinchGeometry U V W T Q' Q δ) (hφc : Continuous φ)
    (hφsupp : ∀ z, z ∉ thickening (5 * δ) W → φ z = 0)
    (hφO2 : ∀ z ∈ closure (pinchO2 δ V W), φ z = 1) (hφU : ∀ z ∈ closure U, φ z = 0)
    (hφ01 : ∀ z, 0 ≤ φ z ∧ φ z ≤ 1) (hξ : 0 < ξ) (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hD : IsEuclideanLengthMetric D)
    (hfin : ∀ x y, weylScaling D ξ (bumpExponent ξ k φ) x y ≠ ⊤)
    (hE : IsEuclideanLengthMetric (bumpShiftedMetric D ξ (bumpExponent ξ k φ)))
    (hE1 : pinchFirstEvent D W T Q' Q δ) (hE2 : pinchSecondEvent μ D U V δ M)
    (hstrict : ENNReal.ofReal k * internalDiam D δ (thickening (3 * δ) W \ V) <
      ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))) :
    pinchFirstEvent (bumpShiftedMetric D ξ (bumpExponent ξ k φ)) W T Q' Q δ ∧
    pinchSecondEvent (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (γ * bumpExponent ξ k φ x))))
      (bumpShiftedMetric D ξ (bumpExponent ξ k φ)) U V δ M ∧
    pinchThirdEvent (bumpShiftedMetric D ξ (bumpExponent ξ k φ)) V W δ := by
  have hδ0 : 0 < δ := h.delta_pos
  have hδ1 : δ < 1 / 1000 := h.delta_lt
  -- the bump vanishes off the annulus `1 < |z| < 2` (buffer_W)
  have hsupp : ∀ z, z ∉ annulus 0 1 2 → φ z = 0 := by
    intro z hz
    apply hφsupp z
    intro hzW
    apply hz
    have hsub : thickening (5 * δ) W ⊆ closure (thickening (10 * δ) (closure W)) := by
      intro y hy
      apply subset_closure
      obtain ⟨x, hx, hxy⟩ := mem_thickening_iff.1 hy
      exact mem_thickening_iff.2 ⟨x, subset_closure hx, by linarith⟩
    exact (h.buffer_W (hsub hzW)).2
  have hfz : ∀ z, z ∉ annulus 0 1 2 → bumpExponent ξ k φ z = 0 := fun z hz => by
    show ξ⁻¹ * Real.log k * φ z = 0
    rw [hsupp z hz, mul_zero]
  have hfneg : ∀ x ∈ ball (0 : ℂ) 1, bumpExponent ξ k φ x = 0 := fun x hx =>
    hfz x fun hA => hA.2 (ball_subset_closedBall hx)
  have hfouter : ∀ x ∈ (closedBall (0 : ℂ) 3)ᶜ, bumpExponent ξ k φ x = 0 := fun x hx =>
    hfz x fun hA => hx (ball_subset_closedBall (ball_subset_ball (by norm_num) hA.1))
  -- sign and range of the exponent
  have hc : ξ⁻¹ * Real.log k ≤ 0 :=
    mul_nonpos_iff.2 (Or.inl ⟨inv_nonneg.2 hξ.le, Real.log_nonpos hk0.le hk1⟩)
  have hf_nonpos : ∀ z, bumpExponent ξ k φ z ≤ 0 := fun z =>
    mul_nonpos_iff.2 (Or.inr ⟨hc, (hφ01 z).1⟩)
  have hf_lower : ∀ z, ξ⁻¹ * Real.log k ≤ bumpExponent ξ k φ z := fun z => by
    have := mul_le_mul_of_nonpos_left (hφ01 z).2 hc
    simp only [mul_one] at this
    exact this
  have hfc : Continuous (bumpExponent ξ k φ) := by
    unfold bumpExponent
    exact continuous_const.mul hφc
  have hfU : ∀ x ∈ closure U ∪ (annulus 0 1 2)ᶜ, bumpExponent ξ k φ x = 0 := by
    intro x hx
    rcases hx with hx | hx
    · show ξ⁻¹ * Real.log k * φ x = 0
      rw [hφU x hx, mul_zero]
    · exact hfz x hx
  -- the configuration of the Steps lemmas
  have hcfg := h.toIsCorrectedPinchConfiguration.toIsPinchPointProofConfiguration
  have hzeroD : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y) := fun x y => hD.weylScaling_zero ξ x y
  have hzeroE : ∀ x y, weylScaling (bumpShiftedMetric D ξ (bumpExponent ξ k φ)) ξ 0 x y =
      ENNReal.ofReal (bumpShiftedMetric D ξ (bumpExponent ξ k φ) x y) := fun x y =>
    hE.weylScaling_zero ξ x y
  have hforward : ∀ x y, ENNReal.ofReal (bumpShiftedMetric D ξ (bumpExponent ξ k φ) x y) =
      weylScaling D ξ (bumpExponent ξ k φ) x y := fun x y => ENNReal.ofReal_toReal (hfin x y)
  have hreverse : ∀ x y, ENNReal.ofReal (D x y) =
      weylScaling (bumpShiftedMetric D ξ (bumpExponent ξ k φ)) ξ (fun z => -bumpExponent ξ k φ z) x y :=
    fun x y => IsEuclideanLengthMetric.inverse_weylScaling hD hξ.le _ hfc hf_lower hf_nonpos hE x y
  -- the first event
  have hE1' : pinchFirstEvent (bumpShiftedMetric D ξ (bumpExponent ξ k φ)) W T Q' Q δ :=
    hcfg.pinchFirstEvent_of_weylScaling hD hE hξ.le hf_nonpos hfneg hfouter hzeroD hforward hzeroE hreverse hE1
  -- the second event: the density `e^{γ f}` is one on `U` and off the annulus
  have hE2' := hcfg.pinchSecondEvent_of_weighted_weylScaling (γ := γ) hD hE hξ.le hf_nonpos hfU hzeroD hforward
    hzeroE hreverse hE2
  -- the third event: the weight is `log k` on the δ-neighbourhood of `B_{3δ}(W) \ V`, and the spheres are unchanged
  have hweight : ∀ z ∈ thickening δ (thickening (3 * δ) W \ V), ξ * bumpExponent ξ k φ z ≤ Real.log k := by
    intro z hz
    have hsub1 : thickening δ (thickening (3 * δ) W \ V) ⊆ pinchO2 δ V W := by
      unfold pinchO2
      intro y hy
      obtain ⟨x, hx, hxy⟩ := mem_thickening_iff.1 hy
      exact mem_thickening_iff.2 ⟨x, subset_closure hx, hxy⟩
    have hz' : z ∈ closure (pinchO2 δ V W) := subset_closure (hsub1 hz)
    have h1 : φ z = 1 := hφO2 z hz'
    have key : ξ * (ξ⁻¹ * Real.log k * 1) = Real.log k := by
      rw [mul_one, ← mul_assoc, mul_inv_cancel₀ hξ.ne', one_mul]
    show ξ * (ξ⁻¹ * Real.log k * φ z) ≤ Real.log k
    rw [h1]
    exact key.le
  have hgap := ofReal_setDist_pinch_spheres_le_of_inverse_weylScaling hD hE hδ0 (R := 1) (by linarith)
    (f := bumpExponent ξ k φ) (fun x hx => hfneg x hx) hzeroE hreverse
  have hstrict' : ENNReal.ofReal (Real.exp (Real.log k)) * internalDiam D δ (thickening (3 * δ) W \ V) <
      ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) := by
    rw [Real.exp_log hk0]
    exact hstrict
  have hE3 := IsEuclideanLengthMetric.pinchThirdEvent_of_weylScaling hD hE
    (fun x y => ENNReal.toReal_nonneg) V W hzeroD hforward hweight hgap hstrict'
  exact ⟨hE1', hE2', hE3⟩

end HarmonicBalls

#print axioms HarmonicBalls.pinchEvents_of_bumpShift
