import HarmonicBalls.FirstPass.S11i.PinchAffine
import HarmonicBalls.FirstPass.S11n

/-!
# Dilation of the pinch event (deterministic part of Step 13 of the proof of Lemma 11.13)

Source: `paper/lqg_harmonic_ball-corrected.tex`, Lemma `lem:mu_h-pinch-bad` (11.13), and the write-up
`notes/fp-gaps/CHATGPT-11-13-proof.md`, Step 13 (l.528-579): for `R > 0` the rescaled field
`h^(R)(w) = h(R w) - h_R(0)` has the coordinate identities
`mu_{h^(R)}(A) = c * mu_h(R A)` and `D_{h^(R)}(u,v) = b * D_h(R u, R v)` with positive constants `c, b`.
The pinch event of the rescaled pair at `(z, r)` is then the pinch event of the original pair at `(R z, R r)`.
This is the identity `E^{h^(R)}_{2^{-n}}(z; M) <-> E^h_{2^{-(n-k)}}(R z; M)` used with `R = 2^k`.

Proof: the affine chart identity `pinchPointEvent_chart_iff` (PinchAffine.lean) on both sides, the coincidence
of the two charts `(w / R - z) / r = (w - R z) / (R r)`, and the constant-factor invariance
`S11n.pinchPointEvent_smul_iff`. No external input.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Pinch event of the dilated pair: the measure `c • mu.map (· / R)` and the metric `b * D (R ·) (R ·)`
(the LQG pair of the rescaled field) at `(z, r)` is equivalent to the pinch event of `(mu, D)` at `(R z, R r)`. -/
theorem pinchPointEvent_dilate_iff (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M r : ℝ) (z : ℂ)
    {R a b : ℝ} (hR : 0 < R) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    pinchPointEvent (ENNReal.ofReal a • μ.map (fun w : ℂ => w / (R : ℂ)))
        (fun u v => b * D ((R : ℂ) * u) ((R : ℂ) * v)) U T Q' Q M r z ↔
      pinchPointEvent μ D U T Q' Q M (R * r) ((R : ℂ) * z) := by
  have hRr : 0 < R * r := mul_pos hR hr
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hmeas : (ENNReal.ofReal a • μ.map (fun w : ℂ => w / (R : ℂ))).map (pinchChart z hr.ne') =
      ENNReal.ofReal a • μ.map (pinchChart ((R : ℂ) * z) hRr.ne') := by
    have hf : Measurable (fun w : ℂ => w / (R : ℂ)) := (continuous_id.div_const _).measurable
    have hg : Measurable (pinchChart z hr.ne') := (pinchChart z hr.ne').measurable
    have hfun : (pinchChart z hr.ne') ∘ (fun w : ℂ => w / (R : ℂ)) = pinchChart ((R : ℂ) * z) hRr.ne' := by
      funext w
      simp only [Function.comp_apply, pinchChart_apply]
      push_cast
      field_simp
    rw [Measure.map_smul _ hg.aemeasurable, Measure.map_map hg hf, hfun]
  have hD : (fun x y : ℂ => b * D ((R : ℂ) * ((r : ℂ) * x + z)) ((R : ℂ) * ((r : ℂ) * y + z))) =
      (fun u v : ℂ => b * D (((R * r : ℝ) : ℂ) * u + (R : ℂ) * z) (((R * r : ℝ) : ℂ) * v + (R : ℂ) * z)) := by
    funext x y
    push_cast
    congr 2 <;> ring
  refine (pinchPointEvent_chart_iff _ _ U T Q' Q M r z hr).trans ?_
  rw [pinchPointEvent_chart_iff μ D U T Q' Q M (R * r) ((R : ℂ) * z) hRr, hmeas]
  rw [hD]
  exact S11n.pinchPointEvent_smul_iff ha hb _ _ U T Q' Q M 1 0

end HarmonicBalls
