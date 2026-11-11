import HarmonicBalls.FirstPass.S11i.DilatePinch

/-!
# The hypothesis `hcert` of `pinch_window_ae_of_cert`, reduced to the original model

`CertWindow.pinch_window_ae_of_cert` (`FirstPass/S11i/CertWindow.lean:58`) takes the implication
`hcert` for the rescaled model `(μk k, Dk k) = (c • μ.map (· / 2^k), b * D(2^k ·, 2^k ·))` (shape of `hscale`).
This file proves, with no new input, that `hcert` follows from the same implication for the ORIGINAL model
`(μ ω, D ω)`, at the dilated radius `2^k 2^{-n}` and at the point `z = 2^k w`: this is `DilatePinch.pinchPointEvent_dilate_iff`
transported along `μ`-a.e. (the measure `ofReal a • μ.map f` has the same null sets as `μ.map f`, and
`Measure.ae_map_le` moves a predicate from `μ` to `μ.map f`; no measurability of the predicate is needed).

The residual input `horig` is the statement that the certificate index of the rescaled model at the point `z / 2^k`
forces the actual pinch event at `z` (radius `2^k 2^{-n}`), for `μ`-almost every `z`. It is NOT proved here.
-/

namespace HarmonicBalls.S11w

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- `hcert` of `CertWindow.pinch_window_ae_of_cert` from the original-model implication `horig`. -/
theorem hcert_of_original_pinch {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M : ℝ)
    (Cert : ℕ → Ω → ℕ → ℂ → Prop)
    (μk : ℕ → Ω → Measure ℂ) (Dk : ℕ → Ω → ℂ → ℂ → ℝ)
    (hscale : ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      μk k ω = ENNReal.ofReal a • (μ ω).map (fun x : ℂ => x / ((((2 : ℝ) ^ k : ℝ)) : ℂ)) ∧
      ∀ u v : ℂ, Dk k ω u v = b * D ω ((((2 : ℝ) ^ k : ℝ) : ℂ) * u) ((((2 : ℝ) ^ k : ℝ) : ℂ) * v))
    (horig : ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ n : ℕ,
      Cert k ω n (z / ((((2 : ℝ) ^ k : ℝ)) : ℂ)) →
        HarmonicBalls.pinchPointEvent (μ ω) (D ω) U T Q' Q M ((((2 : ℝ) ^ k : ℝ)) * (2 : ℝ)⁻¹ ^ n) z) :
    ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ w ∂(μk k ω), ∀ n : ℕ, Cert k ω n w →
      HarmonicBalls.pinchPointEvent (μk k ω) (Dk k ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) w := by
  intro k
  filter_upwards [hscale k, horig k] with ω hsc hor
  obtain ⟨a, b, ha, hb, hμk, hD⟩ := hsc
  set R : ℝ := (2 : ℝ) ^ k with hRdef
  have hR0 : (0 : ℝ) < R := by positivity
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR0.ne'
  have hDfun : Dk k ω = fun u v => b * D ω ((R : ℂ) * u) ((R : ℂ) * v) :=
    funext fun u => funext fun v => hD u v
  have hRz : ∀ z : ℂ, (R : ℂ) * (z / (R : ℂ)) = z := fun z => by field_simp
  rw [hμk, hDfun]
  -- dilation of the pinch event, for each index `n` and each point `w`
  have hiff : ∀ (w : ℂ) (n : ℕ),
      HarmonicBalls.pinchPointEvent (ENNReal.ofReal a • (μ ω).map (fun x : ℂ => x / (R : ℂ)))
        (fun u v => b * D ω ((R : ℂ) * u) ((R : ℂ) * v)) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) w ↔
      HarmonicBalls.pinchPointEvent (μ ω) (D ω) U T Q' Q M (R * (2 : ℝ)⁻¹ ^ n) ((R : ℂ) * w) :=
    fun w n => HarmonicBalls.pinchPointEvent_dilate_iff (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) w hR0 ha hb
      (by positivity)
  -- transport the almost-everywhere statement from `μ ω` to `μ.map f`, `f z = z / R`, along the inverse `y ↦ R y`
  have hf : Measurable (fun x : ℂ => x / (R : ℂ)) := measurable_id.div_const _
  have hg : Measurable (fun y : ℂ => (R : ℂ) * y) := measurable_id.const_mul _
  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving (fun y : ℂ => (R : ℂ) * y)
      ((μ ω).map (fun x : ℂ => x / (R : ℂ))) (μ ω) := by
    refine ⟨hg, ?_⟩
    rw [Measure.map_map hg hf]
    have hid : (fun y : ℂ => (R : ℂ) * y) ∘ (fun x : ℂ => x / (R : ℂ)) = id := by
      funext x
      show (R : ℂ) * (x / (R : ℂ)) = x
      field_simp
    rw [hid, Measure.map_id]
  have hae : ∀ᵐ y ∂((μ ω).map (fun x : ℂ => x / (R : ℂ))), ∀ n : ℕ, Cert k ω n y →
      HarmonicBalls.pinchPointEvent (μ ω) (D ω) U T Q' Q M (R * (2 : ℝ)⁻¹ ^ n) ((R : ℂ) * y) :=
    (hqmp.ae hor).mono fun y hy n hn => hy n (by rwa [mul_div_cancel_left₀ y hRc])
  exact Measure.ae_smul_measure (hae.mono fun y hy n hn => (hiff y n).2 (hy n hn)) _

end HarmonicBalls.S11w
