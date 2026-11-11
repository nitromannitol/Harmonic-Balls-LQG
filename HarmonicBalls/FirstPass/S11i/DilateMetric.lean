import HarmonicBalls.FirstPass.S11q.Metric

/-!
# Metric half of the rescaling hypothesis `hscale` (Lemma 11.13, write-up sec. 6, paper eq. (34)-(37))

For a whole-plane GFF model `hC` with LQG metric `D` (`IsLQGMetricOfField`) and the dilated background
`hC(R ·) + Q_γ log R - c` (paper eq. (34)), the real metric of the dilated field is
`e^{-ξ(c - α₀ log R)} · D(R ·, R ·)` almost surely (paper eq. (37)). This is
`ae_weylScaling_affinePullback_background` (FirstPass/S11q/Metric.lean) read back in real-valued form.
The measure half is `FirstPass/S11i/DilateMeasure.lean`; both halves use the same constant `c_R = c - α₀ log R`
(`c_R = dilationConstant`, FirstPass/S11q.lean, when `c = H R 0 + (Q_γ + α₀) log R`).
Not used: measurability of `c` is an explicit hypothesis here (its derivation from the circle averages is pending).
-/

namespace HarmonicBalls.DilateMetric

open MeasureTheory Filter
open scoped ENNReal

/-- Real-valued dilated metric (paper eq. (37)). Given the LQG metric `D` of `hC` through a functional `𝔇` with
`IsLQGMetric γ ξ 𝔇`, almost surely for all `u v`, the real value of the Weyl scaling of the dilated background
`hC(R ·) + Q_γ log R - c` equals `e^{-ξ(c - α₀ log R)} · D(R u, R v)`. -/
theorem ae_toReal_weylScaling_affinePullback_background
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (D : Ω → ℂ → ℂ → ℝ)
    (hD : ∀ᵐ ω ∂P, ∀ u v : ℂ, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v)
    {R : ℝ} (hR : 0 < R) (c : Ω → ℝ) (hc : Measurable c) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      (weylScaling (𝔇 (addFunPairing (affinePullbackPairing (hC ω) R 0) (fun _ => lqgQ γ * Real.log R - c ω)))
          ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal =
        Real.exp (-(ξ * (c ω - α₀ * Real.log R))) * D ω (R * u) (R * v) := by
  filter_upwards [ae_weylScaling_affinePullback_background hG 𝔇 h𝔇 hR c hc α₀, hD] with ω hω hDω
  intro u v
  obtain ⟨hD0, _⟩ := hDω (R * u) (R * v)
  rw [hω u v, ← (hDω (R * u) (R * v)).2, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_ofReal hD0]

/-- Existential form for a model with LQG metric `D` (`IsLQGMetricOfField`): the dilated background metric is a
positive multiple of `D(R ·, R ·)` almost surely, with the multiple `e^{-ξ(c - α₀ log R)}` for the measurable
random constant `c`. The witnessing functional `𝔇` is the one of `IsLQGMetricOfField`. -/
theorem exists_ae_toReal_weylScaling_affinePullback_background
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {D : Ω → ℂ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) (hM : IsLQGMetricOfField P γ ξ α₀ hC D)
    {R : ℝ} (hR : 0 < R) (c : Ω → ℝ) (hc : Measurable c) :
    ∃ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 ∧
      ∀ᵐ ω ∂P, ∀ u v : ℂ,
        (weylScaling (𝔇 (addFunPairing (affinePullbackPairing (hC ω) R 0) (fun _ => lqgQ γ * Real.log R - c ω)))
            ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal =
          Real.exp (-(ξ * (c ω - α₀ * Real.log R))) * D ω (R * u) (R * v) := by
  obtain ⟨𝔇, h𝔇, hD⟩ := hM
  exact ⟨𝔇, h𝔇, ae_toReal_weylScaling_affinePullback_background hG 𝔇 h𝔇 D hD hR c hc⟩

end HarmonicBalls.DilateMetric
