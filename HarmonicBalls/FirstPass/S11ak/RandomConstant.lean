import HarmonicBalls.FirstPass.S11aa
import HarmonicBalls.FirstPass.S11q.Metric

/-! # Universe lift of the random-constant affine Weyl identity (fp-S11ak, owner z6)

The Type-`0` identity `HarmonicBalls.ae_weylScaling_affinePullback_background` (`FirstPass/S11q/Metric.lean`; the random
constant shift `ae_metric_background_add_random_constant` of `Steps/Sec11/ContinuousFieldShift.lean` is its ingredient)
quantifies over `Ω : Type`. This file lifts it to `Ω : Type u` for the random constant `c ω = hcirc ω R 0 + q`, which is a
coordinate of the circle process (Gwynne-Miller arXiv:1905.00383, Fact 2.2 III and IV; paper l.434-453).

The lift is the transport of `FirstPass/S11aa.lean` (blocker U, option (b)): push `P` forward along `sample` to the Type-0
space `CircleSample`, where `s.1.1` is the pairing and `s.1.2` the circle process; apply the Type-0 identity there with the
random constant `s ↦ s.1.2 R 0 + q` (measurable by `measurable_circleCoord`); pull back along `sample`, using that the
sample agrees with `(hC ω, hcirc ω)` on the good set `G0` and that the circle process is unchanged at radius `R > 0`
(`posCircle`).
-/

open HarmonicBalls MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace HarmonicBalls.S11ak

universe u

/-- On the good set, the sample has the original circle averages at every positive radius. -/
lemma sample_circle_apply {Ω : Type*} [MeasurableSpace Ω] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {G0 : Set Ω}
    (hG0c : ∀ ω ∈ G0, ContinuousOn (fun q : ℝ × ℂ => hcirc ω q.1 q.2) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)))
    {ω : Ω} (hω : ω ∈ G0) {R : ℝ} (hR : 0 < R) (z : ℂ) :
    (FirstPassS11aa.sample hC hcirc G0 hG0c ω).1.2 R z = hcirc ω R z := by
  show (FirstPassS11aa.sampleFun hC hcirc G0 ω).2 R z = hcirc ω R z
  rw [FirstPassS11aa.sampleFun_of_mem hω]
  simp [FirstPassS11aa.posCircle, hR]

/-- **Universe lift of the random-constant affine Weyl identity** (fp-S11ak, owner z6). For `Ω : Type u` with a whole-plane
GFF `(P, hC, hcirc)`, an LQG metric `𝔇` of exponent `ξ`, `R > 0` and a real `q`, almost surely for all `u v`, the Weyl
scaling of the metric of `h(R·) + (Q_γ log R - (hcirc R 0 + q))` at weight `-α₀ log|·|` equals
`e^{-ξ (hcirc R 0 + q - α₀ log R)}` times the Weyl scaling of the metric of `h` at `(R u, R v)`. -/
theorem ae_weylScaling_affinePullback_circle_universe {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (h𝔇 : IsLQGMetric γ ξ 𝔇) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {R : ℝ} (hR : 0 < R) (q α₀ : ℝ) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      weylScaling (𝔇 (addFunPairing (affinePullbackPairing (hC ω) R 0)
          (fun _ => lqgQ γ * Real.log R - (hcirc ω R 0 + q)))) ξ (fun x => -α₀ * Real.log ‖x‖) u v =
        ENNReal.ofReal (Real.exp (-(ξ * (hcirc ω R 0 + q - α₀ * Real.log R)))) *
          weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) (R * u) (R * v) := by
  obtain ⟨G0, hG0m, hG0, hG0c⟩ := FirstPassS11aa.exists_good_set hG.ae_continuousOn_circle
  have hS := FirstPassS11aa.isWholePlaneGFF_map_sample hG hG0m hG0 hG0c
  have hSm := FirstPassS11aa.measurable_sample hG0m hG.measurable_pairing hG.measurable_circle hG0c
  have hT := HarmonicBalls.ae_weylScaling_affinePullback_background hS 𝔇 h𝔇 hR
    (fun s : FirstPassS11aa.CircleSample => s.1.2 R 0 + q)
    ((FirstPassS11aa.measurable_circleCoord R 0).add_const q) α₀
  have h1 := ae_of_ae_map hSm.aemeasurable hT
  filter_upwards [h1, hG0] with ω hω hωG
  have hfst := FirstPassS11aa.sample_fst_eq (hC := hC) (hcirc := hcirc) hG0c hωG
  have hsnd := sample_circle_apply (hC := hC) (hcirc := hcirc) hG0c hωG hR 0
  simp only [hfst, hsnd] at hω
  exact hω

end HarmonicBalls.S11ak
