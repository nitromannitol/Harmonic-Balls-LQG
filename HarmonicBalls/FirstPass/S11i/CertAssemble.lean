import HarmonicBalls.FirstPass.S11i.CertHcert
import HarmonicBalls.FirstPass.S11i.CertGeometry
import HarmonicBalls.FirstPass.S11i.CertWindow
import HarmonicBalls.Proposed.LQG

/-!
# Lemma 11.13, Steps 13-14: buffered certificate geometry into the pinch-window count (fp-S11i-11-13)

Composition of `HarmonicBalls.CertWindow.pinch_window_ae_of_cert` (hypotheses `hscale`, `hcert`, `hstep12`) with:
* `hcert`: `FirstPassS11i.hcert_of_buffered` (CertGeometry.lean), for the buffered geometry `IsBufferedPinchGeometry`
  with buffer `η = δ`; no geometric hypothesis is left;
* `hDlen`: almost sure Euclidean length property of the LQG metric, derived from the Proposed input
  `LQGMetricFieldAxioms` (Fact 2.2 I; Proposed/LQG.lean, pending operator source-check);
* `hscale`: the zoom family `μk`, `Dk` with its shape. The caller supplies it; `HarmonicBalls.ae_hscale_dyadic`
  (FirstPass/S11v.lean) produces such a family.

`hstep12` (Step 12, conclusion (10): the certificate window frequency tends to `q` at `μk`-almost every point of the unit
ball) is NOT proved here. It is an explicit hypothesis, stated for the given zoom family. It must not be quantified over all
families with the shape of `hscale`: the certificate event depends on the metric scale `b` in `Dk = b D(2^k ·, 2^k ·)`.
-/

universe u

namespace FirstPassS11i.CertAssemble

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls FirstPassS11i

/-- Almost surely the LQG metric is a Euclidean length metric (Fact 2.2 I, through the Proposed input
`LQGMetricFieldAxioms`). Used as `hDlen` of `hcert_of_buffered`. -/
theorem ae_isEuclideanLengthMetric_of_lqgMetric {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hAx : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hG : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ α hC D) : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) := by
  obtain ⟨𝔇, h𝔇, hae⟩ := hD
  unfold LQGMetricFieldAxioms at hAx
  have hax := hAx hG hγ hγ2 hα 𝔇 h𝔇
  filter_upwards [hax.1, hae] with ω hω hωD
  have hfun : D ω = fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v).toReal := by
    funext u v
    rw [← (hωD u v).2, ENNReal.toReal_ofReal (hωD u v).1]
  rw [hfun]
  exact hω.2

/-- **Lemma 11.13, Steps 13-14 (buffered geometry, zoom family given).** For the buffered geometry `hg` and the LQG pair
`(μ, D)` of the whole-plane model, with the zoom family `μk`, `Dk` (hypothesis `hsc`, shape of `ae_hscale_dyadic`) and the
certificate window frequency `hstep12` (Step 12), almost surely for `μ`-almost every `z` the pinch-window count is eventually
at least `q N / 4`. -/
theorem pinch_window_ae_buffered {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hAx : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hG : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ)
    (hγ2 : γ < 2) (hα : α < lqgQ γ) {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ α hC D)
    {Ostar U V W T Q' Q : Set ℂ} {δ M q : ℝ} (hg : IsBufferedPinchGeometry U V W T Q' Q δ) (hq : 0 < q)
    (μk : ℕ → Ω → Measure ℂ) (Dk : ℕ → Ω → ℂ → ℂ → ℝ)
    (hsc : ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      μk k ω = ENNReal.ofReal a • (μ ω).map (fun x : ℂ => x / ((((2 : ℝ) ^ k : ℝ)) : ℂ)) ∧
      ∀ u v : ℂ, Dk k ω u v = b * D ω ((((2 : ℝ) ^ k : ℝ) : ℂ) * u) ((((2 : ℝ) ^ k : ℝ) : ℂ) * v))
    (hstep12 : ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ w ∂(μk k ω), w ∈ ball (0 : ℂ) 1 →
      Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        windowCert Ostar U V W T Q' Q δ M μk Dk k ω n w}.ncard : ℝ) / (N : ℝ)) atTop (𝓝 q)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ᶠ N : ℕ in atTop,
      q / 4 * (N : ℝ) ≤
        ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ) := by
  have hDk : ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ u v : ℂ, Dk k ω u v = b * D ω ((((2 : ℝ) ^ k : ℝ) : ℂ) * u) ((((2 : ℝ) ^ k : ℝ) : ℂ) * v) :=
    fun k => (hsc k).mono fun ω h => by
      obtain ⟨_, b, _, hb, _, hDe⟩ := h
      exact ⟨b, hb, hDe⟩
  exact HarmonicBalls.CertWindow.pinch_window_ae_of_cert P μ D U T Q' Q M q hq
    (windowCert Ostar U V W T Q' Q δ M μk Dk) μk Dk hsc
    (hcert_of_buffered P D (ae_isEuclideanLengthMetric_of_lqgMetric hAx hG hγ hγ2 hα hD) μk Dk hDk hg)
    hstep12

end FirstPassS11i.CertAssemble

#print axioms FirstPassS11i.CertAssemble.ae_isEuclideanLengthMetric_of_lqgMetric
#print axioms FirstPassS11i.CertAssemble.pinch_window_ae_buffered
