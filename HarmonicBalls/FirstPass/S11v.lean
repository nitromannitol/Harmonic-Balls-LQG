import HarmonicBalls.FirstPass.S11v.Pullback

/-!
# Lemma 11.13, hypothesis `hscale` of `CertWindow.pinch_window_ae_of_cert` (fp-S11v-11-13-hscale)

`HarmonicBalls.FirstPass.S11i.CertWindow.pinch_window_ae_of_cert` takes the zoom hypothesis
`hscale : ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ a b, 0 < a ∧ 0 < b ∧ μk k ω = ofReal a • (μ ω).map (· / 2^k) ∧ Dk k ω u v = b * D ω (2^k u) (2^k v)`.
`ae_hscale_dyadic` provides `μk`, `Dk` with this shape and with `μk k`, `Dk k` the LQG measure and LQG metric of the
pulled-back model at scale `2^k` (`ae_isLQGMeasureOfField_dyadicZoom`, `ae_isLQGMetricOfField_zoom`, FirstPass/S11v/Pullback.lean).
The zoom is the affine pullback with `R = 2^k`, `k : ℕ`: it is the direction of `isLQGLimit_dilate_dyadic`. The inverse direction
`R = 1/2` of `S11s/Transfer.lean` is not used here.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- **Zoom family at every dyadic scale `2^k`, `k : ℕ` (exact form of `hscale`).** For an LQG measure `μ` and an LQG metric `D` of
a whole-plane GFF model, there are the LQG measures `μk k` and LQG metrics `Dk k` of the pulled-back models at scale `2^k`, and
almost surely for every `k` they are constant multiples of `μ.map (· / 2^k)` and of `D(2^k ·, 2^k ·)`. -/
theorem ae_hscale_dyadic {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {γ ξ α : ℝ} (hγ : 0 < γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ α hC D) :
    ∃ (μk : ℕ → Ω → Measure ℂ) (Dk : ℕ → Ω → ℂ → ℂ → ℝ),
      (∀ k : ℕ, IsLQGMeasureOfField P γ α
        (fun ω ρ z => hcirc ω (((2 : ℝ) ^ k) * ρ) ((((2 : ℝ) ^ k : ℝ) : ℂ) * z) - hcirc ω ((2 : ℝ) ^ k) 0) (μk k)) ∧
      (∀ k : ℕ, IsLQGMetricOfField P γ ξ α
        (fun ω => normDilatePairing (hC ω) (hcirc ω ((2 : ℝ) ^ k) 0) ((2 : ℝ) ^ k)) (Dk k)) ∧
      ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
        μk k ω = ENNReal.ofReal a • (μ ω).map (fun x : ℂ => x / ((((2 : ℝ) ^ k : ℝ)) : ℂ)) ∧
        ∀ u v : ℂ, Dk k ω u v = b * D ω ((((2 : ℝ) ^ k : ℝ) : ℂ) * u) ((((2 : ℝ) ^ k : ℝ) : ℂ) * v) := by
  refine ⟨fun k ω => ENNReal.ofReal (Real.exp (-(γ * dilationConstant γ (fieldCircleAverage α (hcirc ω))
      ((2 : ℝ) ^ k)))) • (μ ω).map (fun w : ℂ => w / (((2 : ℝ) ^ k : ℝ) : ℂ)),
    fun k ω u v => Real.exp (-(ξ * (fieldCircleAverage α (hcirc ω) ((2 : ℝ) ^ k) 0
      + lqgQ γ * Real.log ((2 : ℝ) ^ k)))) * D ω ((((2 : ℝ) ^ k : ℝ) : ℂ) * u) ((((2 : ℝ) ^ k : ℝ) : ℂ) * v),
    fun k => ae_isLQGMeasureOfField_dyadicZoom P hγ hG hμ k,
    fun k => ae_isLQGMetricOfField_zoom P hG hD (R := (2 : ℝ) ^ k) (by positivity), fun k => ?_⟩
  exact ae_of_all _ fun ω => ⟨Real.exp (-(γ * dilationConstant γ (fieldCircleAverage α (hcirc ω)) ((2 : ℝ) ^ k))),
    Real.exp (-(ξ * (fieldCircleAverage α (hcirc ω) ((2 : ℝ) ^ k) 0 + lqgQ γ * Real.log ((2 : ℝ) ^ k)))),
    Real.exp_pos _, Real.exp_pos _, rfl, fun u v => rfl⟩

end HarmonicBalls
