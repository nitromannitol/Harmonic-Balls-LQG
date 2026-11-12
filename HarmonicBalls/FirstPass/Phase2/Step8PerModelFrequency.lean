import HarmonicBalls.FirstPass.S11i.CertAssemble
import HarmonicBalls.FirstPass.S11i.Faithful
import HarmonicBalls.FirstPass.Frozen.S11j

/-!
# Lemma 11.13 (canonical exponent) from the certificate frequency of each model

`CorrectedLemma11_13CanonicalStmt` (`S11i/Faithful.lean:101`) chooses the density `δ` after the model
`(P, hC, hcirc, μ, D)`. The window lower bound for the pinch-point events, `pinch_window_ae_buffered`
(`S11i/CertAssemble.lean:50`), needs, for that one model, a number `q > 0`, the dyadic zoom families `μk`, `Dk` and the
almost sure convergence to `q` of the window frequency of the certificate events (paper, Lemma 11.13, Step 8,
`eq:dyadic-frequency`, with `q = P[E₁^{h^γ}(0; M)]` for the LQG metric of the model).

`Step8CertificateFrequencyPerModelStmt` is this input for each model separately. Its limit `q` may depend on the model,
hence on the LQG metric `𝔇` of the model. The event calibration `Step8EventCalibrationStmt`
(`S11i/Step8PhysExists.lean:108`) asks instead for one limit, the canonical probability of a field event, for every
metric `𝔇` with `IsLQGMetric γ (lqgXi γ) 𝔇`. Since `IsLQGMetric` lists the axioms of the LQG metric only, that common
limit amounts to the uniqueness of the LQG metric up to a deterministic factor (Gwynne-Miller, arXiv:1905.00383v3,
Theorem 1.2, p. 6). The statement here does not need it: for a fixed metric, the frequency limit is the probability of
the certificate event for that metric.

* `firstPass_11_13_canonical_of_perModelFrequency`: Lemma 11.13 (canonical) from the field axioms `hAx` and the
  per-model certificate frequency `hPM`. The Lemma 11.12 event is not used.
-/

universe u

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- **Step 8 of Lemma 11.13, for each model.** For every buffered geometry, `0 < γ < 2`, `α₀ < Q_γ`, `M > 0`, and every
whole-plane model `(P, hC, hcirc, μ, D)` with insertion `α₀` on a space `Ω : Type u`, there are `q > 0` and dyadic zoom
families `μk k = a • μ ∘ (· / 2^k)⁻¹`, `Dk k = b · D(2^k ·, 2^k ·)` such that, for every `k`, almost surely and for
`μk k`-almost every `w ∈ B₁(0)`, the window frequency of the certificate events (`windowCert`, `O_* = pinchOmegaGeom W Q δ₀`,
`η = δ₀`) at the radii `2⁻ⁿ` tends to `q`. -/
def Step8CertificateFrequencyPerModelStmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ₀ →
  ∀ γ α₀ M : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → 0 < M →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    IsLQGMetricOfField P γ (lqgXi γ) α₀ hC D →
    ∃ q : ℝ, 0 < q ∧ ∃ (μk : ℕ → Ω → Measure ℂ) (Dk : ℕ → Ω → ℂ → ℂ → ℝ),
      (∀ k : ℕ, ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
        μk k ω = ENNReal.ofReal a • (μ ω).map (fun x : ℂ => x / ((((2 : ℝ) ^ k : ℝ)) : ℂ)) ∧
        ∀ u v : ℂ, Dk k ω u v = b * D ω ((((2 : ℝ) ^ k : ℝ) : ℂ) * u) ((((2 : ℝ) ^ k : ℝ) : ℂ) * v)) ∧
      ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ w ∂(μk k ω), w ∈ ball (0 : ℂ) 1 →
        Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
          _root_.FirstPassS11i.windowCert (pinchOmegaGeom W Q δ₀) U V W T Q' Q δ₀ M μk Dk k ω n w}.ncard : ℝ) /
            (N : ℝ)) atTop (𝓝 q)

/-- **Lemma 11.13 (canonical exponent) from the per-model certificate frequency.** The density is
`δ = min (q / 4) (1 / 2)`, with `q` the frequency limit of the model; the window bound is `pinch_window_ae_buffered`. -/
theorem firstPass_11_13_canonical_of_perModelFrequency (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hPM : Step8CertificateFrequencyPerModelStmt.{u}) : CorrectedLemma11_13CanonicalStmt.{u} := by
  intro U V W T Q' Q δ₀ hgeom γ α₀ hγ0 hγ2 hα M hM Ω _ P hC hcirc μ D hG hμ hD
  obtain ⟨q, hq, μk, Dk, hsc, hstep⟩ :=
    hPM U V W T Q' Q δ₀ hgeom γ α₀ M hγ0 hγ2 hα hM Ω P hC hcirc μ D hG hμ hD
  refine ⟨min (q / 4) (1 / 2), ⟨lt_min (by positivity) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩, ?_⟩
  exact (_root_.FirstPassS11i.CertAssemble.pinch_window_ae_buffered (hAx Ω P γ (lqgXi γ) α₀ hC hcirc) hG hγ0 hγ2
    hα hD hgeom hq μk Dk hsc hstep).mono fun ω hω => hω.mono fun z hz => hz.mono fun N hN =>
      le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg N)) hN

end HarmonicBalls
