import HarmonicBalls.FirstPass.S11i.CertAssemble
import HarmonicBalls.FirstPass.S11i.Faithful

/-!
# Lemma 11.13 (corrected): conditional assembly from the zoom-family window frequency (fp-S11i, owner n3)

Route A (`notes/n3.md`): `FirstPassS11i.CertAssemble.pinch_window_ae_buffered` gives, almost surely and for `μ`-a.e. `z`,
the pinch-window count bound `q/4 * N ≤ #{n ∈ [N+1, 2N] : pinchPointEvent ...}` from the zoom-family window frequency
(Step 12 of the corrected proof of `lemma:mu_h-pinch-bad`). This file assembles `CorrectedLemma11_13Stmt` from that input.

Named inputs (neither frozen nor proved here):
* `hAx`: `LQGMetricFieldAxioms` (Proposed, Fact 2.2 I-IV; operator-approved), used only for the Euclidean length property.
* `hZoom`: `ZoomWindowFrequencyStmt` (NEW, Step 12 of Lemma 11.13 for the zoom family). It asserts a deterministic
  `q > 0` that is the a.s. limit of the certificate window frequency. Its positivity is meant to be the probability of the
  certificate event of Lemma 11.12 (`FirstPassS11i.certificate_canonical_pos`); that identity is not in Lean yet.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

universe u

/-- **Zoom-family window frequency (Step 12 of Lemma 11.13, NEW; named input).** For the buffered geometry
`U V W T Q' Q` with buffer `δ`, the insertion `α₀`, `γ`, `ξ`, `M` and a deterministic limit `q`: there is an open set
`Ostar` with `0 ∈ Ostar` and `sphere 0 5 ⊆ Ostar` (the `O_*` of the certificate event) such that for every whole-plane
model with `IsLQGMeasureOfField P γ α₀ hcirc μ` and `IsLQGMetricOfField P γ ξ α₀ hC D` there is a zoom family `μk, Dk` at
dyadic scales `2^k` (the scaling shape of `ae_hscale_dyadic`) whose window certificate frequency converges to `q`, for
every `k`, almost surely, for `μk`-almost every centre `w` in `B₁(0)`.

Source (corrected paper, `paper/lqg_harmonic_ball-corrected.tex`, eq. `s11-pinch:eq:dyadic-frequency` at line 3832, proof
of `lemma:mu_h-pinch-bad` at lines 3848-3930): the dyadic frequency converges almost surely to `p_α(M)`, the probability of
the Lemma 11.12 event at scale one, so `q = p_α₀(M)`. The positivity `q > 0` is the positive-probability clause of
Lemma 11.12 (`CorrectedLemma11_12Stmt`, Faithful.lean:56). Neither the identity `q = P(E^{α₀}(M))` nor the positivity is
in Lean yet: this is the named input. Open point: `IsWholePlaneGFF` (Defs/GFF.lean:93) does not state that `P` is a
probability measure, so `P(E)` need not be finite there. -/
def ZoomWindowFrequencyStmt (γ ξ α₀ : ℝ) (U V W T Q' Q : Set ℂ) (δ M q : ℝ) : Prop :=
  ∃ Ostar : Set ℂ, IsOpen Ostar ∧ (0 : ℂ) ∈ Ostar ∧ sphere (0 : ℂ) 5 ⊆ Ostar ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
      ∃ (μk : ℕ → Ω → Measure ℂ) (Dk : ℕ → Ω → ℂ → ℂ → ℝ),
        (∀ k : ℕ, ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
          μk k ω = ENNReal.ofReal a • (μ ω).map (fun x : ℂ => x / ((((2 : ℝ) ^ k : ℝ)) : ℂ)) ∧
          ∀ x y : ℂ, Dk k ω x y = b * D ω ((((2 : ℝ) ^ k : ℝ) : ℂ) * x) ((((2 : ℝ) ^ k : ℝ) : ℂ) * y)) ∧
        ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ w ∂(μk k ω), w ∈ ball (0 : ℂ) 1 →
          Tendsto (fun N : ℕ => ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
            FirstPassS11i.windowCert Ostar U V W T Q' Q δ M μk Dk k ω n w}.ncard : ℝ) / (N : ℝ)) atTop (𝓝 q)

/-- **Lemma 11.13 (corrected), conditional on the zoom-family window frequency.** The density is
`δ = min (q/4) (1/2)`, chosen before the probability space (`q` depends only on the geometry, `γ`, `ξ`, `α₀`, `M`). -/
theorem correctedLemma11_13_of_zoom
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hZoom : ∀ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ₀ →
      ∀ γ ξ α₀ M : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → 0 < M →
        ∃ q : ℝ, 0 < q ∧ ZoomWindowFrequencyStmt.{u} γ ξ α₀ U V W T Q' Q δ₀ M q) :
    CorrectedLemma11_13Stmt.{u} := by
  intro U V W T Q' Q δ₀ hgeom γ α₀ ξ hγ0 hγ2 hα M hM
  obtain ⟨q, hq, Ostar, -, -, -, hfreq⟩ := hZoom U V W T Q' Q δ₀ hgeom γ ξ α₀ M hγ0 hγ2 hα hM
  refine ⟨min (q / 4) (1 / 2), ⟨lt_min (div_pos hq (by norm_num)) (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩, ?_⟩
  intro Ω _ P hC hcirc μ D hG hμ hD
  obtain ⟨μk, Dk, hsc, hstep⟩ := hfreq Ω P hC hcirc μ D hG hμ hD
  exact (FirstPassS11i.CertAssemble.pinch_window_ae_buffered (hAx γ ξ α₀ Ω P hC hcirc) hG hγ0 hγ2 hα hD hgeom hq
    μk Dk hsc hstep).mono fun ω hω => hω.mono fun z hz => hz.mono fun N hN =>
      le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg N)) hN

end HarmonicBalls

#print axioms HarmonicBalls.correctedLemma11_13_of_zoom
