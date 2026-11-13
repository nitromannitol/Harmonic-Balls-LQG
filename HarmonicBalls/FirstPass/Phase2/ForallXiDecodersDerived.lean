import HarmonicBalls.FirstPass.Phase2.ForallXiCalibrationDerived
import HarmonicBalls.FirstPass.Phase2.LocalMetricReplacementR4Derived
import HarmonicBalls.FirstPass.Phase2.LQGXiCanonical
import HarmonicBalls.FirstPass.Phase2.CanonicalDecodersCanonXi

/-!
# Lemma 11.13, Proposition 11.11 and Theorem 1.2 for every Weyl exponent, without the local metric replacement

`ForallXiCalibrationDerived.lean` gives the corrected Lemma 11.13, Proposition 11.11 and Theorem 1.2 for every Weyl
exponent `ξ` from four inputs: the local metric replacement `hN2`, the measurable canonical decoders `hCanonM`, the Weyl
exponent of every γ-LQG metric `hXi` and the identification `hDim` of the paper's canonical exponent
`lqgXi γ = γ / lqgGraphDimension γ` with Gwynne-Miller's `LQGMetric.xiGamma γ`.

The local metric replacement is now a theorem (`localMetricReplacementStmt_derived`,
`Phase2/LocalMetricReplacementR4Derived.lean:33`), so the three results rest on `hCanonM`, `hXi` and `hDim` only. The
identification `hDim` follows from the graph-distance characterization of `d_γ` (Ding-Gwynne): if `LQGMetric.dGamma γ` is
the whole-plane graph-distance dimension (`IsWholePlaneLQGDimension`, `Defs/LQGGraphDistance.lean:97`), then
`lqgXi γ = LQGMetric.xiGamma γ` (`lqgXi_eq_xiGamma_of_isWholePlaneLQGDimension`, `Phase2/LQGXiCanonical.lean:50`); the
`*_of_dimension` forms bind that characterization instead of `hDim`.

The decoders are needed only at the canonical exponent: given `hXi` and `hDim`, at any `ξ ≠ lqgXi γ` no field carries an
LQG metric of Weyl exponent `ξ`, so the identification clause of `LQGCanonicalDecodersMeasurableExistStmt` holds
vacuously, and its other clauses do not involve `ξ` (`lqgCanonicalDecodersMeasurableExist_of_canonXi`). The
`*_of_canonXiDecoders` and `*_of_dimension` forms bind the canonical-exponent form
`LQGCanonicalDecodersMeasurableExistCanonXiStmt` (`Phase2/CanonicalDecodersCanonXi.lean:28`), which the frozen free-`ξ`
form implies (`lqgCanonicalDecodersMeasurableExistCanonXi_of_free`). The statements of the draft are unchanged.
-/

universe u

namespace HarmonicBalls

open MeasureTheory

/-- The local metric replacement on sample spaces in `Type`, in the binder form of `ForallXiCalibrationDerived.lean`. -/
theorem localMetricReplacement_zero_derived : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
    LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂ :=
  fun γ ξ _ _ _ c₁ c₂ r₁ r₂ => localMetricReplacementStmt_derived.{0} γ ξ c₁ c₂ r₁ r₂

/-- **Lemma 11.13 (corrected, every `ξ`, every universe)** from the measurable canonical decoders `hCanonM`, the Weyl
exponent of every γ-LQG metric `hXi` and the identification `hDim` of the canonical exponents. -/
theorem correctedLemma11_13_of_canonicalDecoders
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ)
    (hDim : ∀ γ : ℝ, 0 < γ → γ < 2 → lqgXi γ = LQGMetric.xiGamma γ) :
    CorrectedLemma11_13Stmt.{u} :=
  correctedLemma11_13_of_decoders localMetricReplacement_zero_derived hCanonM hXi hDim

/-- **Proposition 11.11 (every `ξ`, every universe)** from `hCanonM`, `hXi` and `hDim`. -/
theorem firstPass_11_11_of_canonicalDecoders
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ)
    (hDim : ∀ γ : ℝ, 0 < γ → γ < 2 → lqgXi γ = LQGMetric.xiGamma γ) :
    HarmonicBallNotMetricBallStmt.{u} :=
  firstPass_11_11_of_decoders localMetricReplacement_zero_derived hCanonM hXi hDim

/-- **Theorem 1.2 (every `ξ`, every universe)** from `hCanonM`, `hXi` and `hDim`. -/
theorem firstPass_1_2_of_canonicalDecoders
    (hCanonM : LQGCanonicalDecodersMeasurableExistStmt.{0})
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ)
    (hDim : ∀ γ : ℝ, 0 < γ → γ < 2 → lqgXi γ = LQGMetric.xiGamma γ) :
    HarmonicBallNoveltyStmt.{u} :=
  firstPass_1_2_of_decoders localMetricReplacement_zero_derived hCanonM hXi hDim

/-- **The free-`ξ` measurable decoders from the canonical-exponent ones.** If every γ-LQG metric has Weyl exponent
`LQGMetric.xiGamma γ` (`hXi`) and this is the paper's canonical exponent `lqgXi γ` (`hDim`), then at `ξ ≠ lqgXi γ` the
premise `IsLQGMetricOfField P γ ξ α₀ hC D` of the identification clause fails, and the kernel, the metric decoder and the
conull set `G` of the canonical exponent serve for every `ξ`. -/
theorem lqgCanonicalDecodersMeasurableExist_of_canonXi
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ)
    (hDim : ∀ γ : ℝ, 0 < γ → γ < 2 → lqgXi γ = LQGMetric.xiGamma γ)
    (h : LQGCanonicalDecodersMeasurableExistCanonXiStmt.{u}) : LQGCanonicalDecodersMeasurableExistStmt.{u} := by
  intro γ ξ α₀ hγ0 hγ2 hα
  obtain ⟨K, d, hK, hKc, hd, hId, G, hG, hGae, hGL⟩ := h γ α₀ hγ0 hγ2 hα
  refine ⟨K, d, hK, hKc, hd, ?_, G, hG, hGae, hGL⟩
  by_cases hξ : ξ = lqgXi γ
  · subst hξ
    exact hId
  · unfold S11n.LQGCanonicalIdentificationStmt
    intro Ω _ P hC hcirc μ D _ _ hD
    exfalso
    obtain ⟨𝔇, h𝔇, -⟩ := hD
    exact hξ ((hXi γ ξ hγ0 hγ2 𝔇 h𝔇).trans (hDim γ hγ0 hγ2).symm)

/-- **Lemma 11.13 (corrected, every `ξ`, every universe)** from the measurable decoders at the canonical exponent
`hCanonX`, `hXi` and `hDim`. -/
theorem correctedLemma11_13_of_canonXiDecoders
    (hCanonX : LQGCanonicalDecodersMeasurableExistCanonXiStmt.{0})
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ)
    (hDim : ∀ γ : ℝ, 0 < γ → γ < 2 → lqgXi γ = LQGMetric.xiGamma γ) :
    CorrectedLemma11_13Stmt.{u} :=
  correctedLemma11_13_of_canonicalDecoders (lqgCanonicalDecodersMeasurableExist_of_canonXi hXi hDim hCanonX) hXi hDim

/-- **Proposition 11.11 (every `ξ`, every universe)** from `hCanonX`, `hXi` and `hDim`. -/
theorem firstPass_11_11_of_canonXiDecoders
    (hCanonX : LQGCanonicalDecodersMeasurableExistCanonXiStmt.{0})
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ)
    (hDim : ∀ γ : ℝ, 0 < γ → γ < 2 → lqgXi γ = LQGMetric.xiGamma γ) :
    HarmonicBallNotMetricBallStmt.{u} :=
  firstPass_11_11_of_canonicalDecoders (lqgCanonicalDecodersMeasurableExist_of_canonXi hXi hDim hCanonX) hXi hDim

/-- **Theorem 1.2 (every `ξ`, every universe)** from `hCanonX`, `hXi` and `hDim`. -/
theorem firstPass_1_2_of_canonXiDecoders
    (hCanonX : LQGCanonicalDecodersMeasurableExistCanonXiStmt.{0})
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ)
    (hDim : ∀ γ : ℝ, 0 < γ → γ < 2 → lqgXi γ = LQGMetric.xiGamma γ) :
    HarmonicBallNoveltyStmt.{u} :=
  firstPass_1_2_of_canonicalDecoders (lqgCanonicalDecodersMeasurableExist_of_canonXi hXi hDim hCanonX) hXi hDim

/-- The identification of the canonical exponents from the graph-distance characterization of `d_γ`. -/
theorem lqgXi_eq_xiGamma_of_dimension
    (hDimW : ∀ γ : ℝ, 0 < γ → γ < 2 → IsWholePlaneLQGDimension γ (LQGMetric.dGamma γ)) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → lqgXi γ = LQGMetric.xiGamma γ :=
  fun γ hγ0 hγ2 => lqgXi_eq_xiGamma_of_isWholePlaneLQGDimension hγ0 hγ2 (hDimW γ hγ0 hγ2)

/-- **Lemma 11.13 (corrected, every `ξ`, every universe)** from the canonical-exponent decoders `hCanonX`,
`hXi` and the graph-distance characterization `hDimW` of `d_γ`. -/
theorem correctedLemma11_13_of_dimension
    (hCanonX : LQGCanonicalDecodersMeasurableExistCanonXiStmt.{0})
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ)
    (hDimW : ∀ γ : ℝ, 0 < γ → γ < 2 → IsWholePlaneLQGDimension γ (LQGMetric.dGamma γ)) :
    CorrectedLemma11_13Stmt.{u} :=
  correctedLemma11_13_of_canonXiDecoders hCanonX hXi (lqgXi_eq_xiGamma_of_dimension hDimW)

/-- **Proposition 11.11 (every `ξ`, every universe)** from `hCanonX`, `hXi` and `hDimW`. -/
theorem firstPass_11_11_of_dimension
    (hCanonX : LQGCanonicalDecodersMeasurableExistCanonXiStmt.{0})
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ)
    (hDimW : ∀ γ : ℝ, 0 < γ → γ < 2 → IsWholePlaneLQGDimension γ (LQGMetric.dGamma γ)) :
    HarmonicBallNotMetricBallStmt.{u} :=
  firstPass_11_11_of_canonXiDecoders hCanonX hXi (lqgXi_eq_xiGamma_of_dimension hDimW)

/-- **Theorem 1.2 (every `ξ`, every universe)** from `hCanonX`, `hXi` and `hDimW`. -/
theorem firstPass_1_2_of_dimension
    (hCanonX : LQGCanonicalDecodersMeasurableExistCanonXiStmt.{0})
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ)
    (hDimW : ∀ γ : ℝ, 0 < γ → γ < 2 → IsWholePlaneLQGDimension γ (LQGMetric.dGamma γ)) :
    HarmonicBallNoveltyStmt.{u} :=
  firstPass_1_2_of_canonXiDecoders hCanonX hXi (lqgXi_eq_xiGamma_of_dimension hDimW)

end HarmonicBalls
