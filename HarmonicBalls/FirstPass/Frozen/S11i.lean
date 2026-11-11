import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Proposed.DuplantierMillerSheffield

/-!
# Frozen inputs of the S11i chain (Lemma 11.13)

Each `def` below is an EXTERNAL fact (general GFF / LQG background, not a statement about the clusters,
odometers or harmonic balls of this paper), stated in the weakest form the proofs use.

`DMSLemmaA10WholePlaneMarked` imports the formula `dmsShiftedPairing` (the shift `z ↦ -γ log|· - z| + γ log max(|·|,1)`
and its circle-average constant) from `Proposed/DuplantierMillerSheffield.lean`. That file is a definition only; the
frozen Prop does not depend on the pending source-check of the unmarked Proposed Prop `DMSLemmaA10WholePlaneUnnormalized`.
-/

namespace HarmonicBalls

open MeasureTheory Metric
open scoped ENNReal

/-- RETIRED (derived), not an input. Formerly a frozen input: measurability of the dyadic circle
averages in the centre variable. It is now derived from `IsWholePlaneGFF.ae_continuousOn_circle`
(`HarmonicBalls.SingularWeyl.ae_measurable_dyadic_circleAverage`, S11i/SingularWeyl.lean); no proof uses this `def`. -/
def CircleAverageVersionMeasurableStmt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ k : ℕ, Measurable (fun z : ℂ => hcirc ω (dyadicScale k) z)

/-- FROZEN (marked DMS). Truth check TRUE, assuming the normalization encoded by
`dmsShiftedPairing` (whole-plane GFF with unit-circle average zero; no factor `π⁻¹`: both sides have total mass `π`).
Marked whole-plane form of Duplantier-Miller-Sheffield Lemma A.10 for `D = B₁`, unnormalized, with `ℝ≥0∞`-valued
marked test functions `Ψ(h, z)`. Under `P(dω) μ_ω(dz)` restricted to `z ∈ B₁`, the marked pair `(h, z)` has the same
mass as the image of Lebesgue measure on `B₁` times `P` under `ω ↦ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z)`.
Source: DMS, arXiv:1409.7055v4, Appendix A, Lemma A.10, p. 184, whole-plane clause AND ITS PROOF (the proof starts from the
regularized weighting `ε^{γ²/2} e^{γ h_ε(u)} du dh` and conditions on the chosen point), together with Duplantier-Sheffield,
arXiv:0808.1560, §3.3 (rooted random measures; the rooted measure Θ on pairs `(z, h)`).
NOT verbatim: the printed lemma states the field marginal only, as `DMSLemmaA10WholePlaneUnnormalized`
(Proposed/DuplantierMillerSheffield.lean:73), which discards the mark `z`; the marked identity is read off the proof.
Truth check: FALSE as universally typed
(missing `0 < γ` and `γ < 2`). At a fixed `0 < γ < 2` it follows from `DMSLemmaA10WholePlaneMarkedSub` by
`dmsA10Marked_of_sub`; top-level theorems take the Sub form. -/
def DMSLemmaA10WholePlaneMarked {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) : Prop :=
  IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
    ∀ Ψ : (((ℂ → ℝ) → ℝ) × ℂ) → ℝ≥0∞,
      Measurable[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance] Ψ →
        ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (hC ω, z) ∂(μ ω) ∂P
          = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) ∂P ∂volume

/-- FROZEN. Same parameters and body as `DMSLemmaA10WholePlaneMarked`; the subcritical
range `0 < γ` and `γ < 2` is inserted after the two old antecedents, so call sites keep their argument order.
Truth check: TRUE. The subcritical range `0 < γ` and `γ < 2` is part of this statement, and the identity holds for
each such `γ`.
The identity is unnormalized; no factor `π⁻¹`; both sides have total mass `π`.
Marked whole-plane form of Duplantier-Miller-Sheffield Lemma A.10 for `D = B₁`, unnormalized, with `ℝ≥0∞`-valued
marked test functions `Ψ(h, z)`. Source: DMS, arXiv:1409.7055v4, Appendix A.1, Lemma A.10, printed p. 184, whole-plane
clause and its proof; Duplantier-Sheffield, arXiv:0808.1560, §3.3 (rooted random measures). -/
def DMSLemmaA10WholePlaneMarkedSub {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) : Prop :=
  IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ → 0 < γ → γ < 2 →
    ∀ Ψ : (((ℂ → ℝ) → ℝ) × ℂ) → ℝ≥0∞,
      Measurable[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance] Ψ →
        ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (hC ω, z) ∂(μ ω) ∂P
          = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) ∂P ∂volume

/-- At a fixed subcritical `0 < γ < 2`, the Sub form gives the marked form `DMSLemmaA10WholePlaneMarked`
(hypothesis threading only; no new mathematics). -/
theorem dmsA10Marked_of_sub {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (h : DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ) (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    DMSLemmaA10WholePlaneMarked P γ hC hcirc μ :=
  fun hW hL => h hW hL hγ0 hγ2

end HarmonicBalls
