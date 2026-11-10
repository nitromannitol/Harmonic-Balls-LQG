import HarmonicBalls.FirstPass.Closure.Bridge12

/-!
# Canonical-exponent form of Lemma 11.13 for the closures of 1.2 and 11.11 (fp-11-13-canonical-bridge-1-2-11-11, z4)

FIRST-PASS plumbing, deterministic (no probability). Source: `notes/fp-gaps/CHATGPT-224-hb-11-13-target-audit-PRO.md` §5,
Correction 1 (canonical exponent `ξ = lqgXi γ`, `FirstPass/S11i/Faithful.lean:94`) and Correction 3 (the model
`(Ω, P, hC, hcirc, μ, D)` is quantified before `∃ δ`, the exact PASS form).

* `ManyPinchScalesCanonicalStmt`: `ManyPinchScalesStmt` (`Draft/Section11.lean:259`) with `ξ := lqgXi γ`, body otherwise
  copied. Its density `δ` is chosen before the probability space (uniform in the model), as in the printed statement.
* `ManyPinchScalesCanonicalModelStmt`: the same geometry and pinch event, with the model quantified before `∃ δ`.
* `manyPinchScalesCanonicalModel_of_canonical`: `CorrectedLemma11_13CanonicalStmt` implies the model-dependent form,
  with the geometry fixed by `exists_bufferedPinchGeometry` (the closed form of `Closure/Bridge12.lean`).

Not given: `CorrectedLemma11_13CanonicalStmt → ManyPinchScalesCanonicalStmt`. The canonical hypothesis gives `∃ δ` after
the model, and the uniform form needs `∃ δ` before it. Swapping these two quantifiers is not plumbing (cross-model
uniformity, chat 224 Correction 3, `STRONGER-BUT-PROVED`). The 1.2 and 11.11 consumers fix the model before using `δ`
(see the report), so they need only the model-dependent form.
-/

open MeasureTheory Set Filter Topology

universe u

namespace HarmonicBalls.Closure

/-- `ManyPinchScalesStmt` (`Draft/Section11.lean:259`) with the canonical Weyl exponent `ξ = lqgXi γ` (Correction 1).
The density `δ` is still chosen before the probability space (uniform in the model). -/
def ManyPinchScalesCanonicalStmt : Prop :=
  ∃ U T Q' Q : Set ℂ, IsPinchPointConfiguration U T Q' Q ∧
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ M : ℝ, 0 < M → ∃ δ ∈ Ioo (0 : ℝ) 1,
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ (lqgXi γ) α₀ hC D →
  ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ᶠ N in atTop,
    δ * N ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
      pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ)

/-- Lemma 11.13 at the canonical exponent `ξ = lqgXi γ`, with the model quantified before `∃ δ` (Correction 3, PASS form):
the pinch geometry is fixed first, then the model, then the density. Same pinch event as `ManyPinchScalesStmt`. -/
def ManyPinchScalesCanonicalModelStmt : Prop :=
  ∃ U T Q' Q : Set ℂ, IsPinchPointConfiguration U T Q' Q ∧
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ M : ℝ, 0 < M →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ (lqgXi γ) α₀ hC D →
  ∃ δ ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ᶠ N in atTop,
    δ * N ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
      pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ)

/-- `CorrectedLemma11_13CanonicalStmt` implies `ManyPinchScalesCanonicalModelStmt`: fix the buffered geometry of
`exists_bufferedPinchGeometry` (closed form, no hypothesis on `T`), keep the model-dependent density. -/
theorem manyPinchScalesCanonicalModel_of_canonical (h : CorrectedLemma11_13CanonicalStmt.{u}) :
    ManyPinchScalesCanonicalModelStmt.{u} := by
  obtain ⟨U, V, W, T, Q', Q, δ₀, hgeom⟩ := exists_bufferedPinchGeometry
  exact ⟨U, T, Q', Q, hgeom.toPinchPointConfiguration,
    fun γ α₀ hγ hγ₂ hα M hM Ω _ P hC hcirc μ D hgff hμ hmetric =>
      h U V W T Q' Q δ₀ hgeom γ α₀ hγ hγ₂ hα M hM Ω P hC hcirc μ D hgff hμ hmetric⟩

end HarmonicBalls.Closure
