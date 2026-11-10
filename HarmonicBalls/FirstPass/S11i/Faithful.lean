import HarmonicBalls.Draft.Section11
import HarmonicBalls.Draft.Section6
import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.FirstPass.S11h.LocalEvents

/-!
# Faithful forms of Lemmas 11.12 and 11.13 (corrected paper), first pass fp-S11i (owner n3)

Operator note 2026-11-09 20:59 UTC (`notes/fp-gaps/CHATGPT-hb-s11-fidelity.md`, sections 2 and 3): the Draft forms are
too weak. This file states the corrected forms; `firstPass_11_12_corrected` and `firstPass_11_13_corrected` will prove
them.

* `CorrectedLemma11_12Stmt` (corrected paper lines 3236-3244, correction `[C43]`): for every fixed buffered geometry
  (`IsBufferedPinchGeometry`, corrected lines 3157-3201), every insertion `α < Q` and `M > 0`, there is one event rule
  `E` on the local field modulo additive constants on `B₇(0)`, measurable, independent of `α`, such that for each model
  `P[E^α(M)] > 0` and `E^α(M) ⊆ Ĝ₁^{h^α}(0; M)` almost surely. Here `E^α(M) = {ω : h^α|_{B₇} mod constants ∈ E}`.
* `CorrectedLemma11_13Stmt` (corrected lemma `lemma:mu_h-pinch-bad`): for every buffered geometry, `γ, α₀, ξ`, `M > 0`
  there is a deterministic `δ ∈ (0,1)` (chosen before the probability space) such that almost surely, for `μ`-a.e. `z`,
  eventually in `N`, `δ N ≤ #{n ∈ [N+1, 2N] : Ĝ_n(z; M) occurs}`.

Local field modulo constants: the pairings of the field with mean-zero test functions supported in `U`. Adding a constant
to the field changes no such pairing, so constant invariance holds by construction.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- The local field `h^α|_U` modulo additive constants: the functions `φ ↦ (h^α, φ)` on mean-zero test functions
supported in `U`. -/
abbrev ModConstTestPairings (U : Set ℂ) : Type :=
  {φ : ℂ → ℝ // IsTestFunction U φ ∧ ∫ x, φ x = 0} → ℝ

/-- The restriction to `U` modulo constants of the field `h^α = h^ℂ - α log|·|` of the model `hC`, at `ω`. -/
noncomputable def localModConstField {Ω : Type*} (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) (ω : Ω) :
    ModConstTestPairings U :=
  fun φ => fieldPairing α (hC ω) φ.1

set_option linter.style.haveILetI false in
/-- The restriction `h^α|_U` modulo constants is measurable for `σ(h^α|_U)` modulo constants
(`Section6.fieldSigmaAlgebraModConst`, `HarmonicBalls/Draft/Section6.lean:148`). Its coordinates are the generators of that
σ-algebra. -/
theorem localModConstField_measurable {Ω : Type*} (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) :
    Measurable[Section6.fieldSigmaAlgebraModConst α hC U] (localModConstField α hC U) := by
  letI m : MeasurableSpace Ω := Section6.fieldSigmaAlgebraModConst α hC U
  refine Measurable.of_eval fun φ => ?_
  refine measurable_iff_comap_le.mpr ?_
  unfold Section6.fieldSigmaAlgebraModConst
  exact le_iSup₂_of_le (f := fun (ψ : ℂ → ℝ) (_ : IsTestFunction U ψ ∧ ∫ x, ψ x = 0) =>
    MeasurableSpace.comap (fun ω => fieldPairing α (hC ω) ψ) inferInstance) φ.1 φ.2 le_rfl

/-- Lemma 11.12 in the corrected form (`[C43]`, corrected paper lines 3236-3244). For every buffered geometry, `γ`,
`ξ`, `M > 0` there is one measurable rule `E` on the local field modulo constants on `B₇(0)`, such that for every
`α < Q = lqgQ γ` and every model: `E^α(M)` is `σ(h^α|_{B₇})`-measurable modulo constants, `P[E^α(M)] > 0`, and
`E^α(M) ⊆ Ĝ₁^{h^α}(0; M)` almost surely (Euclidean radius one, centre zero).

The geometry hypothesis `{0} ∪ ∂B₅ ⊆ pinchOmegaGeom W Q δ₀` (the component `Ω_geom` of `0` in `B₇ \ (…)`, which must
contain the origin and the circle `∂B₅`) is the corrected-paper clause of corrected paper lines 3186-3199, added by the
operator ruling R1 (02:20 UTC). It is not part of `IsBufferedPinchGeometry`, which is unchanged. -/
def CorrectedLemma11_12Stmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ₀ →
  insert (0 : ℂ) (sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ₀ →
  ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ M : ℝ, 0 < M →
  ∃ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), MeasurableSet E ∧
  ∀ α : ℝ, α < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ → IsLQGMetricOfField P γ ξ α hC D →
    MeasurableSet[Section6.fieldSigmaAlgebraModConst α hC (ball (0 : ℂ) 7)]
      {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} ∧
    0 < P {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} ∧
    ∀ᵐ ω ∂P, localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E →
      pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0

/-- Lemma 11.13 in the corrected form (`lemma:mu_h-pinch-bad`, corrected paper lines 3251-3263), quantified over every
buffered geometry (`[C42]`, corrected lines 3157-3201). The density `δ` is chosen before the probability space.
The component clause `insert 0 (sphere 0 5) ⊆ pinchOmegaGeom W Q δ₀` (corrected lines 3180-3200) is derived from the buffered
geometry (`FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom`), so it is not a hypothesis here. -/
def CorrectedLemma11_13Stmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ₀ →
  ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ M : ℝ, 0 < M →
  ∃ δ ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ᶠ N in atTop,
      δ * N ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ)

end HarmonicBalls
