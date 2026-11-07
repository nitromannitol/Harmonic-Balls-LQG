import HarmonicBalls.Draft.Section11

/-! # Corrected Section 11 pinch geometry and statements

The dimension function is a parameter: the existing metric interface does not
define the LQG dimension `d_γ`. To recover the paper's statement, instantiate
it with the LQG metric dimension. Positivity alone does not identify that
function. The frozen Section 11 statements remain unchanged.
-/

open MeasureTheory Metric Set Filter

namespace HarmonicBalls

universe u

/-- The obstacle-free component used in the corrected pinch construction. -/
noncomputable def pinchCorridor (W Q : Set ℂ) (δ : ℝ) : Set ℂ :=
  connectedComponentIn
    (ball (0 : ℂ) 7 \ (closure (thickening (2 * δ) Q) ∪
      closure (thickening (2 * δ) W))) 0

/-- Buffered keyhole geometry in the corrected draft, including the
component needed for paths around the two obstacles. The inherited fields
retain the hypotheses used by the deterministic metric-ball consequence. -/
structure IsCorrectedPinchConfiguration (U V W T Q' Q : Set ℂ) (δ : ℝ) : Prop
    extends IsPinchPointProofConfiguration U V W T Q' Q δ where
  delta_small : δ < 1 / 1000
  buffer_T : closure (thickening (10 * δ) (closure T)) ⊆ annulus 0 1 6
  buffer_U : closure (thickening (10 * δ) (closure U)) ⊆ V
  buffer_V : closure (thickening (10 * δ) (closure V)) ⊆ W
  buffer_W : closure (thickening (10 * δ) (closure W)) ⊆ T ∩ annulus 0 1 2
  buffer_Q' : closure (thickening (10 * δ) (closure Q')) ⊆ Q
  buffer_Q : closure (thickening (10 * δ) (closure Q)) ⊆
    annulus 0 4 5 \ thickening (10 * δ) (closure T)
  corridor_contains : ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchCorridor W Q δ

/-- Positive block density for the pinch events associated with fixed sets. -/
def PinchBlockDensity (μ : Measure ℂ) (D : ℂ → ℂ → ℝ)
    (U T Q' Q : Set ℂ) (M q : ℝ) (z : ℂ) : Prop :=
  ∀ᶠ N : ℕ in atTop, q * N ≤
    ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
      pinchPointEvent μ D U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ)

/-- Corrected Lemma 11.13, for the fixed dimension function `dγ` and Weyl
exponent `γ / dγ γ`. Its geometry is selected once, before the parameters. -/
def CorrectedManyPinchScalesStmt (dγ : ℝ → ℝ) : Prop :=
  ∃ U V W T Q' Q : Set ℂ, ∃ ε : ℝ, IsCorrectedPinchConfiguration U V W T Q' Q ε ∧
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → 0 < dγ γ →
  ∀ M : ℝ, 0 < M → ∃ q ∈ Ioo (0 : ℝ) 1,
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    IsLQGMetricOfField P γ (γ / dγ γ) α₀ hC D →
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), PinchBlockDensity (μ ω) (D ω) U T Q' Q M q z

/-- Lemma 11.14 for every corrected geometry and the physical exponent
specified by `dγ`. -/
def CorrectedPinchMetricBallConsequenceStmt (dγ : ℝ → ℝ) : Prop :=
  ∀ U V W T Q' Q : Set ℂ, ∀ ε : ℝ, IsCorrectedPinchConfiguration U V W T Q' Q ε →
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → 0 < dγ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    IsLQGMetricOfField P γ (γ / dγ γ) α₀ hC D →
  ∀ᵐ ω ∂P, ∀ M : ℝ, 0 < M → ∀ z : ℂ, ∀ r : ℝ, 0 < r → (0 : ℂ) ∉ ball z (10 * r) →
    ∀ u : ℝ, 0 < u → pinchPointEvent (μ ω) (D ω) U T Q' Q M r z →
    z ∈ frontier (lqgMetricBall (D ω) 0 u) →
    rescaledSet Q' r z ⊆ (lqgMetricBall (D ω) 0 u)ᶜ ∧
      rescaledSet T r z ⊆ lqgMetricBall (D ω) 0 u

/-- Proposition 11.11 at the exponent specified by `dγ`, retaining all centers
and all radii of the metric ball. -/
def CorrectedHarmonicBallNotMetricBallStmt (dγ : ℝ → ℝ) : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → 0 < dγ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    IsLQGMetricOfField P γ (γ / dγ γ) α₀ hC D →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) 0) →
  ∀ᵐ ω ∂P, ∀ᵐ t ∂volume, 0 < t → ∀ (w : ℂ) (s : ℝ),
    Λ ω t ≠ lqgMetricBall (D ω) w s

/-- The frozen geometric consequence implies the corrected successor. -/
theorem correctedPinchMetricBallConsequence_of_frozen (dγ : ℝ → ℝ)
    (h : PinchEventMetricBallConsequenceStmt.{u}) : CorrectedPinchMetricBallConsequenceStmt.{u} dγ := by
  intro U V W T Q' Q ε hc γ α₀ hγ hγ₂ hα _ Ω _ P hC hcirc μ D hg hm hd
  exact h U T Q' Q hc.toIsPinchPointProofConfiguration.toIsPinchPointConfiguration
    γ α₀ (γ / dγ γ) hγ hγ₂ hα Ω P hC hcirc μ D hg hm hd

/-- The frozen proposition implies its physical-exponent successor. -/
theorem correctedHarmonicBallNotMetricBall_of_frozen (dγ : ℝ → ℝ)
    (h : HarmonicBallNotMetricBallStmt.{u}) : CorrectedHarmonicBallNotMetricBallStmt.{u} dγ := by
  intro γ α₀ hγ hγ₂ hα _ Ω _ P hC hcirc μ D hg hm hd
  exact h γ α₀ (γ / dγ γ) hγ hγ₂ hα Ω P hC hcirc μ D hg hm hd

#print axioms correctedPinchMetricBallConsequence_of_frozen
#print axioms correctedHarmonicBallNotMetricBall_of_frozen

end HarmonicBalls
