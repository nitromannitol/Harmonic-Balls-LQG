import HarmonicBalls.Draft.Section11

/-!
# Section 11 faithful forms of Lemmas 11.15-11.17

The Draft statements `PinchFirstEventPositiveStmt`, `PinchSecondEventPositiveStmt` and `PinchThirdEventPositiveStmt`
(`Draft/Section11.lean:289-320`) fix the insertion to `0` and quantify existentially over the geometry. The fidelity
review requires the
corrected forms below:

* every insertion `α₀ < lqgQ γ` (the corrected context `h^α = g - α log|·|`, `α < Q`; corrected paper lines 3236-3238,
  correction `[C43]`), and
* every fixed buffered geometry `IsBufferedPinchGeometry` (corrected paper lines 3157-3201, correction `[C42]`, with the
  buffer conditions of eq:buffers and `δ < 10⁻³`).

The events are the paper's `Ẽ₁`, `Ẽ₂(M)`, `Ẽ₃` (corrected paper lines 3326-3343), i.e. the Draft events
`pinchFirstEvent`, `pinchSecondEvent`, `pinchThirdEvent`, unchanged. The Draft statements are not edited and are not
counted.

Not part of `IsBufferedPinchGeometry`: the component `Ω` of `B₇ \ (closure (B_{2δ}(Q)) ∪ closure (B_{2δ}(W)))` containing
`0` (corrected paper lines 3189-3201). It is a construction of the proof. The paper asserts its properties as consequences
of the buffer and connectivity conditions, so they are not hypotheses here.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter
open scoped ENNReal

universe u

/-- The fixed buffered keyhole geometry of the corrected paper (`[C42]`, corrected paper lines 3157-3201): concentric
open disks `U ⋐ V ⋐ W` in `𝔸_{1,2}`, `W̄ ⊆ T`, `T` bounded, connected and open with `T̄ ⊆ 𝔸_{1,6}`, `T ⊆ 𝔸_{1,5}`,
`∂B₅ ⊆ T̄`; bounded connected open `Q' ⋐ Q` with `Q̄ ⊆ 𝔸_{4,5} \ T̄`; a deterministic `δ ∈ (0, 10⁻³)` with the six buffer
conditions of eq:buffers (paper lines 3184-3189). -/
structure IsBufferedPinchGeometry (U V W T Q' Q : Set ℂ) (δ : ℝ) : Prop where
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  isOpen_W : IsOpen W
  isOpen_T : IsOpen T
  isOpen_Q' : IsOpen Q'
  isOpen_Q : IsOpen Q
  isConnected_T : IsConnected T
  isConnected_Q' : IsConnected Q'
  isConnected_Q : IsConnected Q
  concentric : ∃ (c : ℂ) (ρU ρV ρW : ℝ), U = ball c ρU ∧ V = ball c ρV ∧ W = ball c ρW
  /-- `U` is an open disk of positive radius (corrected paper line 3238), so it is nonempty. Given `concentric`,
  this is `0 < ρU`. Without it `PinchSecondEventFaithfulStmt` and `PinchThirdEventFaithfulStmt` are false for `U = ∅`
. -/
  U_nonempty : U.Nonempty
  U_subset : U ⊆ annulus 0 1 2
  V_subset : V ⊆ annulus 0 1 2
  W_subset : W ⊆ annulus 0 1 2
  closure_W_subset_T : closure W ⊆ T
  T_subset : T ⊆ annulus 0 1 5
  closure_T_subset : closure T ⊆ annulus 0 1 6
  sphere_subset_closure_T : sphere (0 : ℂ) 5 ⊆ closure T
  closure_Q'_subset_Q : closure Q' ⊆ Q
  closure_Q_subset : closure Q ⊆ annulus 0 4 5 \ closure T
  delta_pos : 0 < δ
  delta_lt : δ < 1 / 1000
  buffer_T : closure (thickening (10 * δ) (closure T)) ⊆ annulus 0 1 6
  buffer_U : closure (thickening (10 * δ) (closure U)) ⊆ V
  buffer_V : closure (thickening (10 * δ) (closure V)) ⊆ W
  buffer_W : closure (thickening (10 * δ) (closure W)) ⊆ T ∩ annulus 0 1 2
  buffer_Q' : closure (thickening (10 * δ) (closure Q')) ⊆ Q
  buffer_Q : closure (thickening (10 * δ) (closure Q)) ⊆ annulus 0 4 5 \ thickening (10 * δ) (closure T)

/-- Lemma 11.15, corrected form (`lemma:first-event-proof`, corrected paper lines 3347-3349): for every fixed buffered
geometry, every `γ ∈ (0, 2)`, every `α₀ < Q`, and every LQG metric of the field, `P[Ẽ₁] > 0` (inner-measure form). -/
def PinchFirstEventFaithfulStmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
  ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α₀ hC D →
  ∃ A ⊆ {ω | pinchFirstEvent (D ω) W T Q' Q δ}, MeasurableSet A ∧ 0 < P A

/-- Lemma 11.16, corrected form (`lemma:second-event-proof`, corrected paper lines 3351-3353): for every fixed buffered
geometry, every `γ ∈ (0, 2)`, every `α₀ < Q`, and every `M > 0`, `P[Ẽ₁ ∩ Ẽ₂(M)] > 0` (inner-measure form). -/
def PinchSecondEventFaithfulStmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
  ∀ γ α₀ ξ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ M : ℝ, 0 < M →
    ∃ A ⊆ {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧ pinchSecondEvent (μ ω) (D ω) U V δ M},
      MeasurableSet A ∧ 0 < P A

/-- Lemma 11.17, corrected form (`lemma:third-event-proof`, corrected paper lines 3355-3357): for every fixed buffered
geometry, every `γ ∈ (0, 2)`, every `α₀ < Q`, and every `M > 0`, `P[Ẽ₁ ∩ Ẽ₂(M) ∩ Ẽ₃] > 0` (inner-measure form).
The Weyl exponent is the canonical one, `ξ = γ / d_γ` (eq:xi, corrected paper line 440; GM21 (1.5)), with `d_γ > 0`
a parameter: the paper claims the lemma for this exponent only.
The parameter `d_γ` enters only through the exponent `γ / d_γ > 0`, so the hypothesis `IsLQGMetricOfField` is the
metric of the paper exactly when `d_γ` is the true dimension constant. -/
def PinchThirdEventFaithfulStmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ →
  ∀ γ α₀ dγ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → 0 < dγ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ (γ / dγ) α₀ hC D →
  ∀ M : ℝ, 0 < M →
    ∃ A ⊆ {ω | pinchFirstEvent (D ω) W T Q' Q δ ∧ pinchSecondEvent (μ ω) (D ω) U V δ M ∧
      pinchThirdEvent (D ω) V W δ}, MeasurableSet A ∧ 0 < P A


end HarmonicBalls
