import HarmonicBalls.Draft.Section11Corrected
import HarmonicBalls.Draft.Section6
import HarmonicBalls.Proofs.Sec11.InternalPinchFrequency
import HarmonicBalls.Steps.Sec11.PinchDyadicWindowShift

/-! # The corrected pinch block-density reduction

The marked-root and dilation arguments must establish the named typical-point
block-density property below. It is a proof obligation, not a literature input.
The only staged literature hypothesis used in the reduction is the metric-field
proposition, which remains subject to source review.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Finset
open scoped ENNReal Topology BigOperators

universe u

/-- The local, additive-constant-invariant certificate in the corrected
positive-probability proof. It certifies the original pinch event; no
identification with the stronger internal event is asserted. -/
def CorrectedLocalPinchCertificate {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (μ : Ω → Measure ℂ)
    (D : Ω → ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M : ℝ) : Prop :=
  ∃ E : Set Ω, MeasurableSet[Section6.fieldSigmaAlgebraModConst α hC (ball 0 7)] E ∧
    0 < P E ∧ E ⊆ {ω | pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0}

/-- The local certificate supplies a measurable inner witness for the
original event. -/
theorem correctedLocalPinchCertificate_innerWitness
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M : ℝ)
    (hgff : IsWholePlaneGFF P hC hcirc)
    (h : CorrectedLocalPinchCertificate P α hC μ D U T Q' Q M) :
    ∃ E ⊆ {ω | pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0}, MeasurableSet E ∧ 0 < P E := by
  obtain ⟨E, hE, hpos, hsub⟩ := h
  exact ⟨E, hsub,
    (Section6.fieldSigmaAlgebraModConst_le α hC _ |>.trans (hgff.fieldSigmaAlgebra_le α _)) E hE,
    hpos⟩

/-- Block density for the internal-metric pinch event at one point. -/
def InternalPinchBlockDensity (μ : Measure ℂ) (D : ℂ → ℂ → ℝ)
    (U T Q' Q : Set ℂ) (M q : ℝ) (z : ℂ) : Prop :=
  ∀ᶠ N : ℕ in atTop, q * N ≤
    ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
      pinchPointEventWithInternalBounds μ D U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ)

/-- The typical-point block-density obligation for one fixed geometry. The
rate is deterministic and is chosen before the probability space. -/
def CorrectedInternalPinchBlockDensityStmt (dγ : ℝ → ℝ) (U T Q' Q : Set ℂ) : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ → 0 < dγ γ →
  ∀ M : ℝ, 0 < M → ∃ q : ℝ, 0 < q ∧
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    IsLQGMetricOfField P γ (γ / dγ γ) α₀ hC D →
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), InternalPinchBlockDensity (μ ω) (D ω) U T Q' Q M q z

/-- On a Euclidean length metric, internal pinch block density implies the
same rate for the original pinch event. -/
theorem pinchBlockDensity_of_internal (μ : Measure ℂ) (D : ℂ → ℂ → ℝ)
    (U T Q' Q : Set ℂ) (M q : ℝ) (z : ℂ) (hD : IsEuclideanLengthMetric D)
    (h : InternalPinchBlockDensity μ D U T Q' Q M q z) :
    PinchBlockDensity μ D U T Q' Q M q z :=
  eventually_pinchPointEvent_block_ncard_of_internalBounds hD h

/-- Shifting the indices of an arbitrary event by a fixed `k` preserves any
strictly smaller eventual block-density bound. -/
theorem eventually_shifted_index_block_density
    (S : Set ℕ) [DecidablePred (· ∈ S)] (k : ℕ) {q q' : ℝ} (hqq : q' < q)
    (h : ∀ᶠ N : ℕ in atTop,
      q * N ≤ (((Finset.Icc (N + 1) (2 * N)).filter (· ∈ S)).card : ℝ)) :
    ∀ᶠ N : ℕ in atTop,
      q' * N ≤ (((Finset.Icc (N + 1) (2 * N)).filter (fun n => n + k ∈ S)).card : ℝ) := by
  filter_upwards [eventually_pinch_window_shift_density S k hqq h] with N hN
  let A := (Finset.Icc (N + 1) (2 * N)).filter (fun n => n + k ∈ S)
  let B := (Finset.Icc (N + k + 1) (2 * N + k)).filter (· ∈ S)
  have heq : A.image (fun n => n + k) = B := by
    ext x
    simp only [A, B, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨n, ⟨⟨hn1, hn2⟩, hnS⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, hnS⟩
    · rintro ⟨⟨hx1, hx2⟩, hxS⟩
      refine ⟨x - k, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      simpa only [Nat.sub_add_cancel (by omega : k ≤ x)] using hxS
  have hc : A.card = B.card := by
    rw [← heq, Finset.card_image_of_injective _ (fun _ _ h => Nat.add_right_cancel h)]
  change q' * N ≤ (A.card : ℝ)
  rw [hc]
  exact hN

/-- An eventual implication from the shifted source events to target events
transfers any strictly smaller block-density rate. This is the counting step
for a dyadic recentering once the corresponding event comparison is proved. -/
theorem eventually_block_density_of_shifted_event_implication
    (S T : Set ℕ) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (k : ℕ) {q q' : ℝ} (hqq : q' < q)
    (h : ∀ᶠ N : ℕ in atTop,
      q * N ≤ (((Finset.Icc (N + 1) (2 * N)).filter (· ∈ S)).card : ℝ))
    (hST : ∀ᶠ n : ℕ in atTop, n + k ∈ S → n ∈ T) :
    ∀ᶠ N : ℕ in atTop,
      q' * N ≤ (((Finset.Icc (N + 1) (2 * N)).filter (· ∈ T)).card : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hST
  filter_upwards [eventually_shifted_index_block_density S k hqq h,
    Filter.eventually_ge_atTop N₀] with N hN hbound
  have hsub : (Finset.Icc (N + 1) (2 * N)).filter (fun n => n + k ∈ S) ⊆
      (Finset.Icc (N + 1) (2 * N)).filter (· ∈ T) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hN₀ n (by omega) hn.2⟩
  exact hN.trans (by exact_mod_cast Finset.card_le_card hsub)

/-- The corrected Lemma 11.13 follows from the typical-point internal block
density at a fixed corrected geometry and the staged metric-field axiom. -/
theorem correctedManyPinchScales_of_internalBlockDensity
    (dγ : ℝ → ℝ) (U V W T Q' Q : Set ℂ) (ε : ℝ)
    (hconfig : IsCorrectedPinchConfiguration U V W T Q' Q ε)
    (hfreq : CorrectedInternalPinchBlockDensityStmt.{u} dγ U T Q' Q)
    (hmetric : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMetricFieldAxioms P γ (γ / dγ γ) α₀ hC hcirc) :
    CorrectedManyPinchScalesStmt.{u} dγ := by
  refine ⟨U, V, W, T, Q', Q, ε, hconfig, ?_⟩
  intro γ α₀ hγ hγ2 hα hd M hM
  obtain ⟨q, hq, hfreq⟩ := hfreq γ α₀ hγ hγ2 hα hd M hM
  let δ : ℝ := min q (1 / 2)
  have hδ : δ ∈ Ioo (0 : ℝ) 1 := by
    dsimp [δ]
    constructor
    · exact lt_min hq (by norm_num)
    · have := min_le_right q (1 / 2 : ℝ)
      linarith
  have hδq : δ ≤ q := min_le_left _ _
  refine ⟨δ, hδ, ?_⟩
  intro Ω _ P hC hcirc μ D hGFF hμ hD
  filter_upwards [hfreq Ω P hC hcirc μ D hGFF hμ hD,
    ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ (γ / dγ γ) α₀ hC hcirc D
      (hmetric Ω P γ α₀ hC hcirc) hGFF hγ hγ2 hα hD] with ω hfreqω hDω
  filter_upwards [hfreqω] with z hz
  have h := pinchBlockDensity_of_internal (μ ω) (D ω) U T Q' Q M q z hDω hz
  filter_upwards [h] with N hN
  exact (mul_le_mul_of_nonneg_right hδq (Nat.cast_nonneg N)).trans hN

#print axioms pinchBlockDensity_of_internal
#print axioms correctedLocalPinchCertificate_innerWitness
#print axioms eventually_shifted_index_block_density
#print axioms eventually_block_density_of_shifted_event_implication
#print axioms correctedManyPinchScales_of_internalBlockDensity

end HarmonicBalls
