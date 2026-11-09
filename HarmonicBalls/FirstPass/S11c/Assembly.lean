import HarmonicBalls.Proofs.Sec11.MassDiameterClassSelection
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Proposition 11.10, probabilistic core of the class choice (fp-S11c, owner n1)

FIRST-PASS NEW. Deterministic-in-form bookkeeping of the paper's proof of `lemma:mass-diam` (corrected lines
3046-3110): the four parity classes of the level-`N` cells of `S₁` (`exists_positive_measure_four_tile_class`,
reused from `Proofs/Sec11/MassDiameterClassSelection.lean`) and an almost-sure set `G` whose complement has small
probability (the exterior bound of the second Weyl shift). Given the positive-probability class event, some class `i`
and some measurable `G` satisfy `0 < P(X_i ∩ G)`, where `X_i` is the class event intersected with the pieces event.
-/

namespace HarmonicBalls

open MeasureTheory
open scoped ENNReal

theorem exists_class_and_good_set {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsFiniteMeasure P] (μ : Ω → Measure X) (Q : Set Ω) (S : Set X) (C : Fin 4 → Set X)
    (c : ℝ≥0∞) (hcover : S ⊆ ⋃ i, C i) (hp : 0 < P {ω | ω ∈ Q ∧ 8 * c < μ ω S})
    (hG : ∀ _i : Fin 4, ∀ η : ℝ≥0∞, 0 < η → ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ ≤ η) :
    ∃ i : Fin 4, ∃ G : Set Ω, MeasurableSet G ∧ 0 < P ({ω | ω ∈ Q ∧ 2 * c < μ ω (C i)} ∩ G) := by
  obtain ⟨i, hi⟩ := exists_positive_measure_four_tile_class P μ Q S C c hcover hp
  have hXpos : 0 < P {ω | ω ∈ Q ∧ 2 * c < μ ω (C i)} := hi
  obtain ⟨G, hGm, hGc⟩ := hG i (P {ω | ω ∈ Q ∧ 2 * c < μ ω (C i)} / 2)
    (ENNReal.div_pos_iff.2 ⟨hXpos.ne', ENNReal.ofNat_ne_top⟩)
  refine ⟨i, G, hGm, ?_⟩
  have hsub : {ω | ω ∈ Q ∧ 2 * c < μ ω (C i)} ⊆
      ({ω | ω ∈ Q ∧ 2 * c < μ ω (C i)} ∩ G) ∪ Gᶜ := by
    intro ω hω
    by_cases h : ω ∈ G
    · exact Or.inl ⟨hω, h⟩
    · exact Or.inr h
  have hle : P {ω | ω ∈ Q ∧ 2 * c < μ ω (C i)} ≤
      P ({ω | ω ∈ Q ∧ 2 * c < μ ω (C i)} ∩ G) + P Gᶜ :=
    (measure_mono hsub).trans (measure_union_le _ _)
  rcases eq_or_ne (P ({ω | ω ∈ Q ∧ 2 * c < μ ω (C i)} ∩ G)) 0 with h0 | h0
  · exfalso
    rw [h0, zero_add] at hle
    have h1 := hle.trans hGc
    exact absurd h1 (not_le.2 (ENNReal.half_lt_self hXpos.ne' (measure_ne_top P _)))
  · exact pos_iff_ne_zero.2 h0

end HarmonicBalls
