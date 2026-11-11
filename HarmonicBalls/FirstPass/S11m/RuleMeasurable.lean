import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Countable almost-sure transfer to a distribution-measurable set (step (e) of z4)

Step (e) of the local certificate for Lemma 11.12: a metric event is almost surely the event that a countable
family of metric quantities lies in a measurable set, and each quantity is almost surely a measurable function of the
field. Intersecting the countably many almost-sure identities gives one measurable set of fields, which is the form
`MetricEventCertificateStmt` (`FirstPass/S11ab.lean`) asks for.

This file proves only the abstract countable step. The endpoint-continuity reduction of suprema and infima over
countable dense sets (K1-F4 section 2.4) is a separate step.
-/

namespace HarmonicBalls.S11m.RuleMeasurable

open MeasureTheory Set

/-- Countable almost-sure transfer. Let `g i` be measurable functions of the field `x = hC ω` and let `q i ω` agree
almost surely with `g i (hC ω)`, for countably many `i`. For a measurable set `S` of families of values, the set
`B = {x | (g i x)_i ∈ S}` is measurable and `hC ω ∈ B` holds almost surely exactly when `(q i ω)_i ∈ S`. -/
theorem exists_measurableSet_ae_iff_countable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Type*} [MeasurableSpace X] {ι : Type*} [Countable ι] {β : Type*} [MeasurableSpace β]
    (hC : Ω → X) (g : ι → X → β) (hg : ∀ i, Measurable (g i)) (q : ι → Ω → β)
    (hq : ∀ i, ∀ᵐ ω ∂P, g i (hC ω) = q i ω) (S : Set (ι → β)) (hS : MeasurableSet S) :
    ∃ B : Set X, MeasurableSet B ∧ ∀ᵐ ω ∂P, hC ω ∈ B ↔ (fun i => q i ω) ∈ S := by
  have hmeas : Measurable (fun x i => g i x) := Measurable.of_eval fun i => hg i
  refine ⟨(fun x i => g i x) ⁻¹' S, hmeas hS, ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ i, g i (hC ω) = q i ω := ae_all_iff.2 hq
  filter_upwards [hall] with ω hω
  show (fun i => g i (hC ω)) ∈ S ↔ (fun i => q i ω) ∈ S
  rw [funext hω]

end HarmonicBalls.S11m.RuleMeasurable
