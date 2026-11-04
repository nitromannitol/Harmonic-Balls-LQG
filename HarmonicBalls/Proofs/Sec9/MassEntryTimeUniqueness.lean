import HarmonicBalls.Proofs.Sec9.MassEntryTime

/-! # Uniqueness of mass entry times

Equal-mass comparison at rational masses identifies the entry times and all
left rational envelopes outside a single spatial null set for each pair of
families. No existence of a family or pointwise uniqueness of balls is asserted.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Equal membership in all positive rational sections gives equal entry times. -/
theorem massEntryTime_eq_of_rational_sections (A B : ℝ → Set ℂ) (x : ℂ)
    (h : ∀ q : ℚ, 0 < (q : ℝ) → (x ∈ A q ↔ x ∈ B q)) :
    massEntryTime A x = massEntryTime B x := by
  unfold massEntryTime
  congr 1
  funext q
  rw [propext (h q.val q.property)]

universe u

/-- Any two bounded same-centre families parametrized by mass have the same
entry time almost everywhere. Consequently all their positive-time left
rational envelopes agree outside the same spatial null set, which may depend
on the two families. -/
theorem ae_massParametrized_subharmonicBall_entry_time_unique
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A B : ℝ → Set ℂ) (z : ℂ),
      (∀ t : ℝ, 0 < t → Bornology.IsBounded (A t) ∧
        IsSubharmonicBall (μ ω) (A t) z ∧ μ ω (A t) = ENNReal.ofReal t) →
      (∀ t : ℝ, 0 < t → Bornology.IsBounded (B t) ∧
        IsSubharmonicBall (μ ω) (B t) z ∧ μ ω (B t) = ENNReal.ofReal t) →
      ∀ᵐ x ∂(μ ω), massEntryTime A x = massEntryTime B x ∧
        ∀ t : ℝ, 0 < t →
          (x ∈ leftRationalMassEnvelope A t ↔ x ∈ leftRationalMassEnvelope B t) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_bounded_subharmonicBall_order_by_mass hI2 h82
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω horder
  intro A B z hA hB
  have hsections : ∀ᵐ x ∂(μ ω), ∀ q : ℚ, 0 < (q : ℝ) →
      (x ∈ A q ↔ x ∈ B q) := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : 0 < (q : ℝ)
    · have hab : μ ω (A q \ B q) = 0 := horder (A q) (B q) z
        (hA q hq).1 (hB q hq).1 (hA q hq).2.1 (hB q hq).2.1 (by
          rw [(hA q hq).2.2, (hB q hq).2.2])
      have hba : μ ω (B q \ A q) = 0 := horder (B q) (A q) z
        (hB q hq).1 (hA q hq).1 (hB q hq).2.1 (hA q hq).2.1 (by
          rw [(hB q hq).2.2, (hA q hq).2.2])
      filter_upwards [ae_eq_set.mpr ⟨hab, hba⟩] with x hx _
      exact iff_of_eq hx
    · exact Eventually.of_forall fun _ h => (hq h).elim
  filter_upwards [hsections] with x hx
  have heq := massEntryTime_eq_of_rational_sections A B x hx
  refine ⟨heq, ?_⟩
  intro t ht
  rw [← massEntryTime_lt_iff_mem_leftRationalMassEnvelope A ht x,
    ← massEntryTime_lt_iff_mem_leftRationalMassEnvelope B ht x, heq]

end HarmonicBalls
