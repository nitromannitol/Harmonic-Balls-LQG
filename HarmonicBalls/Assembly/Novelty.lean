import HarmonicBalls.Draft.Section10
import HarmonicBalls.Draft.Section11

/-!
# Conditional assembly of the novelty of harmonic balls

Proposition 10.7 quantifies over families simultaneously at all centres, whereas
Theorem 1.2 supplies a family only at zero. Theorem 1.1 supplies the existence
needed to extend the latter to a family at all centres on one almost-sure event.
-/

namespace HarmonicBalls

open MeasureTheory Set

universe u

/-- Extend a family at zero to all centres when families exist simultaneously
at all centres almost surely. No measurability of the family is required. -/
theorem exists_harmonicBallFamily_extension
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (Λ : Ω → ℝ → Set ℂ)
    (hΛ : ∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) 0)
    (hex : ∀ᵐ ω ∂P, ∀ z : ℂ, ∃ L : ℝ → Set ℂ, IsHarmonicBallFamily (μ ω) L z) :
    ∃ L : Ω → ℂ → ℝ → Set ℂ,
      (∀ ω, L ω 0 = Λ ω) ∧
      ∀ᵐ ω ∂P, ∀ z : ℂ, IsHarmonicBallFamily (μ ω) (L ω z) z := by
  classical
  let L : Ω → ℂ → ℝ → Set ℂ := fun ω z =>
    if z = 0 then Λ ω
    else if h : ∃ F : ℝ → Set ℂ, IsHarmonicBallFamily (μ ω) F z then Classical.choose h
    else fun _ => ∅
  refine ⟨L, ?_, ?_⟩
  · intro ω
    simp only [L, ite_eq_left rfl]
  · filter_upwards [hΛ, hex] with ω hzero hall
    intro z
    by_cases hz : z = 0
    · subst z
      simpa only [L, ite_eq_left rfl] using hzero
    · have h : ∃ F : ℝ → Set ℂ, IsHarmonicBallFamily (μ ω) F z := hall z
      simpa only [L, ite_eq_right hz, dite_eq_left h] using Classical.choose_spec h

/-- Theorem 1.2 follows from Theorem 1.1 and Propositions 10.7, 11.2 and
11.11. This is a conditional assembly; it does not prove those results. -/
theorem harmonicBallNoveltyStmt_of_existence_and_results
    (hex : ExistenceUniquenessHarmonicBallsStmt.{u})
    (hjordan : HarmonicBallComplementBoundaryJordanStmt.{u})
    (hlip : HarmonicBallNotLipschitzStmt.{u})
    (hmetric : HarmonicBallNotMetricBallStmt.{u}) : HarmonicBallNoveltyStmt.{u} := by
  intro γ α₀ hγ hγ₂ hα Ω _ P hC hcirc μ hgff hμ Λ hΛ
  have hex' : ∀ᵐ ω ∂P, ∀ z : ℂ, ∃ L : ℝ → Set ℂ,
      IsHarmonicBallFamily (μ ω) L z := by
    filter_upwards [hex γ α₀ hγ hγ₂ hα Ω P hC hcirc μ hgff hμ] with ω hω
    intro z
    obtain ⟨L, hL, _⟩ := hω z
    exact ⟨L, hL⟩
  obtain ⟨L, hLzero, hL⟩ := exists_harmonicBallFamily_extension P μ Λ hΛ hex'
  have hj := hjordan γ α₀ hγ hγ₂ hα Ω P hC hcirc μ hgff hμ L hL
  have hn := hlip γ α₀ hγ hγ₂ hα Ω P hC hcirc μ hgff hμ Λ hΛ
  constructor
  · filter_upwards [hn, hj] with ω hnω hjω
    refine ⟨hnω, ?_⟩
    intro t ht C hCmem
    rw [← hLzero ω] at hCmem
    exact hjω t ht 0 C hCmem
  · intro ξ D hD
    exact hmetric γ α₀ ξ hγ hγ₂ hα Ω P hC hcirc μ D hgff hμ hD Λ hΛ

#print axioms exists_harmonicBallFamily_extension
#print axioms harmonicBallNoveltyStmt_of_existence_and_results

end HarmonicBalls
