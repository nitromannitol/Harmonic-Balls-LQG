import HarmonicBalls.FirstPass.Canonical.Stmts
import HarmonicBalls.Assembly.Novelty
import HarmonicBalls.FirstPass.S1S10

/-!
# Canonical-exponent copies of the novelty assembly and of Theorem 1.2

Copies of `harmonicBallNoveltyStmt_of_existence_and_results` (`HarmonicBalls/Assembly/Novelty.lean:46`) and of `firstPass_1_2`
(`HarmonicBalls/FirstPass/S1S10.lean:43`) for the canonical statements of `FirstPass/Canonical/Stmts.lean` (Correction 1, `ξ := lqgXi γ`): the metric hypothesis is `HarmonicBallNotMetricBallCanonicalStmt` and the conclusion is
`HarmonicBallNoveltyCanonicalStmt`. The proofs are the originals with the universal quantifier over `ξ` removed; every
other hypothesis is unchanged. `exists_harmonicBallFamily_extension` is reused from `Assembly/Novelty.lean`. -/

namespace HarmonicBalls

open MeasureTheory Set

universe u

/-- Theorem 1.2 at the canonical exponent `ξ = lqgXi γ`, assembled from Theorem 1.1, Propositions
10.7 and 11.2, and Proposition 11.11 at the canonical exponent (`hmetric`). Copy of
`harmonicBallNoveltyStmt_of_existence_and_results` (`Assembly/Novelty.lean:46`). This is a conditional assembly. -/
theorem harmonicBallNoveltyStmt_of_existence_and_results_canonical
    (hex : ExistenceUniquenessHarmonicBallsStmt.{u})
    (hjordan : HarmonicBallComplementBoundaryJordanStmt.{u})
    (hlip : HarmonicBallNotLipschitzStmt.{u})
    (hmetric : HarmonicBallNotMetricBallCanonicalStmt.{u}) : HarmonicBallNoveltyCanonicalStmt.{u} := by
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
  · intro D hD
    exact hmetric γ α₀ hγ hγ₂ hα Ω P hC hcirc μ D hgff hμ hD Λ hΛ

/-- Theorem 1.2 at the canonical exponent `ξ = lqgXi γ` (`theorem:harmonic-balls-properties`). The Jordan clause is Proposition 10.7 and the non-Lipschitz clause is Proposition 11.2; the metric-ball clause
is the canonical Proposition 11.11, taken as the hypothesis `hmetric`. Copy of `firstPass_1_2` (`FirstPass/S1S10.lean:43`). -/
theorem firstPass_1_2_canonical
    (h55 : ExistenceHarmonicBallsStmt.{u}) (h56 : UniquenessHarmonicBallsStmt.{u})
    (hjordan : HarmonicBallComplementBoundaryJordanStmt.{u})
    (hlip : HarmonicBallNotLipschitzStmt.{u})
    (hmetric : HarmonicBallNotMetricBallCanonicalStmt.{u}) :
    HarmonicBallNoveltyCanonicalStmt.{u} :=
  harmonicBallNoveltyStmt_of_existence_and_results_canonical (firstPass_1_1 h55 h56) hjordan hlip hmetric

end HarmonicBalls
