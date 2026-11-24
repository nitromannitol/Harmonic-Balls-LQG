import HarmonicBalls.FirstPass.Phase2.WeylExponentOfDG20
import HarmonicBalls.FirstPass.Canonical.Stmts

/-!
# The every-`ξ` and canonical-exponent forms of Theorem 1.2, Proposition 11.11 and Lemma 11.13

The metric clauses of Theorem 1.2, Proposition 11.11 and the corrected Lemma 11.13 are stated for
an LQG metric `D` with any Weyl exponent `ξ` (`HarmonicBallNoveltyStmt`,
`HarmonicBallNotMetricBallStmt`, `CorrectedLemma11_13Stmt`), and in canonical copies for the
exponent `ξ = lqgXi γ = γ / d_γ` only (`HarmonicBallNoveltyCanonicalStmt`,
`HarmonicBallNotMetricBallCanonicalStmt`, `CorrectedLemma11_13CanonicalStmt`).

Every γ-LQG metric has Weyl exponent `γ / d_γ` (`xi_eq_xiGamma_derived`, `lqgXi_eq_xiGamma_derived`),
so the hypothesis `IsLQGMetricOfField P γ ξ α₀ hC D` forces `ξ = lqgXi γ`
(`xi_eq_lqgXi_of_isLQGMetricOfField`). Hence the every-`ξ` and canonical forms of Theorem 1.2 and of
Proposition 11.11 are equivalent, and the every-`ξ` corrected Lemma 11.13 implies its canonical form
(the canonical form chooses the density after the model, so it is weaker) and the printed form
`ManyPinchScalesStmt` (`manyPinchScales_derived`, with no hypothesis).
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- **The Weyl exponent of an LQG metric of the field is the canonical one.** -/
theorem xi_eq_lqgXi_of_isLQGMetricOfField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ ξ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {D : Ω → ℂ → ℂ → ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) : ξ = lqgXi γ := by
  obtain ⟨𝔇, h𝔇, -⟩ := hD
  rw [xi_eq_xiGamma_derived γ ξ hγ hγ2 𝔇 h𝔇, lqgXi_eq_xiGamma_derived γ hγ hγ2]

/-- **Proposition 11.11: the every-`ξ` and canonical-exponent forms are equivalent.** -/
theorem harmonicBallNotMetricBallStmt_iff_canonical :
    HarmonicBallNotMetricBallStmt.{u} ↔ HarmonicBallNotMetricBallCanonicalStmt.{u} := by
  constructor
  · intro h γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ D hG hμ hD Λ hΛ
    exact h γ α₀ (lqgXi γ) hγ hγ2 hα Ω P hC hcirc μ D hG hμ hD Λ hΛ
  · intro h γ α₀ ξ hγ hγ2 hα Ω _ P hC hcirc μ D hG hμ hD Λ hΛ
    obtain rfl := xi_eq_lqgXi_of_isLQGMetricOfField hγ hγ2 hD
    exact h γ α₀ hγ hγ2 hα Ω P hC hcirc μ D hG hμ hD Λ hΛ

/-- **Theorem 1.2: the every-`ξ` and canonical-exponent forms are equivalent.** -/
theorem harmonicBallNoveltyStmt_iff_canonical :
    HarmonicBallNoveltyStmt.{u} ↔ HarmonicBallNoveltyCanonicalStmt.{u} := by
  constructor
  · intro h γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hG hμ Λ hΛ
    obtain ⟨h1, h2⟩ := h γ α₀ hγ hγ2 hα Ω P hC hcirc μ hG hμ Λ hΛ
    exact ⟨h1, fun D hD => h2 (lqgXi γ) D hD⟩
  · intro h γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hG hμ Λ hΛ
    obtain ⟨h1, h2⟩ := h γ α₀ hγ hγ2 hα Ω P hC hcirc μ hG hμ Λ hΛ
    refine ⟨h1, fun ξ D hD => ?_⟩
    obtain rfl := xi_eq_lqgXi_of_isLQGMetricOfField hγ hγ2 hD
    exact h2 D hD

/-- **Lemma 11.13 (corrected): the every-`ξ` form implies the canonical-exponent form.** -/
theorem correctedLemma11_13Canonical_of_corrected (h : CorrectedLemma11_13Stmt.{u}) :
    CorrectedLemma11_13CanonicalStmt.{u} := by
  intro U V W T Q' Q δ₀ hgeo γ α₀ hγ hγ2 hα M hM Ω _ P hC hcirc μ D hG hμ hD
  obtain ⟨δ, hδ, hall⟩ := h U V W T Q' Q δ₀ hgeo γ α₀ (lqgXi γ) hγ hγ2 hα M hM
  exact ⟨δ, hδ, hall Ω P hC hcirc μ D hG hμ hD⟩

/-- **Lemma 11.13 in the printed form**, with no hypothesis: `ManyPinchScalesStmt` from the
every-`ξ` corrected Lemma 11.13. -/
theorem manyPinchScales_derived : ManyPinchScalesStmt.{u} :=
  Closure.manyPinchScales_of_corrected correctedLemma11_13_forallXi_derived

end HarmonicBalls
