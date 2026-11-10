import HarmonicBalls.FirstPass.Closure
import HarmonicBalls.Defs.LQGGraphDistance

/-!
# Faithful form of Theorem 1.2 (canonical Weyl exponent, positive radii)

Owner: z3 (task fp-closure-1-2-faithful). File `HarmonicBalls/FirstPass/Closure/Faithful12.lean`, namespace
`HarmonicBalls.Closure`.

The counted statement `HarmonicBallNoveltyStmt` (`Draft/Section1.lean:124`) states the LQG-metric clause for every Weyl
exponent `ξ`, every realized metric `D` and every real radius `s`. The printed Theorem 1.2 (`theorem:harmonic-balls-properties`,
`paper/lqg_harmonic_ball-corrected.tex:174`) concerns the γ-LQG metric `D_h` with the canonical exponent `ξ = γ / d_γ`
(eq:xi, `paper/lqg_harmonic_ball-corrected.tex:444`, in the Fact on the LQG metric) and balls of positive radius
(operator note 08:24 UTC, `notes/fp-gaps/CHATGPT-hb-main-1-1-1-3-PRO.md` l.153-172).

`HarmonicBallNoveltyFaithfulStmt` is that restriction. It is implied by `HarmonicBallNoveltyStmt`
(`harmonicBallNoveltyFaithful_of_stmt`), so the counted result is not weakened.

The exponent `d_γ` is the repository's `lqgGraphDimension γ` (`Defs/LQGGraphDistance.lean:105`), the Ding-Gwynne exponent
(arXiv:1807.01072, Theorem 1.4, eq. (1.8)) that the repository's `IsLQGMetric` documentation identifies with the Hausdorff
dimension of `(ℂ, D_h)` (`Defs/LQGMetric.lean:170-172`). The value of `lqgGraphDimension γ` is characterized only under the
PROPOSED input `WholePlaneLQGGraphDimension` (`Proposed/LQGDimension.lean`); without a witness it returns the default `1`.
The faithful statement and its proof do not use that input, but its match with the printed `ξ = γ / d_γ` relies on it.

Table row for `closure_1_2_faithful`: the module table of `Closure.lean` ("1.2 faithful").
-/

namespace HarmonicBalls.Closure

universe u

open MeasureTheory Set

/-- **Faithful form of Theorem 1.2** (`theorem:harmonic-balls-properties`, `paper/lqg_harmonic_ball-corrected.tex:174`).
Same body as `HarmonicBallNoveltyStmt` (`Draft/Section1.lean:124`), with one change: the LQG-metric clause is stated only for
the canonical Weyl exponent `ξ = γ / d_γ`, `d_γ = lqgGraphDimension γ` (`Defs/LQGGraphDistance.lean:105`; eq:xi, paper line 444),
and only for radii `0 < s`. The Lipschitz clause and the Jordan clause are unchanged. Operator note 08:24 UTC
(`notes/fp-gaps/CHATGPT-hb-main-1-1-1-3-PRO.md` l.153-172). -/
def HarmonicBallNoveltyFaithfulStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ Λ : Ω → ℝ → Set ℂ, (∀ᵐ ω ∂P, IsHarmonicBallFamily (μ ω) (Λ ω) 0) →
  (∀ᵐ ω ∂P,
    (∀ᵐ t ∂volume, 0 < t → ¬ IsLipschitzDomain (Λ ω t)) ∧
    ∀ t : ℝ, 0 < t → ∀ C ∈ connectedComponentsIn (closure (Λ ω t))ᶜ, IsSimpleLoop (frontier C)) ∧
  ∀ D : Ω → ℂ → ℂ → ℝ, IsLQGMetricOfField P γ (γ / lqgGraphDimension γ) α₀ hC D →
    ∀ᵐ ω ∂P, ∀ᵐ t ∂volume, 0 < t → ∀ (w : ℂ) (s : ℝ), 0 < s → Λ ω t ≠ lqgMetricBall (D ω) w s

/-- Restriction: `HarmonicBallNoveltyStmt` specialised to the Weyl exponent `ξ = γ / lqgGraphDimension γ`, with the radii
restricted to `0 < s`. The non-metric clauses are reused as they are. -/
theorem harmonicBallNoveltyFaithful_of_stmt (h : HarmonicBallNoveltyStmt.{u}) :
    HarmonicBallNoveltyFaithfulStmt.{u} := by
  intro γ α₀ hγ0 hγ2 hα Ω inst P hC hcirc μ hW hμ Λ hΛ
  obtain ⟨hA, hB⟩ := h γ α₀ hγ0 hγ2 hα Ω P hC hcirc μ hW hμ Λ hΛ
  refine ⟨hA, fun D hD => ?_⟩
  filter_upwards [hB (γ / lqgGraphDimension γ) D hD] with ω hω
  filter_upwards [hω] with t ht
  intro ht0 w s _
  exact ht ht0 w s

/-- **Closure of the faithful Theorem 1.2** (`HarmonicBallNoveltyFaithfulStmt`): the hypotheses of `closure_1_2`
(`Closure.lean`, unchanged), with the conclusion restricted by `harmonicBallNoveltyFaithful_of_stmt`. -/
theorem closure_1_2_faithful
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0})
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    (hDecFrozen : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hDec : LocalLQGDecoderCommonFrozen.{u})
    (hCM : CameronMartinLocallyLipschitzShiftAbsCont.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hStep8 : Step8IdentificationStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen) :
    HarmonicBallNoveltyFaithfulStmt.{u} :=
  harmonicBallNoveltyFaithful_of_stmt.{u}
    (closure_1_2 hDG hAff hCC hW hE hN hL1 hWeyl hE1 hE3 hB hCamp hDecFrozen hDec hCM hAx hStep8 hTor)

end HarmonicBalls.Closure
