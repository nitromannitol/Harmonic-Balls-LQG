import HarmonicBalls.Draft.Section9
import HarmonicBalls.Draft.Section2

/-!
# Lemma 9.4: regular open sets which agree `μ_h`-almost everywhere are equal

Reduction of `RegularOpenEqOfAEEqStmt` (Lemma 9.4, lemma:regular-open-ae, line 2394 of
paper/lqg_harmonic_ball-corrected.tex) to a deterministic step and the full support of the LQG measure (input I1,
`LQGMeasureFullSupportStmt` of `HarmonicBalls/Draft/Section2.lean`), following the proof at lines 2399-2409.

## Steps

* `RegularOpenEqOfOpenPosMeasure` (deterministic): if `μ` charges every nonempty open set (`IsOpenPosMeasure`), two
  regular open sets `X, Y` with `μ(X \ Y) = μ(Y \ X) = 0` are equal. The open set `X \ closure Y ⊆ X \ Y` is
  `μ`-null, hence empty, so `X ⊆ closure Y` and, `X` being open, `X ⊆ int(closure Y) = Y`; symmetrically `Y ⊆ X`.
* I1 (`LQGMeasureFullSupportStmt`, explicit hypothesis of `regularOpenEqOfAEEq_of_steps`): almost surely `μ_h`
  charges every nonempty open set.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- Step of Lemma 9.4 (lines 2399-2409): for a measure charging every nonempty open set, regular open sets which
agree up to null sets are equal. -/
def RegularOpenEqOfOpenPosMeasure : Prop :=
  ∀ μ : Measure ℂ, μ.IsOpenPosMeasure → ∀ X Y : Set ℂ, IsRegularOpen X → IsRegularOpen Y →
    μ (X \ Y) = 0 → μ (Y \ X) = 0 → X = Y

/-- Reduction of Lemma 9.4 (`RegularOpenEqOfAEEqStmt`) to the deterministic step and input I1
(`LQGMeasureFullSupportStmt`). -/
theorem regularOpenEqOfAEEq_of_steps (hdet : RegularOpenEqOfOpenPosMeasure)
    (hI1 : LQGMeasureFullSupportStmt.{u}) : RegularOpenEqOfAEEqStmt.{u} := by
  intro γ α₀ hγ hγ2 hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hI1 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hω X Y _ _ hX hY hXY hYX
  exact hdet (μ ω) ⟨fun U hU hne => (hω U hU hne).ne'⟩ X Y hX hY hXY hYX

end HarmonicBalls
