import Mathlib
import HarmonicBalls.LPStage.GFF
import HarmonicBalls.LPStage.LQGMeasure

/-! # Measurability of the γ-LQG mass of a closed set as a functional of the field (LP stage, z7)

LP form of the statement `LQGMassFunctionalMeasurableFrozen` (`HarmonicBalls/FirstPass/Frozen/S11d.lean:155`):
same binders, quantifiers and conclusion, stated for the LP-stage definitions of `HarmonicBalls/LPStage/GFF.lean`
(`IsWholePlaneGFF`, `addFunPairing`, `distributionMeasurableSpace`, `LatticeProb.Gauss`) and
`HarmonicBalls/LPStage/LQGMeasure.lean` (`lqgQ`, `IsLQGMeasureOfField`, `LatticeProb.LQG`).

Terminology: whole-plane Gaussian free field and its circle averages (Berestycki-Powell; Duplantier-Sheffield 2011),
γ-LQG area measure as the vague limit of regularized measures along powers of two (Duplantier-Sheffield 2011,
Proposition 1.1). The statement uses no Harmonic-balls object.

Status: this file holds the statement only. The proof is not yet staged (see the z7 report): it needs the a.s.
convergence of the explicit circle approximants `HarmonicBalls/FirstPass/S11at/Producers.lean:992`, whose
closure is not yet in the LP stage.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

universe u

open LatticeProb.Gauss LatticeProb.LQG

namespace LatticeProb.LQG.MassFunctionalDerived

/-- The LP form of `LQGMassFunctionalMeasurableFrozen` (`FirstPass/Frozen/S11d.lean:155`). For a whole-plane GFF
`hC` with circle averages `hcirc` and a γ-LQG measure `μ` of `h^ℂ - α₀ log|·|` (`IsLQGMeasureOfField`), and a closed
set `S`, there is a `distributionMeasurableSpace`-measurable functional `F` on distributions such that
`F (h^ℂ + f) = μ(S)` almost surely, for every continuous `f` vanishing on `S`. Intended for `0 < γ < 2` and
`α₀ < lqgQ γ`; the hypotheses are the ones of the HB frozen statement. -/
def LQGMassFunctionalMeasurableLP : Prop :=
  ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ S : Set ℂ, IsClosed S → ∃ F : ((ℂ → ℝ) → ℝ) → ℝ≥0∞, Measurable[distributionMeasurableSpace] F ∧
      ∀ f : ℂ → ℝ, Continuous f → (∀ x ∈ S, f x = 0) →
        ∀ᵐ ω ∂P, F (addFunPairing (hC ω) f) = μ ω S

end LatticeProb.LQG.MassFunctionalDerived

end
