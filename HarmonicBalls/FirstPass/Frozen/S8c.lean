import HarmonicBalls.FirstPass.S8c.LocalObservation

/-! # FIRST-PASS frozen external input for Lemma 8.2 (worker n4, fp-S8c-8-2-local)

One EXTERNAL Prop, the local joint field-measure identification of the rooted comparison in Lemma 8.2
(`lemma:mu_h-doubling-and-harnack`, corrected paper, lines 2151-2220, and [C1] near the origin). It is stated
about the whole-plane GFF `P, hC, hcirc` and its LQG measures only (`μ` of insertion `α₀`, `ν` of insertion `γ`,
and the no-insertion measure `lam`). It mentions no cluster, odometer, harmonic ball or IDLA process.
Its objects are the Draft predicates `IsWholePlaneGFF` and `IsLQGMeasureOfField` and the displayed maps of
`FirstPass/S8c/LocalObservation.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- FIRST-PASS FROZEN. Local joint field-measure identification for Lemma 8.2 (local form, ball about `z`
avoiding `0`, normalised restricted measures). The root law is the normalised restriction `λ|B_1(0) / λ(B_1(0))`
of the no-insertion LQG measure `λ` of the whole-plane GFF, and the statement is domination of its observation
(`localRootObservation μ j`, recentred restriction of the `α₀`-measure `μ` at the root) by the reference
observation (`localReferenceObservation ν j`, `γ`-insertion measure `ν` on `B_{r_j}(0)`, with root `z` Lebesgue
distributed on `localDomain j` and independent of the field).
Source: Duplantier, Miller, Sheffield, arXiv:1409.7055v4, Lemma A.10, p. 184 (whole-plane paragraph, marked
sampling description), local joint form: locator pending (the field marginal is printed; the joint
field-measure form is not). Operator ruling 2026-11-09 17:45 UTC; displayed form in
`docs/campaign/audits/LocalRootedComparisonRepair.md`, section "Actual local observation".
Used by: firstPass_8_2 (through the local reduction in `FirstPass/S8c/`). -/
def LocalRootedFieldMeasureDomination : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ ν lam : Ω → Measure ℂ),
    ∀ hGFF : IsWholePlaneGFF P hC hcirc, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMeasureOfField P γ γ hcirc ν →
    ∀ hlam : IsLQGMeasureOfField P γ 0 hcirc lam, ∀ j : ℕ, 1 ≤ j →
      ((P ⊗ₘ localRootKernel P lam (hGFF.aemeasurable_lqgMeasure hlam)).restrict
          (Prod.snd ⁻¹' localDomain j)).map (localRootObservation μ j) ≪
        ((volume.restrict (localDomain j)).prod P).map (localReferenceObservation ν j)

end HarmonicBalls
