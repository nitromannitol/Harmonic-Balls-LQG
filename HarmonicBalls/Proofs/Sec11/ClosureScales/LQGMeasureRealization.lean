import HarmonicBalls.Proofs.Sec11.ClosureScales.LQGProfileMeasureAE
import HarmonicBalls.Proofs.Sec11.ClosureScales.UniversalCircleLaw

/-!
# The measure part of the universal realization

Source: universal realization of the supplied data. The measure part asserts a common law `λ` for the coded circle averages and a Borel map
`m_{γ,α}` on the canonical space, such that on every probability space in any universe satisfying `IsWholePlaneGFF`
and `IsLQGMeasureOfField`, the coded circle averages have law `λ` and the LQG measure is `m_{γ,α}` of them almost surely.

Here `λ` is the law `ν` of the restriction to `J = (0,∞) × ℂ` of the canonical profile (`UniversalCircleLaw.lean`), and
`m_{γ,α}` is the Riesz measure `profileMeasure γ α₀` of the canonical profile (`LQGProfileMeasureAE.lean`, with its
measurability from `LQGProfileMeasurable.lean`). The statement covers every universe `u₁` of the probability space `Ω`.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology

universe u₁

/-- **The measure part of the universal realization**. There are a
probability measure `ν` on the restricted circle averages and a Borel map `m` on the canonical profiles, such that every
whole-plane GFF `(P, hC, hcirc)` in any universe `u₁`, with LQG measure `μ` and any measurable canonical profile `c`
agreeing with the circle averages on `J` almost surely, satisfies `P.map (circleProfileOnJ ∘ c) = ν` and
`μ ω = m (c ω)` for almost every `ω`. -/
theorem exists_universal_lqgMeasure_realization (γ α₀ : ℝ) :
    ∃ (ν : Measure (↥circleIndexSet → ℝ)) (m : CanonicalProfile → Measure ℂ),
      IsProbabilityMeasure ν ∧ Measurable m ∧
      ∀ (Ω : Type u₁) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
        (c : Ω → CanonicalProfile),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ → Measurable c →
        (∀ᵐ ω ∂P, ∀ p ∈ circleIndexSet, (c ω).1 p = hcirc ω p.1 p.2) →
        P.map (fun ω => circleProfileOnJ (c ω)) = ν ∧ ∀ᵐ ω ∂P, μ ω = m (c ω) := by
  obtain ⟨ν, hν, hlaw⟩ := exists_universal_circleProfileLaw.{u₁}
  refine ⟨ν, profileMeasure γ α₀, hν, measurable_profileMeasure γ α₀, ?_⟩
  intro Ω _ P _ hC hcirc μ c hh hμ hc hcJ
  exact ⟨hlaw Ω P hC hcirc c hh hc hcJ, profileMeasure_ae_eq hμ hcJ⟩

end HarmonicBalls
