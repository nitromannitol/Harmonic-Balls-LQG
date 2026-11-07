import LatticeProb.Prob.Birkhoff
import HarmonicBalls.Proofs.Sec8.JointGoodScaleMean
import HarmonicBalls.Proofs.Sec8.AEGermTriviality

/-! # Pointwise ergodic theorem for good-scale frequencies

The Birkhoff theorem used here is from Leonardo Bonanno's LatticeProb
formalization, `LatticeProb.Prob.Birkhoff`.
-/

open MeasureTheory Filter
open scoped Topology

namespace HarmonicBalls

open Classical in
/-- The stationary good-scale estimate, with the pointwise ergodic theorem
provided by LatticeProb. The germ, stationarity, and one-scale estimate remain
explicit hypotheses. -/
theorem ae_eventually_veryGoodComparableScaleCount_of_stationary_and_small_failure_birkhoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (X : ℕ → Ω → ℝ) (ζ ε : ℝ)
    (germ : ℝ → MeasurableSpace Ω) (hgle : ∀ r, 0 < r → germ r ≤ mΩ)
    (hXgerm : ∀ r, 0 < r → ∃ K, ∀ n, K ≤ n →
      @Measurable Ω ℝ (germ r) _ (X n))
    (htrivial : ∀ A : Set Ω, (∀ r, 0 < r → MeasurableSet[germ r] A) →
      P A = 0 ∨ P A = 1)
    (hX : ∀ n ω, X n ω = if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) z N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n z m then 1 else 0)
    (hXm : ∀ n, Measurable (X n))
    (hstat : P.map (fun ω n => X (n + 1) ω) = P.map (fun ω n => X n ω))
    (hε : 0 ≤ ε) (hεζ : ε < ζ)
    (hfail : P {ω | ¬ (IsVeryGoodAnnulus (μ ω) βminus (dyadicScale 0) z N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) 0 z m)} ≤ ENNReal.ofReal ε) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      veryGoodComparableScaleCount (μ ω) βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N := by
  exact ae_eventually_veryGoodComparableScaleCount_of_stationary_and_small_failure P μ βminus z N₀
    a b C₁m C₁p C₂m C₂p C₃ m X ζ ε germ hgle hXgerm htrivial hX hXm
    (pointwiseBirkhoff_of_latticeProb _ _ _) hstat hε hεζ hfail

open Classical in
/-- The version with almost-surely local indicators also uses LatticeProb's
pointwise ergodic theorem directly. -/
theorem ae_eventually_veryGoodComparableScaleCount_of_stationary_ae_local_birkhoff
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (X : ℕ → Ω → ℝ) (q ζ : ℝ)
    (germ : ℝ → MeasurableSpace Ω) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hcofinal : ∀ ε, 0 < ε → ∃ n, r n ≤ ε)
    (hrmono : Antitone r) (hgmono : Monotone germ)
    (hlocal : ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → X n =ᵐ[P] Y n))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1)
    (hX : ∀ n ω, X n ω = if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) z N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n z m then 1 else 0)
    (hXm : ∀ n, Measurable (X n))
    (hstat : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω))
    (hmean : ∀ n, ∫ ω, X n ω ∂P = q) (hq : 1 - ζ < q) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      veryGoodComparableScaleCount (μ ω) βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N := by
  exact ae_eventually_veryGoodComparableScaleCount_of_stationary_ae_local P μ βminus z N₀
    a b C₁m C₁p C₂m C₂p C₃ m X q ζ germ r hr hcofinal hrmono hgmono hlocal htrivial hX hXm
    (pointwiseBirkhoff_of_latticeProb _ _ _) hstat hmean hq

end HarmonicBalls
