import HarmonicBalls.Proofs.Sec8.StationaryGoodScales
import Mathlib.Probability.IdentDistrib

/-!
# One-scale means of stationary processes

Stationarity of the joint sequence law implies equality of all one-scale
laws and hence equality of their expectations.
-/

open MeasureTheory Filter Finset ProbabilityTheory
open scoped Topology BigOperators

namespace HarmonicBalls

/-- In a stationary sequence, consecutive coordinates have the same law. -/
theorem identDistrib_succ_of_stationary {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n))
    (hstat : P.map (fun ω n => X (n + 1) ω) = P.map (fun ω n => X n ω))
    (n : ℕ) : IdentDistrib (X (n + 1)) (X n) P P := by
  have hpath : Measurable (fun ω n => X n ω) := Measurable.of_eval hXm
  have hshift : Measurable (fun ω n => X (n + 1) ω) :=
    Measurable.of_eval (fun n => hXm (n + 1))
  have hid : IdentDistrib (fun ω n => X (n + 1) ω) (fun ω n => X n ω) P P :=
    ⟨hshift.aemeasurable, hpath.aemeasurable, hstat⟩
  exact hid.comp (measurable_pi_apply n)

/-- Every coordinate of a stationary sequence has the same expectation. -/
theorem integral_eq_first_of_stationary {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n))
    (hstat : P.map (fun ω n => X (n + 1) ω) = P.map (fun ω n => X n ω))
    (n : ℕ) : ∫ ω, X n ω ∂P = ∫ ω, X 0 ω ∂P := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (identDistrib_succ_of_stationary P X hXm hstat n).integral_eq.trans ih

open Classical in
/-- The expectation of a measurable indicator is the probability of its
underlying event, including when event measurability is known only through
the indicator. -/
theorem integral_eq_measure_of_indicator {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Set Ω) (X : Ω → ℝ) (hXm : Measurable X)
    (hX : ∀ ω, X ω = if ω ∈ A then 1 else 0) :
    ∫ ω, X ω ∂P = (P A).toReal := by
  have hA : A = X ⁻¹' {1} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hX]
    split_ifs <;> simp_all
  have hm : MeasurableSet A := by
    rw [hA]
    exact hXm (measurableSet_singleton 1)
  have heq : X = A.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    rw [hX]
    simp only [Set.indicator_apply]
  rw [heq]
  change (∫ ω, A.indicator (1 : Ω → ℝ) ω ∂P) = (P A).toReal
  rw [integral_indicator_one hm, measureReal_def]

open Classical in
/-- The stationary good-scale estimate needs only the first indicator mean;
stationarity supplies the means at all other scales. -/
theorem ae_eventually_veryGoodComparableScaleCount_of_stationary_first_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (X : ℕ → Ω → ℝ) (ζ : ℝ)
    (germ : ℝ → MeasurableSpace Ω) (hgle : ∀ ε, 0 < ε → germ ε ≤ mΩ)
    (hXgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      @Measurable Ω ℝ (germ ε) _ (X n))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1)
    (hX : ∀ n ω, X n ω = if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) z N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n z m then 1 else 0)
    (hXm : ∀ n, Measurable (X n))
    (hBirkhoff : PointwiseBirkhoff (P.map (fun ω n => X (n + 1) ω))
      (fun x n => x (n + 1)) (fun x => x 0))
    (hstat : P.map (fun ω n => X (n + 1) ω) = P.map (fun ω n => X n ω))
    (hq : 1 - ζ < ∫ ω, X 0 ω ∂P) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      veryGoodComparableScaleCount (μ ω) βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N := by
  have hstat' : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω) := by
    let shift : (ℕ → ℝ) → (ℕ → ℝ) := fun x n => x (n + 1)
    have hs : Measurable shift := measurable_sequence_shift
    have hp : Measurable (fun ω n => X n ω) := Measurable.of_eval hXm
    have hp' : Measurable (fun ω n => X (n + 1) ω) :=
      Measurable.of_eval (fun n => hXm (n + 1))
    have hm := congrArg (Measure.map shift) hstat
    rw [Measure.map_map hs hp', Measure.map_map hs hp] at hm
    simpa [shift, Function.comp_def, Nat.add_assoc] using hm
  exact ae_eventually_veryGoodComparableScaleCount_of_stationary P μ βminus z N₀
    a b C₁m C₁p C₂m C₂p C₃ m X (∫ ω, X 0 ω ∂P) ζ germ hgle hXgerm htrivial
    hX hXm hBirkhoff hstat' (integral_eq_first_of_stationary P X hXm hstat) hq

end HarmonicBalls
