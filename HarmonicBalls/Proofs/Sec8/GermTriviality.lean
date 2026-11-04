import HarmonicBalls.Proofs.Sec8.FrequencyMoments
import Mathlib.MeasureTheory.Measure.Typeclasses.ZeroOne

/-!
# Measurable limits and trivial germs

A real random variable measurable with respect to a trivial germ is almost
surely constant. This is the measure-theoretic step used after the ergodic
theorem in the proof of Lemma 8.3.
-/

open MeasureTheory Set Filter Finset
open scoped Topology BigOperators

namespace HarmonicBalls

/-- A real-valued random variable whose law assigns only zero or one to
measurable sets is almost surely constant. -/
theorem ae_eq_const_of_zero_one_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (L : Ω → ℝ) (hL : Measurable L)
    (hzeroone : ∀ A : Set ℝ, MeasurableSet A → P (L ⁻¹' A) = 0 ∨ P (L ⁻¹' A) = 1) :
    ∃ c : ℝ, ∀ᵐ ω ∂P, L ω = c := by
  let Q := P.map L
  have : IsZeroOneMeasure Q := ⟨by
    intro A hA
    rw [show Q A = P (L ⁻¹' A) from Measure.map_apply hL hA]
    exact hzeroone A hA⟩
  obtain ⟨c, hc⟩ := IsZeroOneMeasure.exists_eq_dirac (μ := Q)
  refine ⟨c, ?_⟩
  have hc_ae : ∀ᵐ y ∂P.map L, y = c := by
    rw [show P.map L = Measure.dirac c from hc]
    exact (ae_dirac_iff (measurableSet_singleton c)).2 rfl
  exact ae_of_ae_map hL.aemeasurable hc_ae

/-- A real random variable measurable for every positive scale of a trivial
germ is almost surely constant. -/
theorem ae_eq_const_of_trivial_germ {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (germ : ℝ → MeasurableSpace Ω)
    (hgle : ∀ ε, 0 < ε → germ ε ≤ mΩ) (L : Ω → ℝ)
    (hL : ∀ ε, 0 < ε → @Measurable Ω ℝ (germ ε) _ L)
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1) :
    ∃ c : ℝ, ∀ᵐ ω ∂P, L ω = c := by
  have hm : Measurable L := (hL 1 (by norm_num)).mono (hgle 1 (by norm_num)) le_rfl
  apply ae_eq_const_of_zero_one_law P L hm
  intro A hA
  apply htrivial
  intro ε hε
  exact (hL ε hε) hA

open Classical in
/-- Triviality of a germ, together with measurability of the limiting good
scale frequency in that germ, gives the block-frequency conclusion. -/
theorem ae_eventually_veryGoodComparableScaleCount_of_trivial_germ
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (X : ℕ → Ω → ℝ) (L : Ω → ℝ) (q ζ : ℝ)
    (germ : ℝ → MeasurableSpace Ω) (hgle : ∀ ε, 0 < ε → germ ε ≤ mΩ)
    (hL : ∀ ε, 0 < ε → @Measurable Ω ℝ (germ ε) _ L)
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1)
    (hX : ∀ n ω, X n ω = if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) z N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n z m then 1 else 0)
    (hXm : ∀ n, Measurable (X n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ))
      atTop (𝓝 (L ω)))
    (hmean : ∀ n, ∫ ω, X n ω ∂P = q) (hq : 1 - ζ < q) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      veryGoodComparableScaleCount (μ ω) βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m N := by
  obtain ⟨c, hc⟩ := ae_eq_const_of_trivial_germ P germ hgle L hL htrivial
  have hlim' : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ))
      atTop (𝓝 c) := by
    filter_upwards [hlim, hc] with ω hω heq
    simpa only [heq] using hω
  exact ae_eventually_veryGoodComparableScaleCount_of_indicator_limit P μ βminus z N₀
    a b C₁m C₁p C₂m C₂p C₃ m X c q ζ hX hXm hlim' hmean hq

end HarmonicBalls
