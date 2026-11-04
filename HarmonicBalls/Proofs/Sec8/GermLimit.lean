import HarmonicBalls.Proofs.Sec8.GermTriviality
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Germ measurability of limiting frequencies

An everywhere-defined limit representative is independent of approximations
whose difference tends to zero. This permits the removal of finitely many
large scales before taking the limiting frequency.
-/

open Filter MeasureTheory Finset
open scoped Topology BigOperators

namespace HarmonicBalls

/-- Two real sequences with vanishing difference have the same `limUnder`,
including when neither sequence converges. -/
theorem limUnder_eq_of_sub_tendsto_zero (f g : ℕ → ℝ)
    (h : Tendsto (fun n => f n - g n) atTop (𝓝 0)) :
    limUnder atTop f = limUnder atTop g := by
  have hfg : ∀ c, Tendsto f atTop (𝓝 c) ↔ Tendsto g atTop (𝓝 c) := by
    intro c
    constructor
    · intro hf
      have hh := hf.sub h
      simpa only [sub_zero, sub_sub_cancel] using hh
    · intro hg
      have hh := hg.add h
      simpa only [add_zero, add_sub_cancel] using hh
  by_cases hc : ∃ c, Tendsto f atTop (𝓝 c)
  · obtain ⟨c, hc⟩ := hc
    rw [hc.limUnder_eq, ((hfg c).1 hc).limUnder_eq]
  · have hg : ¬ ∃ c, Tendsto g atTop (𝓝 c) := by
      rintro ⟨c, hc'⟩
      exact hc ⟨c, (hfg c).2 hc'⟩
    rw [limUnder_of_not_tendsto hc, limUnder_of_not_tendsto hg]

/-- If each scale admits measurable approximants with vanishing pointwise
error, the canonical limit representative is measurable in every scale germ. -/
theorem germ_measurable_limUnder_of_approximants {Ω : Type*}
    (germ : ℝ → MeasurableSpace Ω) (F : ℕ → Ω → ℝ)
    (happrox : ∀ ε, 0 < ε → ∃ G : ℕ → Ω → ℝ,
      (∀ n, @Measurable Ω ℝ (germ ε) _ (G n)) ∧
      ∀ ω, Tendsto (fun n => F n ω - G n ω) atTop (𝓝 0)) :
    ∀ ε, 0 < ε → @Measurable Ω ℝ (germ ε) _ (fun ω => limUnder atTop (fun n => F n ω)) := by
  intro ε hε
  obtain ⟨G, hG, hclose⟩ := happrox ε hε
  let : MeasurableSpace Ω := germ ε
  have hm : Measurable (fun ω => limUnder atTop (fun n => G n ω)) :=
    (StronglyMeasurable.limUnder (fun n => (hG n).stronglyMeasurable)).measurable
  convert hm using 1
  funext ω
  exact limUnder_eq_of_sub_tendsto_zero _ _ (hclose ω)

/-- Removing finitely many terms changes an initial average by a quantity
that tends to zero, without requiring any bound on the terms. -/
theorem initialScaleAverage_sub_tendsto_zero_of_tail_eq (x y : ℕ → ℝ) (K : ℕ)
    (hxy : ∀ n, K ≤ n → x n = y n) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, x n) / (N : ℝ) -
      (∑ n ∈ Icc 1 N, y n) / (N : ℝ)) atTop (𝓝 0) := by
  have heq : ∀ᶠ N : ℕ in atTop,
      (∑ n ∈ Icc 1 N, x n) / (N : ℝ) -
        (∑ n ∈ Icc 1 N, y n) / (N : ℝ) =
        (∑ n ∈ Icc 1 K, (x n - y n)) / (N : ℝ) := by
    filter_upwards [eventually_ge_atTop K] with N hN
    rw [← sub_div, ← Finset.sum_sub_distrib]
    congr 1
    symm
    apply Finset.sum_subset
    · intro n hn
      simp only [mem_Icc] at hn ⊢
      exact ⟨hn.1, hn.2.trans hN⟩
    · intro n hn hnnot
      have hnN := mem_Icc.mp hn
      have hnK : K ≤ n := by
        have : ¬ n ≤ K := by
          intro h
          exact hnnot (mem_Icc.mpr ⟨hnN.1, h⟩)
        omega
      rw [hxy n hnK, sub_self]
  exact (tendsto_const_div_atTop_nhds_zero_nat _).congr' (heq.mono fun _ h => h.symm)

/-- If each sufficiently small-scale indicator is measurable in the germ at
any given radius, the canonical limiting initial frequency is germ measurable. -/
theorem germ_measurable_initialScaleFrequency {Ω : Type*}
    (germ : ℝ → MeasurableSpace Ω) (X : ℕ → Ω → ℝ)
    (hX : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (X n)) :
    ∀ ε, 0 < ε → @Measurable Ω ℝ (germ ε) _
      (fun ω => limUnder atTop (fun N : ℕ => (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ))) := by
  apply germ_measurable_limUnder_of_approximants
  intro ε hε
  obtain ⟨K, hK⟩ := hX ε hε
  let : MeasurableSpace Ω := germ ε
  let Y : ℕ → Ω → ℝ := fun n ω => if K ≤ n then X n ω else 0
  refine ⟨fun N ω => (∑ n ∈ Icc 1 N, Y n ω) / (N : ℝ), ?_, ?_⟩
  · intro N
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro n hn
    by_cases hkn : K ≤ n
    · simpa [Y, hkn] using hK n hkn
    · simp [Y, hkn]
  · intro ω
    apply initialScaleAverage_sub_tendsto_zero_of_tail_eq _ _ K
    intro n hn
    simp [Y, hn]

open Classical in
/-- Eventual measurability of the one-scale indicators supplies the germ
measurability needed for the good-scale block-frequency conclusion. -/
theorem ae_eventually_veryGoodComparableScaleCount_of_eventual_germ_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (X : ℕ → Ω → ℝ) (L : Ω → ℝ) (q ζ : ℝ)
    (germ : ℝ → MeasurableSpace Ω) (hgle : ∀ ε, 0 < ε → germ ε ≤ mΩ)
    (hXgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      @Measurable Ω ℝ (germ ε) _ (X n))
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
  let L' : Ω → ℝ := fun ω => limUnder atTop
    (fun N : ℕ => (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ))
  have hL' : ∀ ε, 0 < ε → @Measurable Ω ℝ (germ ε) _ L' :=
    germ_measurable_initialScaleFrequency germ X hXgerm
  have hlim' : ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ))
      atTop (𝓝 (L' ω)) := by
    filter_upwards [hlim] with ω hω
    rw [show L' ω = L ω from hω.limUnder_eq]
    exact hω
  exact ae_eventually_veryGoodComparableScaleCount_of_trivial_germ P μ βminus z N₀
    a b C₁m C₁p C₂m C₂p C₃ m X L' q ζ germ hgle hL' htrivial hX hXm hlim' hmean hq

end HarmonicBalls
