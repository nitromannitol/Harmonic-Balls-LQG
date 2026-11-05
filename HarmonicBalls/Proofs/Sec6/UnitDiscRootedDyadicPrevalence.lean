import HarmonicBalls.Proofs.Sec6.UnitDiscRootedPolynomialTail
import HarmonicBalls.Proofs.Sec6.PathwiseScaleUniformAnnuli
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Dyadic annulus counts under unit-disc LQG sampling

The countable-centre iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- A unit-disc LQG root almost surely has the stated lower bound on its
seven-adic good-annulus count eventually along dyadic windows. The threshold
is fixed before the physical scale is chosen. -/
theorem exists_ae_unitDisc_root_eventually_dyadic_goodAnnuli_count
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ, 0 < s →
      ∀ᵐ p ∂(P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const),
      ∀ᶠ n : ℕ in atTop,
        (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2 a (b + 1)}.ncard : ℝ) := by
  obtain ⟨a, ha, ht⟩ := exists_unitDisc_lqg_root_goodAnnuli_polynomial_tail
    hgrowth hγ hγ2 h hμ hb 1 β (by norm_num) hβ
  refine ⟨a, ha, ?_⟩
  intro s hs
  obtain ⟨C, hC, htail⟩ := ht s hs
  let Q := P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
    (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const
  let F : ℕ → Set (Ω × ℂ) := fun n => {p |
    ({r : ℝ | r ∈ Icc (dyadicScale (n + 48)) ((dyadicScale (n + 48)) ^ (3 / 4 : ℝ)) ∧
      (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
      IsGoodAnnulus (μ p.1) (s * r) p.2 a (b + 1)}.ncard : ℝ) <
    (β / 16) * Real.logb 7 ((dyadicScale (n + 48)) ^ (-1 : ℝ))}
  have hbound (n : ℕ) : Q (F n) ≤ ENNReal.ofReal C * (1 / 2 : ℝ≥0∞) ^ n := by
    have hscale : dyadicScale (n + 48) ≤ (2 : ℝ)⁻¹ ^ n := by
      unfold dyadicScale
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right n 48)
    have hh := htail (dyadicScale (n + 48)) (dyadicScale_pos _) (by
      unfold dyadicScale
      exact pow_le_one₀ (by norm_num) (by norm_num))
      (sixteen_le_logb_dyadic_inverse (by omega : 48 ≤ n + 48))
    calc
      Q (F n) ≤ ENNReal.ofReal (C * dyadicScale (n + 48)) := by simpa only [Real.rpow_one] using hh
      _ ≤ ENNReal.ofReal (C * ((2 : ℝ)⁻¹ ^ n)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hscale hC.le)
      _ = _ := by rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2⁻¹)]; rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]; norm_num
  have hsum : (∑' n, Q (F n)) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hbound)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num)
  have hae := ae_eventually_notMem hsum
  filter_upwards [hae] with p hp
  have hp' : ∀ᶠ n : ℕ in atTop, p ∉ F n := hp
  rw [Filter.eventually_atTop] at hp' ⊢
  obtain ⟨N, hN⟩ := hp'
  refine ⟨N + 48, ?_⟩
  intro n hn
  have hbad := hN (n - 48) (by omega)
  have heq : n - 48 + 48 = n := by omega
  simpa only [F, mem_ofPred_eq, not_lt, heq] using hbad

/-- The same threshold works almost surely at every scale in a prescribed
countable family of positive physical scales. -/
theorem exists_ae_unitDisc_root_eventually_dyadic_goodAnnuli_count_all_scales
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      ∀ᵐ p ∂(P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const),
      ∀ i, ∀ᶠ n : ℕ in atTop,
        (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus (μ p.1) (s i * r) p.2 a (b + 1)}.ncard : ℝ) := by
  obtain ⟨a, ha, ht⟩ := exists_ae_unitDisc_root_eventually_dyadic_goodAnnuli_count
    hgrowth hγ hγ2 h hμ hb β hβ
  exact ⟨a, ha, ae_all_iff.mpr (fun i => ht (s i) (hs i))⟩

end HarmonicBalls.Section6
