import HarmonicBalls.Proofs.Sec6.AnnulusLawTransfer
import HarmonicBalls.Proofs.Sec6.GeometricCounts

/-! # Annulus iteration for geometric radii

This combines the geometric scale count with Leonardo Bonanno's proof of the
Gwynne–Miller annulus iteration lemma, used through the bridge in
`HarmonicBalls.Proofs.Sec6.AnnulusLawTransfer` and the Bonanno modules
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`,
`LatticeProb.Bonanno.LQGMetric.Field.GFFLaw`,
`LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate`, and
`LatticeProb.Bonanno.LQGMetric.Field.ExistGFF`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- Annulus iteration bounds the probability of having too few good geometric
radii in an interval. The stride allows a spaced subsequence of radii; `A`
converts a good-event radius into the radius used by the iteration lemma. -/
theorem annulus_iteration_geometric_count
    (s₁ s₂ α β q A : ℝ) (stride : ℕ)
    (hs₁ : 0 < s₁) (hs₁₂ : s₁ < s₂) (hs₂ : s₂ < 1)
    (hα : 0 < α) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (hq0 : 0 < q) (hq1 : q < 1) (hA : 0 < A)
    (hstride : 0 < stride) (hspacing : q ^ stride ≤ s₁) :
    ∃ p ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ α₀ : ℝ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc →
    ∀ (n₀ : ℕ) (lo hi : ℝ), 0 < lo → ∀ (good : Ω → ℝ → Prop),
      (∀ k : ℕ, IsFieldMeasurableModConst P α₀ hC
        (annulus 0 (s₁ * (A * q ^ (n₀ + stride * k)))
          (s₂ * (A * q ^ (n₀ + stride * k))))
        {ω | good ω (q ^ (n₀ + stride * k))}) →
      (∀ k : ℕ, ENNReal.ofReal p ≤ P {ω | good ω (q ^ (n₀ + stride * k))}) →
    ∀ K : ℕ, (∀ k ∈ Finset.range K, q ^ (n₀ + stride * k) ∈ Icc lo hi) →
      P {ω | ({r : ℝ | r ∈ Icc lo hi ∧ (∃ n : ℕ, r = q ^ n) ∧ good ω r}.ncard : ℝ)
        < β * K} ≤ ENNReal.ofReal (C * Real.exp (-α * K)) := by
  classical
  obtain ⟨p, hp, C, hCpos, hiter⟩ :=
    annulusIterationStmt_proved s₁ s₂ hs₁ hs₁₂ hs₂ α hα β hβ
  refine ⟨p, hp, C, hCpos, ?_⟩
  intro α₀ Ω _ P hC hcirc hgff n₀ lo hi hlo good hlocal hprob K hrange
  let r : ℕ → ℝ := fun k => A * q ^ (n₀ + stride * k)
  let E : ℕ → Set Ω := fun k => {ω | good ω (q ^ (n₀ + stride * k))}
  have hr : ∀ k, 0 < r k := fun k => mul_pos hA (pow_pos hq0 _)
  have hratio : ∀ k, r (k + 1) ≤ s₁ * r k := by
    intro k
    have heq : n₀ + stride * (k + 1) = (n₀ + stride * k) + stride := by
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    dsimp [r]
    rw [heq, pow_add]
    nlinarith [mul_nonneg hA.le (pow_nonneg hq0.le (n₀ + stride * k))]
  have hbound := hiter α₀ Ω P hC hcirc hgff r hr hratio E hlocal hprob K
  apply (measure_mono ?_).trans hbound
  intro ω hω
  have hcount := geometric_scale_count_le hq0 hq1 hlo (good ω) n₀ stride K hstride hrange
  change ({r : ℝ | r ∈ Icc lo hi ∧ (∃ n : ℕ, r = q ^ n) ∧ good ω r}.ncard : ℝ) < β * K at hω
  change (((Finset.range K).filter fun k => good ω (q ^ (n₀ + stride * k))).card : ℝ) < β * K
  exact lt_of_le_of_lt (by exact_mod_cast hcount) hω

/-- The good-annulus radii `7⁻ⁿ` satisfy the spacing hypothesis of annulus
iteration with the annuli `A_{3r,5r}`. The field pairings may be those of a
translated whole-plane GFF, so the good annuli can be centered at any `z`. -/
theorem goodAnnulus_geometric_iteration (α β : ℝ) (hα : 0 < α)
    (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ p ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc →
    ∀ (μ : Ω → Measure ℂ) (z : ℂ) (a b : ℝ) (n₀ : ℕ) (lo hi : ℝ),
      0 < lo →
      (∀ k : ℕ, IsFieldMeasurableModConst P 0 hC
        (annulus 0 (3 * ((7 : ℝ)⁻¹ ^ (n₀ + k))) (5 * ((7 : ℝ)⁻¹ ^ (n₀ + k))))
        {ω | IsGoodAnnulus (μ ω) ((7 : ℝ)⁻¹ ^ (n₀ + k)) z a b}) →
      (∀ k : ℕ, ENNReal.ofReal p ≤
        P {ω | IsGoodAnnulus (μ ω) ((7 : ℝ)⁻¹ ^ (n₀ + k)) z a b}) →
    ∀ K : ℕ, (∀ k ∈ Finset.range K, (7 : ℝ)⁻¹ ^ (n₀ + k) ∈ Icc lo hi) →
      P {ω | ({r : ℝ | r ∈ Icc lo hi ∧ (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
        IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ) < β * K} ≤
        ENNReal.ofReal (C * Real.exp (-α * K)) := by
  classical
  obtain ⟨p, hp, C, hCpos, hiter⟩ :=
    annulus_iteration_geometric_count (3 / 7) (5 / 7) α β (7 : ℝ)⁻¹ 7 1
      (by norm_num) (by norm_num) (by norm_num) hα hβ
      (by norm_num) (by norm_num) (by norm_num) (by omega) (by norm_num)
  refine ⟨p, hp, C, hCpos, ?_⟩
  intro Ω _ P hC hcirc hgff μ z a b n₀ lo hi hlo hlocal hprob K hrange
  apply hiter 0 Ω P hC hcirc hgff n₀ lo hi hlo (fun ω r => IsGoodAnnulus (μ ω) r z a b)
  · intro k
    convert hlocal k using 1 <;> norm_num [mul_assoc]
    congr 1 <;> ring
  · simpa using hprob
  · simpa using hrange

/-- Taking every other `8⁻ⁿ` radius makes the annuli `A_{r/4,2r}` satisfy
annulus iteration, yielding a bound for the full very-good radius count. -/
theorem veryGoodAnnulus_geometric_iteration (α β : ℝ) (hα : 0 < α)
    (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ p ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc →
    ∀ (μ : Ω → Measure ℂ) (z : ℂ) (βminus : ℝ) (N : ℕ)
      (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (n₀ : ℕ) (lo hi : ℝ), 0 < lo →
      (∀ k : ℕ, IsFieldMeasurableModConst P 0 hC
        (annulus 0 (((8 : ℝ)⁻¹ ^ (n₀ + 2 * k)) / 4)
          (2 * ((8 : ℝ)⁻¹ ^ (n₀ + 2 * k))))
        {ω | IsVeryGoodAnnulus (μ ω) βminus ((8 : ℝ)⁻¹ ^ (n₀ + 2 * k)) z N
          a b C₁m C₁p C₂m C₂p C₃}) →
      (∀ k : ℕ, ENNReal.ofReal p ≤ P {ω |
        IsVeryGoodAnnulus (μ ω) βminus ((8 : ℝ)⁻¹ ^ (n₀ + 2 * k)) z N
          a b C₁m C₁p C₂m C₂p C₃}) →
    ∀ K : ℕ, (∀ k ∈ Finset.range K, (8 : ℝ)⁻¹ ^ (n₀ + 2 * k) ∈ Icc lo hi) →
      P {ω | ({r : ℝ | r ∈ Icc lo hi ∧ (∃ n : ℕ, r = (8 : ℝ)⁻¹ ^ n) ∧
        IsVeryGoodAnnulus (μ ω) βminus r z N a b C₁m C₁p C₂m C₂p C₃}.ncard : ℝ)
        < β * K} ≤ ENNReal.ofReal (C * Real.exp (-α * K)) := by
  classical
  obtain ⟨p, hp, C, hCpos, hiter⟩ :=
    annulus_iteration_geometric_count (1 / 32) (1 / 4) α β (8 : ℝ)⁻¹ 8 2
      (by norm_num) (by norm_num) (by norm_num) hα hβ
      (by norm_num) (by norm_num) (by norm_num) (by omega) (by norm_num)
  refine ⟨p, hp, C, hCpos, ?_⟩
  intro Ω _ P hC hcirc hgff μ z βminus N a b C₁m C₁p C₂m C₂p C₃ n₀ lo hi hlo
    hlocal hprob K hrange
  apply hiter 0 Ω P hC hcirc hgff n₀ lo hi hlo
    (fun ω r => IsVeryGoodAnnulus (μ ω) βminus r z N a b C₁m C₁p C₂m C₂p C₃)
  · intro k
    convert hlocal k using 1
    norm_num [mul_assoc]
    congr 1 <;> ring
  · exact hprob
  · exact hrange

end HarmonicBalls.Section6
