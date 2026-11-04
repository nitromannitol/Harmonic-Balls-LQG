import HarmonicBalls.Proofs.Sec6.PrevalenceGridCard
import HarmonicBalls.Proofs.Sec6.GoodAnnulusSubrangeProbability
import HarmonicBalls.Proofs.Sec6.VeryGoodAnnulusSubrangeProbability

/-! # From fixed-center tails to grid prevalence

The fixed-center bounds use Leonardo Bonanno's proof of the Gwynne–Miller
lemma via `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`,
`LatticeProb.Bonanno.LQGMetric.Field.GFFLaw`,
`LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate`, and
`LatticeProb.Bonanno.LQGMetric.Field.ExistGFF`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

/-- A uniform fixed-center polynomial tail with exponent greater than two
survives the union bound over the two-dimensional prevalence grid. -/
theorem polyHighProb_forall_prevalenceGrid_of_fixed_center
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (E : ℝ → ℂ → Set Ω)
    {q C r₀ : ℝ} (hq : 2 < q) (hr₀ : 0 < r₀)
    (htail : ∀ ε : ℝ, 0 < ε → ε < r₀ → ∀ z ∈ prevalenceGrid ε,
      P (E ε z)ᶜ ≤ ENNReal.ofReal (C * ε ^ q)) :
    PolyHighProb P (fun ε => {ω | ∀ z ∈ prevalenceGrid ε, ω ∈ E ε z}) := by
  classical
  refine ⟨q - 2, by linarith, 403 ^ 2 * C, min r₀ 1, lt_min hr₀ zero_lt_one, ?_⟩
  intro ε hε hεr
  have hεr₀ : ε < r₀ := lt_of_lt_of_le hεr (min_le_left _ _)
  have hε1 : ε ≤ 1 := (lt_of_lt_of_le hεr (min_le_right _ _)).le
  have heq : {ω | ∀ z ∈ prevalenceGrid ε, ω ∈ E ε z}ᶜ =
      {ω | ∃ z ∈ prevalenceGrid ε, ω ∈ (E ε z)ᶜ} := by
    ext ω
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall, exists_prop]
  rw [heq]
  calc
    _ ≤ ENNReal.ofReal ((403 / ε) ^ 2) * ENNReal.ofReal (C * ε ^ q) :=
      measure_exists_mem_prevalenceGrid_le P hε hε1 (fun z => (E ε z)ᶜ) _
        (htail ε hε hεr₀)
    _ = ENNReal.ofReal ((403 / ε) ^ 2 * (C * ε ^ q)) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (403 / ε) ^ 2)]
    _ = ENNReal.ofReal (403 ^ 2 * C * ε ^ (q - 2)) := by
      congr 1
      rw [Real.rpow_sub hε, Real.rpow_two]
      field_simp

/-- A fixed logarithmic scale threshold holds for all sufficiently small radii. -/
theorem exists_radius_logb_inverse_ge {b D : ℝ} (hb : 1 < b) :
    ∃ r₀ > 0, ∀ ε : ℝ, 0 < ε → ε < r₀ →
      D ≤ Real.logb b (ε ^ (-1 : ℝ)) := by
  refine ⟨Real.exp (-D * Real.log b), Real.exp_pos _, ?_⟩
  intro ε hε hsmall
  have hlog := Real.log_lt_log hε hsmall
  rw [Real.log_exp] at hlog
  rw [Real.rpow_neg_one, Real.logb, Real.log_inv]
  have hbpos : 0 < Real.log b := Real.log_pos hb
  apply (le_div_iff₀ hbpos).2
  linarith

/-- Uniform locality and one-radius bounds imply good-annulus prevalence.
Each center uses its own recentered whole-plane field; the one-radius lower
bound is the threshold supplied by the annulus iteration. -/
theorem goodAnnulus_prevalence_of_fixed_center :
    ∃ p ∈ Ioo (0 : ℝ) 1,
    ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : ℂ → Ω → (ℂ → ℝ) → ℝ) (hcirc : ℂ → Ω → ℝ → ℂ → ℝ),
      (∀ z : ℂ, IsWholePlaneGFF P (hC z) (hcirc z)) →
    ∀ (μ : Ω → Measure ℂ) (a b : ℝ),
      (∀ z : ℂ, ∀ n : ℕ, IsFieldMeasurableModConst P 0 (hC z)
        (annulus 0 (3 * ((7 : ℝ)⁻¹ ^ n)) (5 * ((7 : ℝ)⁻¹ ^ n)))
        {ω | IsGoodAnnulus (μ ω) ((7 : ℝ)⁻¹ ^ n) z a b}) →
      (∀ z : ℂ, ∀ n : ℕ, ENNReal.ofReal p ≤ P {ω |
        IsGoodAnnulus (μ ω) ((7 : ℝ)⁻¹ ^ n) z a b}) →
      PolyHighProb P (fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
        (1 / 32 : ℝ) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)}) := by
  have hlog : 0 < Real.log 7 := Real.log_pos (by norm_num)
  obtain ⟨p, hp, C, hC, htail⟩ := goodAnnulus_subrange_probability
    (96 * Real.log 7) (1 / 2) (by positivity) (by norm_num)
  refine ⟨p, hp, ?_⟩
  intro Ω _ P hCfield hcirc hgff μ a b hlocal hprob
  obtain ⟨r₀, hr₀, hr⟩ := exists_radius_logb_inverse_ge (b := 7) (D := 16) (by norm_num)
  apply polyHighProb_forall_prevalenceGrid_of_fixed_center P _ (q := 6) (C := C) (by norm_num) hr₀
  intro ε hε hεr z hz
  have h := htail Ω P (hCfield z) (hcirc z) (hgff z) μ z a b (hlocal z) (hprob z) ε hε (hr ε hε hεr)
  have hexp : 96 * Real.log 7 / (16 * Real.log 7) = (6 : ℝ) := by
    field_simp
    norm_num
  change P {ω | ¬ (1 / 32 : ℝ) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
    ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
      IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)} ≤ _
  norm_num only at h ⊢
  simpa only [not_le, hexp] using h

/-- Uniform locality and one-radius bounds imply very-good-annulus prevalence
for the absolute lattice used in the event definition. Each center uses its own
recentered whole-plane field. -/
theorem veryGoodAnnulus_prevalence_of_fixed_center :
    ∃ p ∈ Ioo (0 : ℝ) 1,
    ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : ℂ → Ω → (ℂ → ℝ) → ℝ) (hcirc : ℂ → Ω → ℝ → ℂ → ℝ),
      (∀ z : ℂ, IsWholePlaneGFF P (hC z) (hcirc z)) →
    ∀ (μ : Ω → Measure ℂ) (βminus : ℝ) (N : ℕ)
      (a b C₁m C₁p C₂m C₂p C₃ : ℝ),
      (∀ z : ℂ, ∀ n : ℕ, IsFieldMeasurableModConst P 0 (hC z)
        (annulus 0 (((8 : ℝ)⁻¹ ^ n) / 4) (2 * ((8 : ℝ)⁻¹ ^ n)))
        {ω | IsVeryGoodAnnulus (μ ω) βminus ((8 : ℝ)⁻¹ ^ n) z N
          a b C₁m C₁p C₂m C₂p C₃}) →
      (∀ z : ℂ, ∀ n : ℕ, ENNReal.ofReal p ≤ P {ω |
        IsVeryGoodAnnulus (μ ω) βminus ((8 : ℝ)⁻¹ ^ n) z N
          a b C₁m C₁p C₂m C₂p C₃}) →
      PolyHighProb P (fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
        (1 / 64 : ℝ) * Real.logb 8 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (8 : ℝ)⁻¹ ^ n) ∧
            IsVeryGoodAnnulus (μ ω) βminus r z N a b C₁m C₁p C₂m C₂p C₃}.ncard : ℝ)}) := by
  have hlog : 0 < Real.log 8 := Real.log_pos (by norm_num)
  obtain ⟨p, hp, C, hC, htail⟩ := veryGoodAnnulus_subrange_probability
    (192 * Real.log 8) (1 / 2) (by positivity) (by norm_num)
  refine ⟨p, hp, ?_⟩
  intro Ω _ P hCfield hcirc hgff μ βminus N a b C₁m C₁p C₂m C₂p C₃ hlocal hprob
  obtain ⟨r₀, hr₀, hr⟩ := exists_radius_logb_inverse_ge (b := 8) (D := 32) (by norm_num)
  apply polyHighProb_forall_prevalenceGrid_of_fixed_center P _ (q := 6) (C := C) (by norm_num) hr₀
  intro ε hε hεr z hz
  have h := htail Ω P (hCfield z) (hcirc z) (hgff z) μ z βminus N a b C₁m C₁p C₂m C₂p C₃
    (hlocal z) (hprob z) ε hε (hr ε hε hεr)
  have hexp : 192 * Real.log 8 / (32 * Real.log 8) = (6 : ℝ) := by
    field_simp
    norm_num
  change P {ω | ¬ (1 / 64 : ℝ) * Real.logb 8 (ε ^ (-1 : ℝ)) ≤
    ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (8 : ℝ)⁻¹ ^ n) ∧
      IsVeryGoodAnnulus (μ ω) βminus r z N a b C₁m C₁p C₂m C₂p C₃}.ncard : ℝ)} ≤ _
  norm_num only at h ⊢
  simpa only [not_le, hexp] using h

end HarmonicBalls.Section6
