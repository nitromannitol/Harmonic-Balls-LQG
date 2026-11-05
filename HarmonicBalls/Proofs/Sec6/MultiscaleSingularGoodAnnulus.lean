import HarmonicBalls.Proofs.Sec6.UniformSingularGoodAnnulus

/-! # Multiscale good annuli for bounded singularity strengths

The underlying fine-support argument uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The zero-strength existence
input is staged pending source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

universe u

/-- A summable failure budget gives a deterministic threshold at each scale,
uniform over countable admissible annulus families and bounded singularity
strengths. The compact positive-radius sets may approach zero with the scale. -/
theorem exists_multiscale_uniform_singular_goodAnnulus_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc)
    (K : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n))
    (R : ℕ → Set ℝ) (hR : ∀ n, IsCompact (R n)) (hRpos : ∀ n, R n ⊆ Ioi 0)
    {b E : ℝ} (hb : 0 < b) (hE : 0 ≤ E)
    (δ : ℕ → ℝ≥0∞) (hδ : ∀ n, 0 < δ n) :
    ∃ a : ℕ → ℝ, (∀ n, a n ∈ Ioo (0 : ℝ) 1) ∧
      ∀ (z : ℕ → ℕ → ℂ) (r : ℕ → ℕ → ℝ),
        (∀ n i, z n i ∈ K n) → (∀ n i, r n i ∈ R n) →
        (∀ n i, r n i / 100 ≤ infDist (0 : ℂ)
          (annulus (z n i) (3 * r n i) (5 * r n i))) →
        P {ω | ∃ (n i : ℕ) (α : ℝ) (μ : Measure ℂ), |γ * α| ≤ E ∧
          IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ ∧
          ¬ IsGoodAnnulus μ (r n i) (z n i) (a n) b} ≤ ∑' n, δ n := by
  classical
  have hex : ∀ n, ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (z : ℕ → ℂ) (r : ℕ → ℝ),
      (∀ i, z i ∈ K n) → (∀ i, r i ∈ R n) →
      (∀ i, r i / 100 ≤ infDist (0 : ℂ) (annulus (z i) (3 * r i) (5 * r i))) →
      P {ω | ∃ (i : ℕ) (α : ℝ) (μ : Measure ℂ), |γ * α| ≤ E ∧
        IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ ∧
        ¬ IsGoodAnnulus μ (r i) (z i) a b} ≤ δ n := by
    intro n
    exact exists_uniform_singular_goodAnnulus_probability hgrowth hγ hγ2 h hE0
      (hK n) (hR n) (hRpos n) hb hE (hδ n)
  choose a ha hbound using hex
  refine ⟨a, ha, ?_⟩
  intro z r hz hr hd
  let B : ℕ → Set Ω := fun n => {ω | ∃ (i : ℕ) (α : ℝ) (μ : Measure ℂ), |γ * α| ≤ E ∧
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ ∧
      ¬ IsGoodAnnulus μ (r n i) (z n i) (a n) b}
  have hsub : {ω | ∃ (n i : ℕ) (α : ℝ) (μ : Measure ℂ), |γ * α| ≤ E ∧
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ ∧
      ¬ IsGoodAnnulus μ (r n i) (z n i) (a n) b} ⊆ ⋃ n, B n := by
    rintro ω ⟨n, i, α, μ, hα, hμ, hbad⟩
    exact mem_iUnion.mpr ⟨n, i, α, μ, hα, hμ, hbad⟩
  calc
    _ ≤ P (⋃ n, B n) := measure_mono hsub
    _ ≤ ∑' n, P (B n) := measure_iUnion_le B
    _ ≤ ∑' n, δ n := ENNReal.tsum_le_tsum (fun n => hbound n (z n) (r n) (hz n) (hr n) (hd n))

/-- Any positive error budget can be split into strictly positive geometric
scale-wise budgets. -/
theorem exists_positive_geometric_error_budget {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ δ : ℕ → ℝ≥0∞, (∀ n, 0 < δ n) ∧ (∑' n, δ n) ≤ η := by
  refine ⟨fun n => (η / 2) * ((1 / 2 : ℝ≥0∞) ^ n), ?_, ?_⟩
  · intro n
    exact ENNReal.mul_pos (ENNReal.div_pos hη.ne' (by norm_num)).ne' (pow_ne_zero n (by norm_num))
  · rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    norm_num
    rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num)]

/-- A field-dependent scale, annulus index and bounded singularity strength
are controlled by the sum of the scale-wise budgets. -/
theorem exists_multiscale_selected_singular_goodAnnulus_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc)
    (K : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n))
    (R : ℕ → Set ℝ) (hR : ∀ n, IsCompact (R n)) (hRpos : ∀ n, R n ⊆ Ioi 0)
    {b E : ℝ} (hb : 0 < b) (hE : 0 ≤ E)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ a : ℕ → ℝ, (∀ n, a n ∈ Ioo (0 : ℝ) 1) ∧
      ∀ (z : ℕ → ℕ → ℂ) (r : ℕ → ℕ → ℝ),
        (∀ n i, z n i ∈ K n) → (∀ n i, r n i ∈ R n) →
        (∀ n i, r n i / 100 ≤ infDist (0 : ℂ)
          (annulus (z n i) (3 * r n i) (5 * r n i))) →
        ∀ (scale index : Ω → ℕ) (α : Ω → ℝ) (μ : Ω → Measure ℂ),
        (∀ᵐ ω ∂P, |γ * α ω| ≤ E ∧ IsLQGLimit γ (fieldCircleAverage (α ω) (hcirc ω)) (μ ω)) →
        P {ω | ¬ IsGoodAnnulus (μ ω) (r (scale ω) (index ω)) (z (scale ω) (index ω))
          (a (scale ω)) b} ≤ η := by
  obtain ⟨δ, hδ, hsum⟩ := exists_positive_geometric_error_budget hη
  obtain ⟨a, ha, hbound⟩ := exists_multiscale_uniform_singular_goodAnnulus_probability
    hgrowth hγ hγ2 h hE0 K hK R hR hRpos hb hE δ hδ
  refine ⟨a, ha, ?_⟩
  intro z r hz hr hd scale index α μ hlim
  apply (measure_mono_ae ?_).trans ((hbound z r hz hr hd).trans hsum)
  filter_upwards [hlim] with ω hω hbad
  exact ⟨scale ω, index ω, α ω, μ ω, hω.1, hω.2, hbad⟩

end HarmonicBalls.Section6
