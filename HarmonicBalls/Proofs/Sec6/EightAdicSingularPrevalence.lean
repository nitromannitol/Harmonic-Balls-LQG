import HarmonicBalls.Proofs.Sec6.EightAdicGoodPrevalence
import HarmonicBalls.Proofs.Sec6.AlmostSureSingularPrevalence

/-! # Eight-adic prevalence for logarithmic singularities

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The cofinal existence
hypotheses are literature inputs (PENDING TRUTH CHECK).
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

universe u

/-- Eight-adic good-annulus prevalence holds simultaneously over every bounded
range of subcritical singularity strengths, with constants independent of the
range. -/
theorem eightAdic_goodAnnuli_uniform_bounded_singularities
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc)
    {b : ℝ} (hb : 0 < b) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ A : ℝ, 0 ≤ A →
      PolyHighProb P (fun ε => {ω | ∀ α : ℝ, |α| ≤ A → α < lqgQ γ →
        ∀ μ : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
        ∀ z ∈ prevalenceGrid ε,
        (1 / 32 : ℝ) * Real.logb 8 (ε ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc ε (Real.sqrt ε) ∧ (∃ n : ℕ, r = (8 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus μ r z a b}.ncard : ℝ)}) := by
  obtain ⟨a, ha, hprev⟩ := eightAdic_goodAnnulus_prevalence_of_volumeGrowth hgrowth hγ hγ2 hb
  obtain ⟨μ₀, hμ₀, hrepr⟩ :=
    exists_ae_all_subcritical_limits_eq_singularWeight_of_cofinal P γ hγ hγ2 hC hcirc hG hE
  refine ⟨a / 4, ⟨by linarith [ha.1], by linarith [ha.2]⟩, ?_⟩
  intro A hA
  refine ((hprev Ω P hC hcirc μ₀ hG hμ₀).inter_ae hrepr).mono_of_eventually ?_
  filter_upwards [eventually_small_for_bounded_strengths γ A hA, self_mem_nhdsWithin]
    with ε hε hε0
  rintro ω ⟨hω, hωW⟩ α hαA hα μ hμ z hz
  have hexp := hε.2 α hαA
  have hweight : μ.restrict {0}ᶜ =
      ((μ₀ ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ := by
    rw [hωW α hα μ hμ]
  refine ((logb_neg_half_le (by norm_num) (by norm_num : (0 : ℝ) < 1 / 32)
    hε0 hε.1.le).trans (hω z hz)).trans ?_
  norm_cast
  refine Set.ncard_le_ncard (fun r hr => ⟨⟨hr.1.1, ?_⟩, hr.2.1, ?_⟩) ?_
  · calc r ≤ ε ^ (3 / 4 : ℝ) := hr.1.2
      _ ≤ Real.sqrt ε := by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow_of_exponent_ge hε0 hε.1.le (by norm_num)
  · have hr0 : 0 < r := hε0.trans_le hr.1.1
    exact isGoodAnnulus_of_comparable
      (isComparableOn_grid hε0 hε.1 hexp hweight hz (by positivity) (by linarith [hr.1.2]))
      sdiff_subset hr.2.2
  · refine finite_of_geometric (q := (8 : ℝ)⁻¹) (A := 1) (lo := ε)
      (by norm_num) (by norm_num) hε0 fun r hr => ⟨hr.1.1, ?_⟩
    obtain ⟨n, hn⟩ := hr.2.1
    exact ⟨n, by rw [hn, one_mul]⟩

/-- On one probability-one event, every subcritical singularity has eight-adic
good-annulus prevalence for all sufficiently small inverse dyadic scales. -/
theorem ae_eventually_eightAdic_goodAnnuli_all_subcritical
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc)
    {b : ℝ} (hb : 0 < b) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ α : ℝ, α < lqgQ γ →
      ∀ᶠ k : ℕ in atTop, ∀ μ : Measure ℂ,
        IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
        ∀ z ∈ prevalenceGrid ((2 : ℝ)⁻¹ ^ k),
        (1 / 32 : ℝ) * Real.logb 8 (((2 : ℝ)⁻¹ ^ k) ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc ((2 : ℝ)⁻¹ ^ k) (Real.sqrt ((2 : ℝ)⁻¹ ^ k)) ∧
            (∃ n : ℕ, r = (8 : ℝ)⁻¹ ^ n) ∧ IsGoodAnnulus μ r z a b}.ncard : ℝ) := by
  obtain ⟨a, ha, hp⟩ :=
    eightAdic_goodAnnuli_uniform_bounded_singularities hgrowth P γ hγ hγ2 hC hcirc hG hE hb
  refine ⟨a, ha, ?_⟩
  filter_upwards [ae_all_iff.mpr (fun n : ℕ =>
    (hp n (Nat.cast_nonneg n)).ae_eventually_dyadic)] with ω hω
  intro α hα
  obtain ⟨n, hn⟩ := exists_nat_gt |α|
  filter_upwards [hω n] with k hk
  exact hk α hn.le hα

end HarmonicBalls.Section6
