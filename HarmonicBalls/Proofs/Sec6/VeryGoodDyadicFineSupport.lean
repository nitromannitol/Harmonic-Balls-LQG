import HarmonicBalls.Proofs.Sec6.SevenAdicFineSupportPrevalence
import HarmonicBalls.Proofs.Sec6.SingularDyadicVeryGoodProbability

/-! # Very-good annuli at inverse dyadic radii

The prevalence estimate uses Leonardo Bonanno's annulus iteration in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- A dyadic-radius version of the very-good annulus estimate follows from
volume growth and zero-strength LQG existence, without a coordinate-change
hypothesis. The centres are deterministic and satisfy the stated separation
from the singularity. -/
theorem veryGoodAnnulus_dyadic_probability_of_volumeGrowth_zero_existence
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc) :
    ∃ c : ℝ, 0 < c ∧ ∀ γ α : ℝ, 0 < γ → γ < 2 → α < lqgQ γ →
    ∀ β : ℝ, (2 + γ) ^ 2 / 2 < β → ∀ b ∈ Ioo (0 : ℝ) 1,
    ∀ p ∈ Ioo (0 : ℝ) 1, ∃ a ∈ Ioo (0 : ℝ) 1,
    ∃ C₁m C₁p C₂m C₂p : ℝ, 0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
    ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ N : ℕ, N₁ ≤ N →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
    ∀ (n : ℕ) (z : ℂ), dyadicScale n / 100 ≤ infDist (0 : ℂ)
      (annulus z (dyadicScale n / 4) (2 * dyadicScale n)) →
    P {ω | ¬ IsVeryGoodAnnulus (μ ω) β (dyadicScale n) z N
      a b C₁m C₁p C₂m C₂p c} ≤ ENNReal.ofReal (1 - p) := by
  classical
  obtain ⟨c, hc, hsub⟩ := goodAnnuliSubRangeStep_of_volumeGrowth_fineSupport hgrowth
  refine ⟨c, hc, ?_⟩
  intro γ α hγ hγ₂ hα β hβ b hb p hp
  obtain ⟨a, ha, hprev⟩ := hsub γ hγ hγ₂ b hb
  let K : ℝ := ((401 : ℝ) ^ |-(γ * α)|) ^ 2
  have hK1 : 1 ≤ K := by
    have hbase : (1 : ℝ) ≤ (401 : ℝ) ^ |-(γ * α)| :=
      Real.one_le_rpow (by norm_num) (abs_nonneg _)
    dsimp [K]
    nlinarith
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have ha' : a / K ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos ha.1 hK, (div_lt_one hK).2 (lt_of_lt_of_le ha.2 hK1)⟩
  let δ : ℝ≥0∞ := ENNReal.ofReal ((1 - p) / 3)
  have hδreal : 0 < (1 - p) / 3 := by linarith [hp.2]
  have hδ : 0 < δ := ENNReal.ofReal_pos.2 hδreal
  by_cases href : ∃ (Ω₀ : Type u) (m₀ : MeasurableSpace Ω₀),
      letI := m₀
      ∃ (P₀ : Measure Ω₀) (hC₀ : Ω₀ → (ℂ → ℝ) → ℝ)
        (hcirc₀ : Ω₀ → ℝ → ℂ → ℝ) (μ₀ : Ω₀ → Measure ℂ),
        IsWholePlaneGFF P₀ hC₀ hcirc₀ ∧ IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀
  · obtain ⟨Ω₀, m₀, P₀, hC₀, hcirc₀, μ₀, h₀, hμ₀⟩ := href
    let : MeasurableSpace Ω₀ := m₀
    have hprev₀ := hprev Ω₀ P₀ hC₀ hcirc₀ μ₀ h₀ hμ₀
    obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₁, hN₁, hbound⟩ :=
      exists_universal_singular_dyadic_veryGood_probability_of_affine
        (α := α) (β := β) hgrowth P₀ hγ hγ₂ hβ ha.1 hc h₀ hμ₀
        (wholePlaneGFFAffineInvariance_proved P₀ hC₀ hcirc₀) hprev₀ hδ
    refine ⟨a / K, ha', C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p,
      N₁, by omega, ?_⟩
    intro N hN Ω _ P hC hcirc μ hgff hμ n z hd
    have hsum : δ + δ + δ = ENNReal.ofReal (1 - p) := by
      dsimp [δ]
      rw [← ENNReal.ofReal_add hδreal.le,
        ← ENNReal.ofReal_add (by linarith : 0 ≤ (1 - p) / 3 + (1 - p) / 3)]
      congr 1
      ring
      all_goals exact hδreal.le
    rw [← hsum]
    simpa only [K] using hbound N hN Ω P hC hcirc μ hgff hμ
      (hE0 Ω P γ hC hcirc) (wholePlaneGFFAffineInvariance_proved P hC hcirc) n z hd
  · refine ⟨a / K, ha', 1, 1, 1, 1, by norm_num, by norm_num, by norm_num,
      by norm_num, 1, by omega, ?_⟩
    intro N hN Ω mΩ P hC hcirc μ hgff hμ n z hd
    exfalso
    apply href
    have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
    obtain ⟨ν, hν⟩ := hE0 Ω P γ hC hcirc hgff hγ hγ₂ hQ
    exact ⟨Ω, mΩ, P, hC, hcirc, ν, hgff, hν⟩

end HarmonicBalls.Section6
