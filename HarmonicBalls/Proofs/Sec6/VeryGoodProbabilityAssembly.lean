import HarmonicBalls.Proofs.Sec6.SingularCriterionThreeProbability
import HarmonicBalls.Proofs.Sec6.VeryGoodUnionBound
import HarmonicBalls.Steps.Sec6.Prevalence

/-! # Probability of a very-good annulus

The three criteria are combined using a uniform subrange prevalence estimate.
The latter and the Brownian point-avoidance and LQG inputs remain hypotheses.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal

universe u

open MarkovProcess in
/-- The frozen Lemma 6.7 follows from subrange prevalence, Brownian point
avoidance, volume growth, and the stated affine and LQG inputs. -/
theorem veryGoodAnnulusProbabilityStmt_of_subrange_and_point_avoidance
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hsub : GoodAnnuliSubRangeStep.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hex : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hpolar : ∀ v ∈ sphere (0 : ℂ) 4, ∀ x ∈ annulus 0 3 5, x ≠ v →
      ∀ᵐ path ∂(planarBrownianMotion v), ∀ t : ℝ≥0, path t ≠ x) :
    VeryGoodAnnulusProbabilityStmt.{u} := by
  classical
  obtain ⟨c, hc, hsub⟩ := hsub
  refine ⟨c, hc, ?_⟩
  intro γ α₀ hγ hγ₂ hα β hβ b hb p hp
  obtain ⟨a, ha, hprev⟩ := hsub γ hγ hγ₂ b hb
  let K : ℝ := ((401 : ℝ) ^ |-(γ * α₀)|) ^ 2
  have hK1 : 1 ≤ K := by
    have hbase : (1 : ℝ) ≤ (401 : ℝ) ^ |-(γ * α₀)| :=
      Real.one_le_rpow (by norm_num) (abs_nonneg _)
    dsimp [K]
    nlinarith
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have ha' : a / K ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos ha.1 hK, (div_lt_one hK).2 (lt_of_lt_of_le ha.2 hK1)⟩
  let δ : ℝ≥0∞ := ENNReal.ofReal ((1 - p) / 3)
  have hδreal : 0 < (1 - p) / 3 := by linarith [hp.2]
  have hδ : 0 < δ := ENNReal.ofReal_pos.2 hδreal
  obtain ⟨C₁m, C₁p, C₂m, C₂p, hC₁m, hC₁p, hC₂m, hC₂p, hw⟩ :=
    exists_universal_lqg_size_windows_of_inputs hgrowth hγ hγ₂ hα hβ hδ
  have hunit : MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ 1 0 a b} := by
    apply measurableSet_isGoodAnnulus_of_ae_point_avoidance 1 (by norm_num) 0 a b ha.1
    simpa using hpolar
  by_cases href : ∃ (Ω₀ : Type u) (m₀ : MeasurableSpace Ω₀),
      letI := m₀
      ∃ (P₀ : Measure Ω₀) (hC₀ : Ω₀ → (ℂ → ℝ) → ℝ)
        (hcirc₀ : Ω₀ → ℝ → ℂ → ℝ) (μ₀ : Ω₀ → Measure ℂ),
        IsWholePlaneGFF P₀ hC₀ hcirc₀ ∧ IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀
  · obtain ⟨Ω₀, m₀, P₀, hC₀, hcirc₀, μ₀, h₀, hμ₀⟩ := href
    let : MeasurableSpace Ω₀ := m₀
    have hprev₀ := hprev Ω₀ P₀ hC₀ hcirc₀ μ₀ h₀ hμ₀
    obtain ⟨N₁, hN₁, hthree⟩ :=
      exists_universal_singular_criterionThree_probability P₀ hγ hγ₂ hc h₀ hμ₀
        (hAff Ω₀ P₀ hC₀ hcirc₀) (hCC Ω₀ P₀ γ hC₀ hcirc₀) hprev₀ hunit hδ
    refine ⟨a / K, ha', C₁m, C₁p, C₂m, C₂p, hC₁m, hC₁p, hC₂m, hC₂p,
      N₁, by omega, ?_⟩
    intro N hN Ω mΩ P hC hcirc μ hgff hμ ρ hρ x hd
    have hsize := hw Ω P hC hcirc μ hgff hμ (hex Ω P γ hC hcirc)
      (hW Ω P γ hC hcirc) (hAff Ω P hC hcirc) (hCC Ω P γ hC hcirc) ρ hρ x hd
    have hthird := hthree N hN Ω P hC hcirc μ hgff hμ (hex Ω P γ hC hcirc)
      (hW Ω P γ hC hcirc) (hAff Ω P hC hcirc) (hCC Ω P γ hC hcirc) ρ hρ x hd
    have hsum : δ + δ + δ = ENNReal.ofReal (1 - p) := by
      dsimp [δ]
      rw [← ENNReal.ofReal_add hδreal.le,
        ← ENNReal.ofReal_add (by linarith : 0 ≤ (1 - p) / 3 + (1 - p) / 3)]
      congr 1
      ring
      all_goals exact hδreal.le
    calc
      _ ≤ _ := measure_not_veryGoodAnnulus_le P μ β ρ x N (a / K) b C₁m C₁p C₂m C₂p c
      _ ≤ δ + δ + δ := add_le_add (add_le_add hsize.1 hsize.2) (by simpa [K] using hthird)
      _ = _ := hsum
  · refine ⟨a / K, ha', C₁m, C₁p, C₂m, C₂p, hC₁m, hC₁p, hC₂m, hC₂p,
      9, by omega, ?_⟩
    intro N hN Ω mΩ P hC hcirc μ hgff hμ ρ hρ x hd
    exfalso
    apply href
    have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
    obtain ⟨ν, hν⟩ := hex Ω P γ hC hcirc hgff hγ hγ₂ hQ
    exact ⟨Ω, mΩ, P, hC, hcirc, ν, hgff, hν⟩

end HarmonicBalls.Section6
