import HarmonicBalls.Proofs.Sec6.ScaledCriterionThreeUniformProbability
import HarmonicBalls.Proofs.Sec6.SizeUniformProbability
import HarmonicBalls.Proofs.Sec6.SingularDyadicVeryGoodProbability
import HarmonicBalls.Proofs.Sec6.VeryGoodUnionBound

/-! # Very-good annuli at all positive radii

The good-annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- The frozen Lemma 6.7 follows from volume growth and the staged existence
of the zero-strength LQG measure, without a coordinate-change hypothesis. -/
theorem veryGoodAnnulusProbabilityStmt_of_volumeGrowth_zero_existence
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc) :
    VeryGoodAnnulusProbabilityStmt.{u} := by
  classical
  refine ⟨1 / 32, by norm_num, ?_⟩
  intro γ α hγ hγ₂ hα β hβ b hb p hp
  let K : ℝ := ((401 : ℝ) ^ |-(γ * α)|) ^ 2
  have hK1 : 1 ≤ K := by
    have hbase : (1 : ℝ) ≤ (401 : ℝ) ^ |-(γ * α)| :=
      Real.one_le_rpow (by norm_num) (abs_nonneg _)
    dsimp [K]
    nlinarith
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hK1
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
    obtain ⟨a, ha, N₁, hN₁, hthree⟩ :=
      exists_universal_criterionThree_probability_all_radii hgrowth hγ hγ₂ h₀ hμ₀ hb.1 hδ
    obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, hsize⟩ :=
      exists_universal_lqg_size_windows_all_radii (α := α) hgrowth hγ hγ₂ hβ P₀ h₀ hμ₀ hδ
    have ha' : a / K ∈ Ioo (0 : ℝ) 1 :=
      ⟨div_pos ha.1 hK, (div_lt_one hK).2 (lt_of_lt_of_le ha.2 hK1)⟩
    refine ⟨a / K, ha', C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p,
      N₁, by omega, ?_⟩
    intro N hN Ω _ P hC hcirc μ hgff hμ ρ hρ x hd
    have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
    obtain ⟨ν, hν⟩ := hE0 Ω P γ hC hcirc hgff hγ hγ₂ hQ
    have hW := lqgMeasureWeylScaling Ω P γ 0 hC hcirc
    have hweight : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
        ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ := by
      have h1 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
      filter_upwards [h1, hW hgff hγ hγ₂ hQ ν hν] with ω hω1 hω2
      exact restrict_compl_zero_eq_withDensity hω1 hω2
    have hthird : P {ω | ¬ VeryGoodCriterionThree (μ ω) ρ x N (a / K) b (1 / 32)} ≤ δ := by
      have hcompare := measure_not_criterionThree_le_of_singular_weight P (a := a) (b := b) (C₃ := 1 / 32)
        hρ hd (hN₁.trans hN) hweight
      exact hcompare.trans (hthree N hN Ω P hC hcirc ν hgff hν ρ hρ x)
    have hs := hsize Ω P hC hcirc μ hgff hμ (hE0 Ω P γ hC hcirc) ρ hρ x hd
    have hsum : δ + δ + δ = ENNReal.ofReal (1 - p) := by
      dsimp [δ]
      rw [← ENNReal.ofReal_add hδreal.le,
        ← ENNReal.ofReal_add (by linarith : 0 ≤ (1 - p) / 3 + (1 - p) / 3)]
      congr 1
      ring
      all_goals exact hδreal.le
    calc
      _ ≤ _ := measure_not_veryGoodAnnulus_le P μ β ρ x N (a / K) b C₁m C₁p C₂m C₂p (1 / 32)
      _ ≤ δ + δ + δ := add_le_add (add_le_add hs.1 hs.2) hthird
      _ = _ := hsum
  · refine ⟨1 / 2, by norm_num, 1, 1, 1, 1, by norm_num, by norm_num, by norm_num,
      by norm_num, 1, by omega, ?_⟩
    intro N hN Ω mΩ P hC hcirc μ hgff hμ ρ hρ x hd
    exfalso
    apply href
    have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
    obtain ⟨ν, hν⟩ := hE0 Ω P γ hC hcirc hgff hγ hγ₂ hQ
    exact ⟨Ω, mΩ, P, hC, hcirc, ν, hgff, hν⟩

end HarmonicBalls.Section6
