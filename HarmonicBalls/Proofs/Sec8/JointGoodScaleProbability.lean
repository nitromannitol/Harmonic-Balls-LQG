import HarmonicBalls.Proofs.Sec8.UniformAnnulusThreshold
import HarmonicBalls.Draft.Section6

/-! # One-scale probability of the joint good event -/

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

/-- An annulus centred at the origin is separated from the origin by at least
one hundredth of its scale. -/
theorem origin_separated_from_scaled_annulus {ρ : ℝ} (hρ : 0 < ρ) :
    ρ / 100 ≤ infDist (0 : ℂ) (annulus 0 (ρ / 4) (2 * ρ)) := by
  have hne : (annulus (0 : ℂ) (ρ / 4) (2 * ρ)).Nonempty := by
    refine ⟨(ρ : ℂ), ?_⟩
    change dist (ρ : ℂ) 0 < 2 * ρ ∧ ¬ dist (ρ : ℂ) 0 ≤ ρ / 4
    rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    constructor <;> linarith
  apply (Metric.le_infDist hne).2
  intro z hz
  have hz' : ρ / 4 < dist z 0 := by
    have hnot : ¬ dist z 0 ≤ ρ / 4 := hz.2
    exact lt_of_not_ge hnot
  rw [dist_comm]
  linarith

universe u

/-- Lemma 6.7 and the uniform annulus-comparison threshold give a uniform
high-probability estimate for their joint event at every dyadic scale. -/
theorem exists_joint_goodScale_parameters
    (hVG : VeryGoodAnnulusProbabilityStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u}) :
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ βminus : ℝ, (2 + γ) ^ 2 / 2 < βminus →
    ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ b ∈ Ioo (0 : ℝ) 1,
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
    ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ N₀ : ℕ, N₁ ≤ N₀ → ∃ m : ℝ, 0 < m ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      WholePlaneGFFAffineInvariance P hC hcirc → LQGMeasureCoordChange P γ α₀ hC hcirc →
      ∀ n, P {ω | ¬ (IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n 0 m)} ≤ ENNReal.ofReal ε := by
  classical
  obtain ⟨C₃, hC₃, hVG⟩ := hVG
  refine ⟨C₃, hC₃, ?_⟩
  intro γ α₀ hγ hγ2 hα βminus hβ ε hε b hb
  have hp : (1 - ε / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hε.1, hε.2]
  obtain ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h1m, h1p, h2m, h2p, N₁, hN₁, hgood⟩ :=
    hVG γ α₀ hγ hγ2 hα βminus hβ b hb (1 - ε / 2) hp
  refine ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h1m, h1p, h2m, h2p, N₁, hN₁, ?_⟩
  intro N₀ hN₀
  obtain ⟨m, hm, hcomp⟩ := exists_lqg_annulusBallComparison_uniform_threshold hfull
    γ α₀ hγ hγ2 hα (δ := ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (by linarith [hε.1]))
  refine ⟨m, hm.1, ?_⟩
  intro Ω _ P hC hcirc μ h hμ hAff hCC n
  have hv := hgood N₀ hN₀ Ω P hC hcirc μ h hμ (dyadicScale n) (dyadicScale_pos n) 0
    (origin_separated_from_scaled_annulus (dyadicScale_pos n))
  have hv' : P {ω | ¬ IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) 0 N₀
      a b C₁m C₁p C₂m C₂p C₃} ≤ ENNReal.ofReal (ε / 2) := by
    convert hv using 1
    congr 1
    ring
  calc
    P {ω | ¬ (IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n 0 m)} ≤
        P {ω | ¬ IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃} + P {ω | ¬ AnnulusBallComparison (μ ω) n 0 m} := by
      convert measure_union_le (μ := P) {ω | ¬ IsVeryGoodAnnulus (μ ω) βminus
        (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃}
        {ω | ¬ AnnulusBallComparison (μ ω) n 0 m} using 1
      congr 1
      ext ω
      simp only [mem_ofPred_eq, mem_union, not_and_or]
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      add_le_add hv' (hcomp Ω P hC hcirc μ h hμ hAff hCC n)
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by linarith [hε.1]) (by linarith [hε.1])]
      congr 1
      ring

end HarmonicBalls
