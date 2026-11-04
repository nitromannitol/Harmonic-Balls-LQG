import HarmonicBalls.Proofs.Sec8.LQGFrequencyFromRatios

/-! # Uniform parameters for good scales at the origin

The pointwise ergodic theorem used through `LQGFrequencyFromRatios` is from
Leonardo Bonanno's LatticeProb formalization, `LatticeProb.Prob.Birkhoff`.
-/

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

universe u

open Classical MarkovProcess in
/-- Uniform parameter choice for the origin good-scale estimate, conditional
on point avoidance, normalized mass-ratio germ measurability, triviality of the
field germ, and the stated LQG inputs. -/
theorem origin_many_good_scales_of_mass_ratios
    (hVG : VeryGoodAnnulusProbabilityStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hpolar : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ β : ℝ, (2 + γ) ^ 2 / 2 < β →
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ ζ : ℝ, 0 < ζ → ∀ b ∈ Ioo (0 : ℝ) 1,
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
    ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ N₀ : ℕ, N₁ ≤ N₀ → ∃ m : ℝ, 0 < m ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      LQGMeasureNonatomic P γ α₀ hC hcirc → WholePlaneGFFAffineInvariance P hC hcirc →
      LQGMeasureCoordChange P γ α₀ hC hcirc →
      (∀ ε, 0 < ε → ∀ V : Set ℂ, IsOpen V →
        @Measurable Ω ℝ≥0∞ (Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)) _
          (fun ω => μ ω (V ∩ ball 0 ε) / μ ω (ball 0 ε))) →
      (∀ A : Set Ω, (∀ ε, 0 < ε →
        MeasurableSet[Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)] A) →
          P A = 0 ∨ P A = 1) →
      ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
        (1 - ζ) * (N : ℝ) ≤ veryGoodComparableScaleCount (μ ω) β 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ m N := by
  obtain ⟨C₃, hC₃, hp⟩ := exists_joint_goodScale_parameters hVG hfull
  intro γ α₀ hγ hγ2 hα β hβ
  refine ⟨C₃, hC₃, ?_⟩
  intro ζ hζ b hb
  let δ : ℝ := min (ζ / 2) (1 / 2)
  have hδ : δ ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact lt_min (by linarith) (by norm_num)
    · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδζ : δ < ζ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h1m, h1p, h2m, h2p, N₁, hN₁, hp⟩ :=
    hp γ α₀ hγ hγ2 hα β hβ δ hδ b hb
  refine ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h1m, h1p, h2m, h2p, N₁, hN₁, ?_⟩
  intro N₀ hN₀
  obtain ⟨m, hm, hfail⟩ := hp N₀ hN₀
  refine ⟨m, hm, ?_⟩
  intro Ω _ P hC hcirc μ hGFF hμ hatom hAff hCC hratio htrivial
  exact ae_eventually_lqg_goodScaleCount_of_mass_ratios hfull hγ hγ2 hα hGFF hμ
    hatom hAff hCC β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ δ ha.1 hpolar
    (fun ε => Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)) dyadicScale
    dyadicScale_pos dyadicScale_germ_cofinal.2 dyadicScale_germ_cofinal.1
    (monotone_fieldSigmaAlgebraModConst_ball α₀ hC 0) hratio htrivial hδ.1.le hδζ
    (hfail Ω P hC hcirc μ hGFF hμ hAff hCC 0)

end HarmonicBalls
