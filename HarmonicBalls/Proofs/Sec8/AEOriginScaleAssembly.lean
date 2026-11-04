import HarmonicBalls.Proofs.Sec8.LQGFrequencyFromRatios
import HarmonicBalls.Proofs.Sec8.AENormalizedRestriction

/-! # Origin good scales from almost-everywhere normalized restrictions

The pointwise ergodic theorem used through `LQGFrequencyFromRatios` is from
Leonardo Bonanno's LatticeProb formalization, `LatticeProb.Prob.Birkhoff`.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

universe u

open Classical MarkovProcess in
/-- The LQG good-scale bound follows from the one-scale failure estimate,
almost-sure normalized local measure versions and germ triviality. -/
theorem ae_eventually_lqg_goodScaleCount_of_ae_normalizedRestriction
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hatom : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ ε₀ : ℝ) (ha : 0 < a)
    (hpolar : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    (germ : ℝ → MeasurableSpace Ω) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hcofinal : ∀ ε, 0 < ε → ∃ n, r n ≤ ε)
    (hrmono : Antitone r) (hgmono : Monotone germ)
    (hrep : ∀ ε, 0 < ε → ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ) (germ ε) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (ball 0 ε))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1)
    (hε : 0 ≤ ε₀) (hεζ : ε₀ < ζ)
    (hfail : P {ω | ¬ (IsVeryGoodAnnulus (μ ω) β (dyadicScale 0) 0 N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) 0 0 m)} ≤ ENNReal.ofReal ε₀) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      veryGoodComparableScaleCount (μ ω) β 0 N₀ a b C₁m C₁p C₂m C₂p C₃ m N := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let A : Set Ω := {ω | IsVeryGoodAnnulus (μ ω) β (dyadicScale 0) 0 N₀
    a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) 0 0 m}
  have hd := identDistrib_lqg_veryGoodComparable_of_ae_point_avoidance hfull hγ hγ2 hα
    hGFF hμ hatom hAff hCC β N₀ a b C₁m C₁p C₂m C₂p C₃ m ha hpolar
  have hF := (measurable_pi_apply (0 : ℕ)).comp_aemeasurable hd.aemeasurable_fst
  have hAn : NullMeasurableSet A P := by
    convert hF.nullMeasurableSet_preimage (measurableSet_singleton (1 : ℝ)) using 1
    ext ω
    simp only [A, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply]
    split_ifs <;> simp_all
  have hq : 1 - ζ < (P A).toReal := probability_gt_of_small_failure P A hAn hε hεζ hfail
  have hfullae := hfull γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  have hatomae := hatom hGFF hγ hγ2 hα μ hμ
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [hμ] with ω hω
    exact hω.isLocallyFiniteMeasure
  have hlocal := ae_local_veryGoodComparable_indicators_of_ae_normalizedRestriction P germ μ β N₀
    a b C₁m C₁p C₂m C₂p C₃ m ha hpolar hfullae hatomae hloc hrep
  exact ae_eventually_lqg_veryGoodComparableScaleCount_of_local_versions hfull hγ hγ2 hα
    hGFF hμ hatom hAff hCC β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ ha hpolar
    germ r hr hcofinal hrmono hgmono hlocal htrivial hq


open Classical MarkovProcess in
/-- Uniform parameter choice for the origin good-scale estimate, conditional
on point avoidance, almost-sure normalized measure versions, triviality of the
field germ, and the stated LQG inputs. -/
theorem origin_many_good_scales_of_ae_normalizedRestriction
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
      (∀ ε, 0 < ε → ∃ ν : Ω → Measure ℂ,
        @Measurable Ω (Measure ℂ) (Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)) _ ν ∧
        ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (ball 0 ε)) →
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
  intro Ω _ P hC hcirc μ hGFF hμ hatom hAff hCC hrep htrivial
  exact ae_eventually_lqg_goodScaleCount_of_ae_normalizedRestriction hfull hγ hγ2 hα hGFF hμ
    hatom hAff hCC β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ δ ha.1 hpolar
    (fun ε => Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)) dyadicScale
    dyadicScale_pos dyadicScale_germ_cofinal.2 dyadicScale_germ_cofinal.1
    (monotone_fieldSigmaAlgebraModConst_ball α₀ hC 0) hrep htrivial hδ.1.le hδζ
    (hfail Ω P hC hcirc μ hGFF hμ hAff hCC 0)


end HarmonicBalls
