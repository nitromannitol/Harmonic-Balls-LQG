import HarmonicBalls.Proofs.Sec8.RootedAmbientMeasureLaw

/-! # Typical-point frequency with a γ-log singular reference

The imported ergodic theorem is due to Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. The rooted and centered law
comparisons are explicit assumptions, not established field laws.
-/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

universe u

/-- The rooted reduction at the paper's singularity strength `γ`, restricted
to typical points in the unit disc, with the same parameter order as Lemma 8.2. -/
theorem exists_uniform_typicalPoint_frequency_of_centered_measureLaw
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hsub : GoodAnnuliSubRangeStep.{u}) :
    ∃ c : ℝ, 0 < c ∧ ∀ γ β : ℝ, 0 < γ → γ < 2 →
      (2 + γ) ^ 2 / 2 < β → ∀ ζ : ℝ, 0 < ζ → ∀ b ∈ Ioo (0 : ℝ) 1,
      ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C₁m C₁p C₂m C₂p : ℝ,
        0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
        ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∃ m : ℝ, 0 < m ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (μ ν : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc ν →
      LQGMeasureExistence P γ 0 hC hcirc → LQGMeasureWeylScaling P γ 0 hC hcirc →
      WholePlaneGFFAffineInvariance P hC hcirc →
      LQGMeasureCoordChange P γ 0 hC hcirc → LQGMeasureCoordChange P γ γ hC hcirc →
      ∀ (hμ : AEMeasurable μ P) (S : Measure Ω), P ≪ S → AEMeasurable μ S →
        (∀ᵐ ω ∂S, IsLocallyFiniteMeasure (μ ω)) →
      ∀ (w : ℂ → ℝ≥0∞) (hw : Measurable w),
        (∀ z, w z ≠ 0) → (∀ z, w z ≠ ∞) →
      ∀ (ρ : ℕ → Measure ℂ), (∀ n, ρ n ≪ volume) →
      ∀ (shift : ℕ → ℂ × Ω → Ω), (∀ n, Measurable (shift n)) →
      ∀ (R : ℕ → ℂ → Measure Ω),
        (∀ n, P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
          (weightedLocalization w n) (measurableSet_weightedLocalization hw n) w hw) ≪
            shiftedRootReferenceLaw (ρ n) P (shift n)) →
        (∀ n, ∀ᵐ z ∂ρ n, P.map (fun ω => shift n (z, ω)) ≪ R n z) →
        (∀ n, ∀ᵐ z ∂ρ n, R n z ≪ S) →
        (∀ n, ∀ᵐ z ∂ρ n,
          (R n z).map (fun ω => (μ ω).map (fun v : ℂ => v - z)) ≪ P.map ν) →
      ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω).restrict (ball (0 : ℂ) 1), ∀ᶠ K : ℕ in atTop,
        (1 - ζ) * (K : ℝ) ≤ (veryGoodComparableScaleCount (μ ω) β z N
          a b C₁m C₁p C₂m C₂p c m K : ℝ) := by
  obtain ⟨c, hc, hfreq⟩ := exists_uniform_rooted_frequency_of_centered_measureLaw hgrowth hfull hsub
  refine ⟨c, hc, ?_⟩
  intro γ β hγ hγ₂ hβ ζ hζ b hb
  have hγQ : γ < lqgQ γ := by
    unfold lqgQ
    have hprod : 0 < (2 - γ) * (2 + γ) := mul_pos (by linarith) (by linarith)
    have hdiv : γ / 2 < 2 / γ := (div_lt_div_iff₀ (by norm_num) hγ).2 (by nlinarith)
    linarith
  obtain ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, hfreq⟩ :=
    hfreq γ γ β hγ hγ₂ hγQ hβ ζ hζ b hb
  refine ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, by omega, ?_⟩
  intro N hN
  refine ⟨m, hm.1, ?_⟩
  intro Ω _ P _ hC hcirc μ ν hGFF hν hEx hW hAff hCC hCCγ
    hμ S hPdom hμS hlocS w hw hpos hfin ρ hρ shift hshift R hrooted hac hdom hraw
  have h := hfreq N hN Ω P hC hcirc ν hGFF hν hEx hW hAff hCC hCCγ
    P hμ S hPdom hμS hlocS w hw hpos hfin ρ hρ shift hshift R hrooted hac hdom hraw
  filter_upwards [h] with ω hω
  exact ae_restrict_of_ae hω

end HarmonicBalls
