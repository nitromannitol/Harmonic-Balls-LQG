import HarmonicBalls.Proofs.Sec8.UniformPhasePrevalenceAssembly
import HarmonicBalls.Proofs.Sec8.RootedSingularPhaseFrequency

/-! # Uniform rooted frequency from good-annulus prevalence

The imported ergodic theorem is due to Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization.
-/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

universe u

open Classical in
/-- Subrange prevalence fixes the third-criterion constant before the
parameters of the rooted frequency estimate. The explicit rooted and
recentered law comparisons are required for every target model. -/
theorem exists_uniform_rooted_frequency_of_subrange
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hsub : GoodAnnuliSubRangeStep.{u}) :
    ∃ c : ℝ, 0 < c ∧ ∀ γ α β : ℝ, 0 < γ → γ < 2 → α < lqgQ γ →
      (2 + γ) ^ 2 / 2 < β → ∀ ζ : ℝ, 0 < ζ → ∀ b ∈ Ioo (0 : ℝ) 1,
      ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C₁m C₁p C₂m C₂p : ℝ,
        0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
        ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∃ m ∈ Ioo (0 : ℝ) 1,
        ∀ N : ℕ, N₀ ≤ N →
      ∀ (Ξ : Type u) [MeasurableSpace Ξ] (P₁ : Measure Ξ)
        (hC : Ξ → (ℂ → ℝ) → ℝ) (hcirc : Ξ → ℝ → ℂ → ℝ) (μ₁ : Ξ → Measure ℂ),
      IsWholePlaneGFF P₁ hC hcirc → IsLQGMeasureOfField P₁ γ α hcirc μ₁ →
      LQGMeasureExistence P₁ γ 0 hC hcirc → LQGMeasureWeylScaling P₁ γ 0 hC hcirc →
      WholePlaneGFFAffineInvariance P₁ hC hcirc →
      LQGMeasureCoordChange P₁ γ 0 hC hcirc → LQGMeasureCoordChange P₁ γ α hC hcirc →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
        {μ : Ω → Measure ℂ} (hμ : AEMeasurable μ P)
        (_hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
        (S : Measure Ω), P ≪ S → AEMeasurable μ S →
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
      ∀ (F : ℕ → ℂ → Ω → {ν : Measure ℂ // IsLocallyFiniteMeasure ν}),
        (∀ n, ∀ᵐ z ∂ρ n, AEMeasurable (F n z) (R n z)) →
        (∀ U : Ξ → {ν : Measure ℂ // IsLocallyFiniteMeasure ν}, Measurable U →
          (∀ᵐ ω ∂P₁, (U ω).val = μ₁ ω) →
          ∀ n, ∀ᵐ z ∂ρ n, (R n z).map (F n z) ≪ P₁.map U) →
        (∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ ω ∂(R n z),
          (μ ω).map (fun v : ℂ => v - z) = (F n z ω).val) →
      ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ K : ℕ in atTop,
        (1 - ζ) * (K : ℝ) ≤ (veryGoodComparableScaleCount (μ ω) β z N
          a b C₁m C₁p C₂m C₂p c m K : ℝ) := by
  obtain ⟨c, hc, hprob⟩ :=
    exists_uniform_singular_phase_probability_of_subrange hgrowth hfull hsub
  refine ⟨c, hc, ?_⟩
  intro γ α β hγ hγ₂ hα hβ ζ hζ b hb
  obtain ⟨a, ha, hprob⟩ := hprob γ α β hγ hγ₂ hα hβ b hb
  let δ : ℝ≥0∞ := ENNReal.ofReal (ζ / 8)
  have hδ : 0 < δ := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, hfail⟩ :=
    hprob δ hδ
  let D : ℝ := ((401 : ℝ) ^ |-(γ * α)|) ^ 2
  have hD : 1 ≤ D := by
    dsimp only [D]
    have h := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 401) (abs_nonneg (-(γ * α)))
    nlinarith
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have ha' : a / D ∈ Ioo (0 : ℝ) 1 := ⟨div_pos ha.1 hDpos, (div_lt_one hDpos).2 (lt_of_lt_of_le ha.2 hD)⟩
  have hδsum : δ + δ + δ + δ = ENNReal.ofReal (ζ / 2) := by
    dsimp only [δ]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  refine ⟨a / D, ha', C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, ?_⟩
  intro N hN Ξ _ P₁ hC hcirc μ₁ hGFF hμ₁ hEx hW hAff hCC hCCα
    Ω _ P _ μ hμ hloc S hPdom hμS hlocS w hw hpos hfin ρ hρ
    shift hshift R hrooted hac hdom F hF hlaw hcenter
  apply hGFF.ae_ae_rooted_veryGoodComparableScaleFrequency_of_singular_phase_bound hfull
    hγ hγ₂ hα hμ₁ hAff hCCα N _ b C₁m C₁p C₂m C₂p c m (ζ / 2) ζ ha'.1
    (by positivity) (by linarith) ?_ P hμ hloc S hPdom hμS hlocS w hw hpos hfin
    ρ hρ shift hshift R hrooted hac hdom F hF hlaw hcenter
  intro q
  simpa only [hδsum, D] using hfail N hN Ξ P₁ hC hcirc μ₁ hGFF hμ₁ hEx hW hAff hCC hCCα q

end HarmonicBalls
