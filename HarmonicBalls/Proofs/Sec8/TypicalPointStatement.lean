import HarmonicBalls.Proofs.Sec8.TypicalPointAmbientLaw

/-! # The typical-point statement from rooted law comparisons

The imported ergodic theorem is due to Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. The comparison hypothesis is a
proof obligation and is not asserted as an external literature input.
-/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

universe u

/-- Lemma 8.2 follows from subrange prevalence, the staged LQG inputs, and
explicit rooted and centered measure-law comparisons for each target field. -/
theorem typicalPointManyGoodScalesStmt_of_ambientLaw
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hsub : GoodAnnuliSubRangeStep.{u})
    (hEx : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ α hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α hC hcirc)
    (hcomparison : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
      (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ ν : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
      (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ),
      0 < γ → γ < 2 → α₀ < lqgQ γ → IsLQGMeasureOfField P γ γ hcirc ν →
      ∃ S : Measure Ω, P ≪ S ∧ AEMeasurable μ S ∧
        (∀ᵐ ω ∂S, IsLocallyFiniteMeasure (μ ω)) ∧
      ∃ (w : ℂ → ℝ≥0∞) (hw : Measurable w),
        (∀ z, w z ≠ 0) ∧ (∀ z, w z ≠ ∞) ∧
      ∃ ρ : ℕ → Measure ℂ, (∀ n, ρ n ≪ volume) ∧
      ∃ shift : ℕ → ℂ × Ω → Ω, (∀ n, Measurable (shift n)) ∧
      ∃ R : ℕ → ℂ → Measure Ω,
        (∀ n, P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ
          (hGFF.aemeasurable_lqgMeasure hμ) (weightedLocalization w n)
          (measurableSet_weightedLocalization hw n) w hw) ≪
            shiftedRootReferenceLaw (ρ n) P (shift n)) ∧
        (∀ n, ∀ᵐ z ∂ρ n, P.map (fun ω => shift n (z, ω)) ≪ R n z) ∧
        (∀ n, ∀ᵐ z ∂ρ n, R n z ≪ S) ∧
        (∀ n, ∀ᵐ z ∂ρ n,
          (R n z).map (fun ω => (μ ω).map (fun v : ℂ => v - z)) ≪ P.map ν)) :
    TypicalPointManyGoodScalesStmt.{u} := by
  obtain ⟨c, hc, hfreq⟩ :=
    exists_uniform_typicalPoint_frequency_of_centered_measureLaw hgrowth hfull hsub
  intro γ α₀ hγ hγ₂ hα₀ β hβ
  refine ⟨c, hc, ?_⟩
  intro ζ hζ b hb
  obtain ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, hfreq⟩ :=
    hfreq γ β hγ hγ₂ hβ ζ hζ b hb
  refine ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, ?_⟩
  intro N hN
  obtain ⟨m, hm, hfreq⟩ := hfreq N hN
  refine ⟨m, hm, ?_⟩
  intro Ω _ P hC hcirc μ hGFF hμ
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hγQ : γ < lqgQ γ := by
    unfold lqgQ
    have hprod : 0 < (2 - γ) * (2 + γ) := mul_pos (by linarith) (by linarith)
    have hdiv : γ / 2 < 2 / γ := (div_lt_div_iff₀ (by norm_num) hγ).2 (by nlinarith)
    linarith
  obtain ⟨ν, hν⟩ := hEx Ω P γ γ hC hcirc hGFF hγ hγ₂ hγQ
  obtain ⟨S, hPS, hμS, hlocS, w, hw, hpos, hfin, ρ, hρ, shift, hshift,
    R, hroot, hac, hdom, hraw⟩ := hcomparison Ω P γ α₀ hC hcirc μ ν hGFF hμ
      hγ hγ₂ hα₀ hν
  exact hfreq Ω P hC hcirc μ ν hGFF hν (hEx Ω P γ 0 hC hcirc)
    (hW Ω P γ hC hcirc) (hAff Ω P hC hcirc) (hCC Ω P γ 0 hC hcirc)
    (hCC Ω P γ γ hC hcirc) (hGFF.aemeasurable_lqgMeasure hμ) S hPS hμS hlocS
    w hw hpos hfin ρ hρ shift hshift R hroot hac hdom hraw

#print axioms typicalPointManyGoodScalesStmt_of_ambientLaw

end HarmonicBalls
