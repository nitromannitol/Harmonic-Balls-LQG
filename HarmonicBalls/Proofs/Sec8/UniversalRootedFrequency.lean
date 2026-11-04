import HarmonicBalls.Proofs.Sec8.UniversalPhaseProbability
import HarmonicBalls.Proofs.Sec8.RootedSingularPhaseFrequency

/-! # Model-independent rooted good-scale frequency -/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

universe u

open Classical in
/-- A regular reference prevalence estimate fixes constants for the rooted
frequency estimate uniformly over singular reference realizations. The rooted
and recentered law comparisons remain explicit. -/
theorem exists_universal_rooted_singular_veryGoodComparableScaleFrequency
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    {Ξ₀ : Type u} [MeasurableSpace Ξ₀] (P₀ : Measure Ξ₀) {γ α β a b c : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ)
    (hβ : (2 + γ) ^ 2 / 2 < β) (ha : 0 < a) (hc : 0 < c)
    {hC₀ : Ξ₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ξ₀ → ℝ → ℂ → ℝ} {ν₀ : Ξ₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hν₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ ν₀)
    (hAff₀ : WholePlaneGFFAffineInvariance P₀ hC₀ hcirc₀)
    (hCC₀ : LQGMeasureCoordChange P₀ γ 0 hC₀ hcirc₀)
    (hprev : PolyHighProb P₀ fun ε => {ω | ∀ z ∈ Section6.prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (ν₀ ω) r z a b}.ncard : ℝ)})
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
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
          (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b C₁m C₁p C₂m C₂p c m K : ℝ) := by
  have hunit := measurableSet_isGoodAnnulus_of_pos 1 (by norm_num) 0 a b ha
  let δ : ℝ≥0∞ := ENNReal.ofReal (ζ / 8)
  have hδ : 0 < δ := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, hfail⟩ :=
    exists_universal_singular_phaseVeryGoodComparable_probability hgrowth hfull P₀
      hγ hγ₂ hα hβ hc h₀ hν₀ hAff₀ hCC₀ hprev hunit hδ
  have hδsum : δ + δ + δ + δ = ENNReal.ofReal (ζ / 2) := by
    dsimp only [δ]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have ha' : 0 < a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2) := by positivity
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, ?_⟩
  intro N hN Ξ _ P₁ hC hcirc μ₁ hGFF hμ₁ hEx hW hAff hCC hCCα
    Ω _ P _ μ hμ hloc S hPdom hμS hlocS w hw hpos hfin ρ hρ
    shift hshift R hrooted hac hdom F hF hlaw hcenter
  apply hGFF.ae_ae_rooted_veryGoodComparableScaleFrequency_of_singular_phase_bound hfull
    hγ hγ₂ hα hμ₁ hAff hCCα N _ b C₁m C₁p C₂m C₂p c m (ζ / 2) ζ ha'
    (by positivity) (by linarith) ?_ P hμ hloc S hPdom hμS hlocS w hw hpos hfin
    ρ hρ shift hshift R hrooted hac hdom F hF hlaw hcenter
  intro q
  simpa only [hδsum] using hfail N hN Ξ P₁ hC hcirc μ₁ hGFF hμ₁ hEx hW hAff hCC hCCα q

#print axioms exists_universal_rooted_singular_veryGoodComparableScaleFrequency

end HarmonicBalls
