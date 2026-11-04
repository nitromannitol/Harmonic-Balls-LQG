import HarmonicBalls.Proofs.Sec8.PhaseReferenceMeasure
import HarmonicBalls.Proofs.Sec8.GoodEventPointPolarity

/-! # Rooted frequency from phase frequency

The imported ergodic theorem is due to Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. All rooted and recentered law
comparisons remain explicit hypotheses.
-/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

universe u

open Classical in
/-- Uniform one-scale estimates give good-scale frequency at random-measure
roots whenever the displayed rooted and recentered law comparisons hold. The
reference field may live on a different probability space from the rooted
measure. -/
theorem IsWholePlaneGFF.exists_ae_ae_rooted_veryGoodComparableScaleFrequency
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    {Ξ : Type u} [MeasurableSpace Ξ] {P₀ : Measure Ξ} {γ β : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ξ → (ℂ → ℝ) → ℝ} {hcirc : Ξ → ℝ → ℂ → ℝ} {μ₀ : Ξ → Measure ℂ}
    {a b c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hGFF : IsWholePlaneGFF P₀ hC hcirc) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc μ₀)
    (hAff : WholePlaneGFFAffineInvariance P₀ hC hcirc)
    (hCC : LQGMeasureCoordChange P₀ γ 0 hC hcirc)
    (hprev : PolyHighProb P₀ fun ε => {ω | ∀ z ∈ Section6.prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ₀ ω) r z a b}.ncard : ℝ)})
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    {μ : Ω → Measure ℂ} (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (S : Measure Ω) (hPdom : P ≪ S)
    (hμS : AEMeasurable μ S) (hlocS : ∀ᵐ ω ∂S, IsLocallyFiniteMeasure (μ ω))
    (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hpos : ∀ z, w z ≠ 0) (hfin : ∀ z, w z ≠ ∞)
    (ρ : ℕ → Measure ℂ) (hρ : ∀ n, ρ n ≪ volume)
    (shift : ℕ → ℂ × Ω → Ω) (hshift : ∀ n, Measurable (shift n))
    (R : ℕ → ℂ → Measure Ω)
    (hrooted : ∀ n, P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
      (weightedLocalization w n) (measurableSet_weightedLocalization hw n) w hw) ≪
        shiftedRootReferenceLaw (ρ n) P (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, P.map (fun ω => shift n (z, ω)) ≪ R n z)
    (hdom : ∀ n, ∀ᵐ z ∂ρ n, R n z ≪ S)
    (F : ℕ → ℂ → Ω → {ν : Measure ℂ // IsLocallyFiniteMeasure ν})
    (hF : ∀ n, ∀ᵐ z ∂ρ n, AEMeasurable (F n z) (R n z))
    (hlaw : ∀ U : Ξ → {ν : Measure ℂ // IsLocallyFiniteMeasure ν}, Measurable U →
      (∀ᵐ ω ∂P₀, (U ω).val = μ₀ ω) →
      ∀ n, ∀ᵐ z ∂ρ n, (R n z).map (F n z) ≪ P₀.map U)
    (hcenter : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ ω ∂(R n z),
      (μ ω).map (fun v : ℂ => v - z) = (F n z ω).val)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∃ m ∈ Ioo (0 : ℝ) 1,
      ∀ N : ℕ, N₀ ≤ N → ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ K : ℕ in atTop,
        (1 - ζ) * (K : ℝ) ≤ (veryGoodComparableScaleCount (μ ω) β z N
          a b C₁m C₁p C₂m C₂p c m K : ℝ) := by
  let : IsProbabilityMeasure P₀ := hGFF.isProbabilityMeasure
  have hunit := measurableSet_isGoodAnnulus_of_pos 1 (by norm_num) 0 a b ha
  obtain ⟨U, hU, hUeq, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, hphase⟩ :=
    hGFF.exists_phaseFrequency_reference_measure hgrowth hfull hγ hγ2 hβ hc hμ₀
      hAff hCC hprev hunit hζ
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, ?_⟩
  intro N hN
  exact ae_ae_rooted_veryGoodComparableScaleFrequency_of_recentered_law P hμ hloc
    S hPdom hμS hlocS P₀ U hU β N a b C₁m C₁p C₂m C₂p c m ζ hunit w hw hpos hfin
    ρ hρ shift hshift R hrooted hac hdom F hF (hlaw U hU hUeq) hcenter (hphase N hN)

end HarmonicBalls
