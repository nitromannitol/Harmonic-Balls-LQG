import HarmonicBalls.Proofs.Sec8.SingularRootedFrequencyAssembly
import HarmonicBalls.Proofs.Sec6.SimultaneousPrevalenceZeroExistence

/-! # Rooted frequency from an existing regular measure

The weight relating the two existing limits follows from regularity of the
whole-plane GFF circle averages.
The rooted-law and recentering comparisons remain explicit. The imported
Section 8 development uses Leonardo Bonanno's `LatticeProb.Prob.Birkhoff`.
-/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

universe u

/-- Existing regular and singular LQG measures of the same whole-plane GFF
are related by the singular Weyl weight away from the origin. -/
theorem IsWholePlaneGFF.ae_singular_weight_of_existing_regular_measure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν) :
    ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ := by
  have hc0 : ∀ᵐ ω ∂P, ∀ k : ℕ,
      Continuous (fieldCircleAverage 0 (hcirc ω) (dyadicScale k)) :=
    ae_all_iff.mpr (fun k => hGFF.ae_continuous_fieldCircleAverage 0 (dyadicScale_pos k))
  filter_upwards [hμ, hν, hc0] with ω hμω hνω hcω
  have hW : ∀ f : ℂ → ℝ, Continuous f →
      IsLQGLimit γ (addCircleAverage (fieldCircleAverage 0 (hcirc ω)) f)
        ((ν ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))) :=
    fun f hf => Section6.isLQGLimit_addCircleAverage hνω hcω f hf
  exact restrict_compl_zero_eq_withDensity hμω hW

open Classical in
/-- An existing regular LQG measure supplies the logarithmic weight in the rooted
frequency assembly for an existing singular LQG measure. -/
theorem IsWholePlaneGFF.exists_ae_ae_rooted_singular_veryGoodComparableScaleFrequency_of_existing_regular_measure
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    {Ξ : Type u} [MeasurableSpace Ξ] {P₀ : Measure Ξ} {γ α β : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ξ → (ℂ → ℝ) → ℝ} {hcirc : Ξ → ℝ → ℂ → ℝ} {μ₀ ν : Ξ → Measure ℂ}
    {a b c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hGFF : IsWholePlaneGFF P₀ hC hcirc) (hμ₀ : IsLQGMeasureOfField P₀ γ α hcirc μ₀)
    (hν : IsLQGMeasureOfField P₀ γ 0 hcirc ν)
    (hAff : WholePlaneGFFAffineInvariance P₀ hC hcirc)
    (hCC₀ : LQGMeasureCoordChange P₀ γ 0 hC hcirc)
    (hCCα : LQGMeasureCoordChange P₀ γ α hC hcirc)
    (hprev : PolyHighProb P₀ fun ε => {ω | ∀ z ∈ Section6.prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (ν ω) r z a b}.ncard : ℝ)})
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
          (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b C₁m C₁p C₂m C₂p c m K : ℝ) := by
  have hweight := hGFF.ae_singular_weight_of_existing_regular_measure hμ₀ hν
  exact hGFF.exists_ae_ae_rooted_singular_veryGoodComparableScaleFrequency
    hgrowth hfull hγ hγ2 hα hβ ha hc hμ₀ hν hAff hCC₀ hCCα hweight hprev
    P hμ hloc S hPdom hμS hlocS w hw hpos hfin ρ hρ shift hshift R hrooted hac hdom
    F hF hlaw hcenter hζ

end HarmonicBalls
