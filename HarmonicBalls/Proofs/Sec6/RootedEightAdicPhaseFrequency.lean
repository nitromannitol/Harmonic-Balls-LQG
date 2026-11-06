import HarmonicBalls.Proofs.Sec8.RootedSingularPhaseFrequency
import HarmonicBalls.Proofs.Sec6.EightAdicBlockFrequency
import HarmonicBalls.Proofs.Sec8.SingularRootedFrequencyExistingMeasure
import HarmonicBalls.Proofs.Sec6.SevenAdicFineSupportPrevalence

/-! # Eight-adic frequency at sampled roots

The imported ergodic and annulus iteration arguments use Leonardo Bonanno's
LatticeProb formalizations. Rooted and recentered law comparisons remain explicit.
-/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

universe u

open Classical in
/-- Eight-adic block frequency at measure-typical roots, conditional on the
rooted and recentered law comparisons used by the dyadic theorem. -/
theorem IsWholePlaneGFF.ae_ae_rooted_eightAdic_frequency_of_singular_phase_bound
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ξ : Type u} [MeasurableSpace Ξ] {P₀ : Measure Ξ} {γ α β : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ξ → (ℂ → ℝ) → ℝ} {hcirc : Ξ → ℝ → ℂ → ℝ} {μ₀ : Ξ → Measure ℂ}
    (hGFF : IsWholePlaneGFF P₀ hC hcirc) (hμ₀ : IsLQGMeasureOfField P₀ γ α hcirc μ₀)
    (hAff : WholePlaneGFFAffineInvariance P₀ hC hcirc)
    (hCC : LQGMeasureCoordChange P₀ γ α hC hcirc)
    (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ε ζ : ℝ) (ha : 0 < a)
    (hε : 0 ≤ ε) (hεζ : ε < ζ / 3)
    (hfail : ∀ phase : ℂ, P₀ {ω | ¬
      (PhaseVeryGoodAnnulus (μ₀ ω) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ phase ∧
        AnnulusBallComparison (μ₀ ω) 0 0 m)} ≤ ENNReal.ofReal ε)
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
      (μ ω).map (fun v : ℂ => v - z) = (F n z ω).val) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ K : ℕ in atTop,
      (1 - ζ) * (K : ℝ) ≤
        ({n : ℕ | n ∈ Icc (K+1) (2*K) ∧
          IsVeryGoodAnnulus (μ ω) β ((8 : ℝ)⁻¹ ^ n) z N₀
            a b C₁m C₁p C₂m C₂p C₃ ∧
          AnnulusBallComparison (μ ω) (3*n) z m}.ncard : ℝ) := by
  have hfreq := hGFF.ae_ae_rooted_veryGoodComparableScaleFrequency_of_singular_phase_bound
    hfull hγ hγ2 hα hμ₀ hAff hCC N₀ a b C₁m C₁p C₂m C₂p C₃ m ε (ζ / 3)
    ha hε hεζ hfail P hμ hloc S hPdom hμS hlocS w hw hpos hfin ρ hρ
    shift hshift R hrooted hac hdom F hF hlaw hcenter
  filter_upwards [hfreq] with ω hω
  filter_upwards [hω] with z hz
  have h := Section6.eventually_eightAdic_comparable_block_count_of_dyadic
    (μ ω) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m (ζ / 3) hz
  filter_upwards [h] with K hK
  convert hK using 1
  ring

open Classical in
/-- Eight-adic rooted frequency from same-field regular measure prevalence. -/
theorem IsWholePlaneGFF.exists_ae_ae_rooted_eightAdic_frequency_of_existing_regular_measure
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    {Ξ : Type u} [MeasurableSpace Ξ] {P₀ : Measure Ξ} {γ α β : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ξ → (ℂ → ℝ) → ℝ} {hcirc : Ξ → ℝ → ℂ → ℝ} {μ₀ ν : Ξ → Measure ℂ}
    {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
    (hGFF : IsWholePlaneGFF P₀ hC hcirc) (hμ₀ : IsLQGMeasureOfField P₀ γ α hcirc μ₀)
    (hν : IsLQGMeasureOfField P₀ γ 0 hcirc ν)
    (hAff : WholePlaneGFFAffineInvariance P₀ hC hcirc)
    (hCC₀ : LQGMeasureCoordChange P₀ γ 0 hC hcirc)
    (hCCα : LQGMeasureCoordChange P₀ γ α hC hcirc)
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
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ c : ℝ, 0 < c ∧
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∃ m ∈ Ioo (0 : ℝ) 1,
      ∀ N : ℕ, N₀ ≤ N → ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ K : ℕ in atTop,
        (1 - ζ) * (K : ℝ) ≤
          ({n : ℕ | n ∈ Icc (K+1) (2*K) ∧
            IsVeryGoodAnnulus (μ ω) β ((8 : ℝ)⁻¹ ^ n) z N
              (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b C₁m C₁p C₂m C₂p c ∧
            AnnulusBallComparison (μ ω) (3*n) z m}.ncard : ℝ) := by
  obtain ⟨c, hc, hsub⟩ := Section6.goodAnnuliSubRangeStep_of_volumeGrowth_fineSupport hgrowth
  obtain ⟨a, ha, hprev⟩ := hsub γ hγ hγ2 b hb
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, hfreq⟩ :=
    hGFF.exists_ae_ae_rooted_singular_veryGoodComparableScaleFrequency_of_existing_regular_measure
      hgrowth hfull hγ hγ2 hα hβ ha.1 hc hμ₀ hν hAff hCC₀ hCCα
      (hprev Ξ P₀ hC hcirc ν hGFF hν)
      P hμ hloc S hPdom hμS hlocS w hw hpos hfin ρ hρ shift hshift R hrooted hac hdom
      F hF hlaw hcenter (ζ := ζ / 3) (by positivity)
  refine ⟨a, ha, c, hc, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, ?_⟩
  intro N hN
  filter_upwards [hfreq N hN] with ω hω
  filter_upwards [hω] with z hz
  have h := Section6.eventually_eightAdic_comparable_block_count_of_dyadic
    (μ ω) β z N (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b
    C₁m C₁p C₂m C₂p c m (ζ / 3) hz
  filter_upwards [h] with K hK
  convert hK using 1
  ring

end HarmonicBalls
