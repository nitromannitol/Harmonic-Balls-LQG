import HarmonicBalls.Proofs.Sec8.CenteredMeasureLaw
import HarmonicBalls.Proofs.Sec8.UniformRootedPrevalenceAssembly

/-! # Rooted frequency from centered ambient measure laws

The imported ergodic theorem is due to Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization.
-/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

universe u

open Classical in
/-- The recentered measure-law hypothesis in the rooted frequency reduction
can be stated for ambient measures; measurable locally finite versions are constructed. -/
theorem exists_uniform_rooted_frequency_of_centered_measureLaw
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
        (∀ n, ∀ᵐ z ∂ρ n,
          (R n z).map (fun ω => (μ ω).map (fun v : ℂ => v - z)) ≪ P₁.map μ₁) →
      ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ K : ℕ in atTop,
        (1 - ζ) * (K : ℝ) ≤ (veryGoodComparableScaleCount (μ ω) β z N
          a b C₁m C₁p C₂m C₂p c m K : ℝ) := by
  obtain ⟨c, hc, hfreq⟩ := exists_uniform_rooted_frequency_of_subrange hgrowth hfull hsub
  refine ⟨c, hc, ?_⟩
  intro γ α β hγ hγ₂ hα hβ ζ hζ b hb
  obtain ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, hfreq⟩ :=
    hfreq γ α β hγ hγ₂ hα hβ ζ hζ b hb
  refine ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, ?_⟩
  intro N hN Ξ _ P₁ hC hcirc μ₁ hGFF hμ₁ hEx hW hAff hCC hCCα
    Ω _ P _ μ hμ S hPdom hμS hlocS w hw hpos hfin ρ hρ
    shift hshift R hrooted hac hdom hraw
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := hPdom.ae_le hlocS
  obtain ⟨F, hF, hcenter⟩ := exists_jointlyMeasurable_centeredMeasure S hμS hlocS
  have hFz (z : ℂ) : Measurable (fun ω => F (z, ω)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  apply hfreq N hN Ξ P₁ hC hcirc μ₁ hGFF hμ₁ hEx hW hAff hCC hCCα
    P hμ hloc S hPdom hμS hlocS w hw hpos hfin ρ hρ shift hshift R hrooted hac hdom
    (fun _ z ω => F (z, ω))
  · intro n
    exact Filter.Eventually.of_forall fun z => (hFz z).aemeasurable
  · intro U hU hUeq n
    filter_upwards [hdom n, hraw n] with z hdomz hrawz
    apply centeredSubtypeLaw_absolutelyContinuous_of_measureLaw (R n z) P₁ z
      (fun ω => F (z, ω)) (hFz z) U hU ?_ hUeq hrawz
    filter_upwards [hdomz.ae_le hcenter] with ω hω
    exact hω z
  · intro n
    filter_upwards [hdom n] with z hdomz
    filter_upwards [hdomz.ae_le hcenter] with ω hω
    exact hω z

#print axioms exists_uniform_rooted_frequency_of_centered_measureLaw

end HarmonicBalls
