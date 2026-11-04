import HarmonicBalls.Proofs.Sec8.RootedPhaseFrequencyAssembly

/-! # Rooted phase frequency with a logarithmic singularity

The imported ergodic theorem is due to Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. The uniform one-scale estimate,
rooted law, and recentered law comparisons remain explicit hypotheses.
-/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

universe u

open Classical in
/-- A uniform one-scale phase bound for a logarithmically singular reference
field yields good-scale frequency at roots, under the displayed comparisons
of rooted and recentered laws. -/
theorem IsWholePlaneGFF.ae_ae_rooted_veryGoodComparableScaleFrequency_of_singular_phase_bound
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ξ : Type u} [MeasurableSpace Ξ] {P₀ : Measure Ξ} {γ α β : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ξ → (ℂ → ℝ) → ℝ} {hcirc : Ξ → ℝ → ℂ → ℝ} {μ₀ : Ξ → Measure ℂ}
    (hGFF : IsWholePlaneGFF P₀ hC hcirc) (hμ₀ : IsLQGMeasureOfField P₀ γ α hcirc μ₀)
    (hAff : WholePlaneGFFAffineInvariance P₀ hC hcirc)
    (hCC : LQGMeasureCoordChange P₀ γ α hC hcirc)
    (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ε ζ : ℝ) (ha : 0 < a)
    (hε : 0 ≤ ε) (hεζ : ε < ζ)
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
      (1 - ζ) * (K : ℝ) ≤ (veryGoodComparableScaleCount (μ ω) β z N₀
        a b C₁m C₁p C₂m C₂p C₃ m K : ℝ) := by
  let : IsProbabilityMeasure P₀ := hGFF.isProbabilityMeasure
  have hunit := measurableSet_isGoodAnnulus_of_pos 1 (by norm_num) 0 a b ha
  have hfreq := hGFF.ae_phaseVeryGoodComparable_blockFrequency_of_buffered_versions hfull
    hγ hγ2 hα hμ₀ hAff hCC
    (hGFF.exists_buffered_normalizedRestriction_of_fullSupport hfull hγ hγ2 hα hμ₀)
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m ε ζ hunit hε hεζ hfail
  obtain ⟨ν, hν, hνfinite, heq⟩ := Section6.exists_measurable_locallyFinite_rep
    (hGFF.aemeasurable_lqgMeasure hμ₀) (hμ₀.mono (fun _ h => h.isLocallyFiniteMeasure))
  let U : Ξ → {ν : Measure ℂ // IsLocallyFiniteMeasure ν} := fun ω => ⟨ν ω, hνfinite ω⟩
  have hU : Measurable U := hν.subtype_mk
  have hUeq : ∀ᵐ ω ∂P₀, (U ω).val = μ₀ ω := heq.symm
  have hphase : ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P₀),
      ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
        ({n : ℕ | n ∈ Icc (K + 1) (2 * K) ∧
          PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
          AnnulusBallComparison (U p.2).val n 0 m}.ncard : ℝ) := by
    filter_upwards [hfreq, Measure.quasiMeasurePreserving_snd.ae heq] with p hp he
    simpa only [U, ← he] using hp
  exact ae_ae_rooted_veryGoodComparableScaleFrequency_of_recentered_law P hμ hloc
    S hPdom hμS hlocS P₀ U hU β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit w hw hpos hfin
    ρ hρ shift hshift R hrooted hac hdom F hF (hlaw U hU hUeq) hcenter hphase

end HarmonicBalls
