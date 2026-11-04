import HarmonicBalls.Proofs.Sec8.BufferedNormalizedRestriction
import HarmonicBalls.Proofs.Sec8.PhaseTorusLawTransfer

/-! # A locally finite reference law for phase frequency

The imported ergodic theorem is due to Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization.
-/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

universe u

open Classical in
/-- The phase-frequency estimate admits a measurable, everywhere locally
finite reference measure, suitable for comparisons of recentered laws. -/
theorem IsWholePlaneGFF.exists_phaseFrequency_reference_measure
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ β : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {a b c : ℝ} (hc : 0 < c)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hprev : PolyHighProb P fun ε => {ω | ∀ z ∈ Section6.prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ U : Ω → {ν : Measure ℂ // IsLocallyFiniteMeasure ν},
      Measurable U ∧ (∀ᵐ ω ∂P, (U ω).val = μ ω) ∧
      ∃ C₁m C₁p C₂m C₂p : ℝ,
        0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
        ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∃ m ∈ Ioo (0 : ℝ) 1,
        ∀ N : ℕ, N₀ ≤ N →
        ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
          ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
            ({n : ℕ | n ∈ Icc (K + 1) (2 * K) ∧
              PhaseVeryGoodAnnulus (U p.2).val β (dyadicScale n) 0 N
                a b C₁m C₁p C₂m C₂p c (torusPhase p.1) ∧
              AnnulusBallComparison (U p.2).val n 0 m}.ncard : ℝ) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨ν, hν, hνfinite, heq⟩ := Section6.exists_measurable_locallyFinite_rep
    (hGFF.aemeasurable_lqgMeasure hμ) (hμ.mono (fun _ h => h.isLocallyFiniteMeasure))
  let U : Ω → {ν : Measure ℂ // IsLocallyFiniteMeasure ν} := fun ω => ⟨ν ω, hνfinite ω⟩
  refine ⟨U, hν.subtype_mk, heq.symm, ?_⟩
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, hfreq⟩ :=
    hGFF.exists_ae_phaseVeryGoodComparable_blockFrequency_of_locality hgrowth hfull
      hγ hγ2 hβ hc hμ hAff hCC hprev hunit hζ
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, ?_⟩
  intro N hN
  filter_upwards [hfreq N hN, Measure.quasiMeasurePreserving_snd.ae heq] with p hp he
  simpa only [U, ← he] using hp

end HarmonicBalls
