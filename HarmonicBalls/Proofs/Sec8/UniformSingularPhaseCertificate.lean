import HarmonicBalls.Proofs.Sec8.SingularPhaseProbability
import HarmonicBalls.Proofs.Sec8.InsertedPhaseFrequencyEvent
import HarmonicBalls.Proofs.Sec8.GoodEventPointPolarity
import HarmonicBalls.Proofs.Sec8.SingularRootedFrequencyExistingMeasure
import HarmonicBalls.Proofs.Sec6.SevenAdicFineSupportPrevalence

/-! # Singular reference phase-frequency certificates

The imported frequency argument uses Leonardo Bonanno's LatticeProb
formalization of the pointwise ergodic theorem. -/

noncomputable section

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

universe u

/-- Uniform singular one-scale estimates yield a measurable certificate for
Haar-phase block frequency of the origin-inserted reference field,
with parameters independent of the observation radius. -/
theorem IsWholePlaneGFF.exists_uniform_singular_inserted_phaseFrequency_certificate
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α β : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC₀ : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hCCα : LQGMeasureCoordChange P γ α hC hcirc)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ c a : ℝ, 0 < c ∧ a ∈ Ioo (0 : ℝ) 1 ∧
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∃ m ∈ Ioo (0 : ℝ) 1,
      ∀ N : ℕ, N₀ ≤ N → ∀ R : ℝ, 0 < R →
      ∃ E : Set (PhaseTorus × (Section6.LocalTest (ball 0 R) → ℝ)),
        MeasurableSet E ∧
        (∀ᵐ ω ∂P, ∀ t : PhaseTorus,
          ((t, fun φ : Section6.LocalTest (ball 0 R) =>
            hC ω φ.1.1 + ∫ x, φ.1.1 x * (-α * Real.log ‖x‖)) ∈ E ↔
          ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
            ({n : ℕ | n ∈ Icc (K + 1) (2 * K) ∧
              PhaseVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N
                (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b
                C₁m C₁p C₂m C₂p c (torusPhase t) ∧
              AnnulusBallComparison (μ ω) n 0 m}.ncard : ℝ))) ∧
        ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
          (p.1, fun φ : Section6.LocalTest (ball 0 R) =>
            hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (-α * Real.log ‖x‖)) ∈ E := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨c, hc, hprev⟩ := Section6.goodAnnuliSubRangeStep_of_volumeGrowth_fineSupport hgrowth
  obtain ⟨a, ha, hprev⟩ := hprev γ hγ hγ2 b hb
  have hweight := hh.ae_singular_weight_of_existing_regular_measure hμ hν
  have hunit := measurableSet_isGoodAnnulus_of_pos 1 (by norm_num) 0 a b ha.1
  let δ : ℝ≥0∞ := ENNReal.ofReal (ζ / 8)
  have hδ : 0 < δ := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, hfail⟩ :=
    exists_singular_phaseVeryGoodComparable_probability_of_weight hgrowth hfull P
      hγ hγ2 hα hβ hc hh hμ hν hAff hCC₀ hCCα hweight (hprev Ω P hC hcirc ν hh hν) hunit hδ
  have hδsum : δ + δ + δ + δ = ENNReal.ofReal (ζ / 2) := by
    dsimp only [δ]
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have ha0 : 0 < a := ha.1
  have ha' : 0 < a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2) := by positivity
  have hunit' := measurableSet_isGoodAnnulus_of_pos 1 (by norm_num) 0 _ b ha'
  have hpos := ae_referenceBall_pos_finite P μ
    (hfull γ α hγ hγ2 hα Ω P hC hcirc μ hh hμ)
    (hμ.mono (fun _ h => h.isLocallyFiniteMeasure))
  refine ⟨c, a, hc, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, ?_⟩
  intro N hN R hR
  obtain ⟨E, hE, hEeq⟩ := hh.exists_inserted_phaseFrequency_event hμ hpos hR
    β N _ b C₁m C₁p C₂m C₂p c m ζ hunit'
  have hfreq := hh.ae_phaseVeryGoodComparable_blockFrequency_of_buffered_versions hfull
    hγ hγ2 hα hμ hAff hCCα
    (hh.exists_buffered_normalizedRestriction_of_fullSupport hfull hγ hγ2 hα hμ)
    β N _ b C₁m C₁p C₂m C₂p c m (ζ / 2) ζ hunit'
    (by positivity) (by linarith) (fun phase => by simpa only [hδsum] using hfail N hN phase)
  refine ⟨E, hE, hEeq, ?_⟩
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hEeq, hfreq] with p hp hf
  exact (hp p.1).2 hf

end HarmonicBalls
