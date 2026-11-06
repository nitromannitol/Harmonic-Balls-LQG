import HarmonicBalls.Proofs.Sec6.EightAdicBlockFrequency
import HarmonicBalls.Proofs.Sec8.UniformSingularPhaseCertificate

/-! # Eight-adic phase frequency for the inserted reference field

The imported frequency argument uses Leonardo Bonanno's LatticeProb
formalization of the pointwise ergodic theorem and his annulus iteration.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal

universe u

/-- The Haar-phase reference certificate yields an eight-adic block count.
This is a statement under the inserted reference law, not a rooted-law transfer. -/
theorem exists_inserted_eightAdic_phase_blockFrequency
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
      ∀ N : ℕ, N₀ ≤ N →
      ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
        ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
          ({n : ℕ | n ∈ Icc (K + 1) (2 * K) ∧
            PhaseVeryGoodAnnulus (μ p.2) β ((8 : ℝ)⁻¹ ^ n) 0 N
              (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b
              C₁m C₁p C₂m C₂p c (torusPhase p.1) ∧
            AnnulusBallComparison (μ p.2) (3*n) 0 m}.ncard : ℝ) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨c, a, hc, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p,
    N₀, hN₀, m, hm, hcert⟩ :=
    hh.exists_uniform_singular_inserted_phaseFrequency_certificate hgrowth hfull
      hγ hγ2 hα hβ hb hμ hν hAff hCC₀ hCCα (ζ := ζ / 3) (by positivity)
  refine ⟨c, a, hc, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p,
    N₀, hN₀, m, hm, ?_⟩
  intro N hN
  obtain ⟨E, _, hEeq, hE⟩ := hcert N hN 1 (by norm_num)
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hEeq, hE] with p hp hpE
  have hfreq := (hp p.1).1 hpE
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.1 hfreq
  filter_upwards [eventually_ge_atTop K₀] with K hK
  have hcount := hK₀ (3*K) (by omega)
  have hthird := every_third_block_count (fun n =>
    PhaseVeryGoodAnnulus (μ p.2) β (dyadicScale n) 0 N
      (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b
      C₁m C₁p C₂m C₂p c (torusPhase p.1) ∧
    AnnulusBallComparison (μ p.2) n 0 m) K
  have hthird' :
      (({n : ℕ | n ∈ Icc (3*K+1) (6*K) ∧
        PhaseVeryGoodAnnulus (μ p.2) β (dyadicScale n) 0 N
          (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b
          C₁m C₁p C₂m C₂p c (torusPhase p.1) ∧
        AnnulusBallComparison (μ p.2) n 0 m}.ncard : ℕ) : ℝ) ≤
      (({n : ℕ | n ∈ Icc (K+1) (2*K) ∧
        PhaseVeryGoodAnnulus (μ p.2) β (dyadicScale (3*n)) 0 N
          (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b
          C₁m C₁p C₂m C₂p c (torusPhase p.1) ∧
        AnnulusBallComparison (μ p.2) (3*n) 0 m}.ncard : ℕ) : ℝ) + 2*(K : ℝ) := by
    exact_mod_cast hthird
  rw [show 2 * (3*K) = 6*K by omega] at hcount
  simp only [← inverse_eight_pow_eq_dyadicScale] at hthird'
  push_cast at hcount
  nlinarith

/-- One Haar-full set of phases works simultaneously for every admissible
value of the criterion-three starting level. -/
theorem exists_ae_phase_inserted_eightAdic_blockFrequency
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
      ∀ᵐ t ∂((volume : Measure PhaseCircle).prod volume),
      ∀ᵐ ω ∂P, ∀ N : ℕ, N₀ ≤ N →
        ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
          ({n : ℕ | n ∈ Icc (K + 1) (2 * K) ∧
            PhaseVeryGoodAnnulus (μ ω) β ((8 : ℝ)⁻¹ ^ n) 0 N
              (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b
              C₁m C₁p C₂m C₂p c (torusPhase t) ∧
            AnnulusBallComparison (μ ω) (3*n) 0 m}.ncard : ℝ) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨c, a, hc, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p,
    N₀, hN₀, m, hm, hcount⟩ :=
    exists_inserted_eightAdic_phase_blockFrequency hgrowth hfull hγ hγ2 hα hβ
      hb hh hμ hν hAff hCC₀ hCCα hζ
  refine ⟨c, a, hc, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p,
    N₀, hN₀, m, hm, ?_⟩
  have hs (N : ℕ) : ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      N₀ ≤ N → ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
        ({n : ℕ | n ∈ Icc (K + 1) (2 * K) ∧
          PhaseVeryGoodAnnulus (μ p.2) β ((8 : ℝ)⁻¹ ^ n) 0 N
            (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b
            C₁m C₁p C₂m C₂p c (torusPhase p.1) ∧
          AnnulusBallComparison (μ p.2) (3*n) 0 m}.ncard : ℝ) := by
    by_cases hN : N₀ ≤ N
    · filter_upwards [hcount N hN] with p hp _
      exact hp
    · exact Filter.Eventually.of_forall (fun _ hn => (hN hn).elim)
  exact Measure.ae_ae_of_ae_prod (ae_all_iff.mpr hs)

end HarmonicBalls.Section6
