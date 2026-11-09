import HarmonicBalls.FirstPass.S8d.ProfileTail
import HarmonicBalls.FirstPass.S8c.PhaseTail
import HarmonicBalls.FirstPass.Frozen.S8c
import HarmonicBalls.Draft.Section6
import HarmonicBalls.Draft.Section2
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.Proofs.Sec8.UniformAnnulusThreshold

/-! # FIRST-PASS helper (fp-S8d, owner n4): the phase-tail step `LocalPhaseTailStep`, from the frozen inputs

`LocalPhaseTailStep` (FirstPass/S8c/PhaseTail.lean:29) is the existential form of the phase tail of Lemma 8.2. Its
constants are taken from the probability statement `VeryGoodAnnulusProbabilityStmt` (Draft/Section6.lean:331) at the
probability `p = 1 - ζ'/4` with `ζ' = min ζ (1/2)` (the Omega-level `hbound` of the profile tail), and the annulus-ball
threshold `m` is uniform in the field (`exists_lqg_annulusBallComparison_uniform_threshold`). The singular phase
constants are the explicit factors `s8dSingK1`, `s8dSingK2` of `PhaseBound.lean`, with `K1/K2 = 2^(-3γ²) ≤ 1`, so the
final threshold `a · K1/K2` lies in `(0,1)`. The per-field proof is `s8d_phase_tail_omega` (ProfileTail.lean). No new
mathematics. -/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- The phase-tail step `LocalPhaseTailStep`, proved from the frozen profile inputs and the probability statement. -/
theorem s8d_localPhaseTailStep
    (hfull : LQGMeasureFullSupportStmt.{u}) (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    (hEx : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hL67 : VeryGoodAnnulusProbabilityStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u}) (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0}) (hU : RadonIntegralUniqueFrozen) :
    LocalPhaseTailStep.{u} := by
  intro γ hγ0 hγ2 βminus hβ
  obtain ⟨C₃, hC₃, hL⟩ := hL67
  refine ⟨C₃, hC₃, fun ζ hζ b hb => ?_⟩
  have hγQ : γ < lqgQ γ := by
    unfold lqgQ
    have hprod : 0 < (2 - γ) * (2 + γ) := mul_pos (by linarith) (by linarith)
    have hdiv : γ / 2 < 2 / γ := (div_lt_div_iff₀ (by norm_num) hγ0).2 (by nlinarith)
    linarith
  have hQ0 : (0 : ℝ) < lqgQ γ := by linarith
  obtain ⟨ζ', hζ'def⟩ : ∃ ζ' : ℝ, ζ' = min ζ (1 / 2) := ⟨_, rfl⟩
  have hζ'0 : 0 < ζ' := by rw [hζ'def]; exact lt_min hζ (by norm_num)
  have hζ'le : ζ' ≤ ζ := by rw [hζ'def]; exact min_le_left _ _
  have hζ'h : ζ' ≤ 1 / 2 := by rw [hζ'def]; exact min_le_right _ _
  have hζ'1 : ζ' < 1 := by linarith
  obtain ⟨a, ha, C₁m, C₁p, C₂m, C₂p, hC1m, hC1p, hC2m, hC2p, N₁, hN₁, hN⟩ :=
    hL γ 0 hγ0 hγ2 hQ0 βminus hβ b hb (1 - ζ' / 4) ⟨by linarith, by linarith⟩
  have hK1 : 0 < s8dSingK1 γ := by unfold s8dSingK1; positivity
  have hK2 : 0 < s8dSingK2 γ := by unfold s8dSingK2; positivity
  have hKle : s8dSingK1 γ / s8dSingK2 γ ≤ 1 := by
    have h1 : ((1 : ℝ) / 4) ^ (γ * γ) ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) (mul_self_nonneg γ)
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (γ * γ) := Real.one_le_rpow (by norm_num) (mul_self_nonneg γ)
    unfold s8dSingK1 s8dSingK2
    rw [inv_div_inv, div_le_one (by positivity)]
    exact h1.trans h2
  have ha1 : a * (s8dSingK1 γ / s8dSingK2 γ) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right ha.1.le hKle) ha.2
  refine ⟨a * (s8dSingK1 γ / s8dSingK2 γ), ⟨mul_pos ha.1 (div_pos hK1 hK2), ha1⟩,
    C₁m * (s8dSingK1 γ / s8dSingK2 γ), C₁p * (s8dSingK2 γ / s8dSingK1 γ),
    C₂m * (s8dSingK1 γ / s8dSingK2 γ), C₂p * (s8dSingK2 γ / s8dSingK1 γ),
    mul_pos hC1m (div_pos hK1 hK2), mul_pos hC1p (div_pos hK2 hK1),
    mul_pos hC2m (div_pos hK1 hK2), mul_pos hC2p (div_pos hK2 hK1),
    max N₁ 9, le_max_right _ _, fun N₀ hN₀ => ?_⟩
  have hN₀N₁ : N₁ ≤ N₀ := le_trans (le_max_left _ _) hN₀
  have hN₀9 : 9 ≤ N₀ := le_trans (le_max_right _ _) hN₀
  obtain ⟨m, hm, hmabc⟩ := exists_lqg_annulusBallComparison_uniform_threshold hfull γ γ hγ0 hγ2 hγQ
    (ENNReal.ofReal_pos.mpr (div_pos hζ'0 (by norm_num : (0 : ℝ) < 4)))
  refine ⟨m, hm.1, fun Ω _ P _ hC hcirc ν hGFF hν => ?_⟩
  obtain ⟨lam, hlam⟩ := hEx Ω P γ 0 hC hcirc hGFF hγ0 hγ2 hQ0
  have hW := hWeyl Ω P γ γ hC hcirc ν lam hGFF hγ0 hγ2 hγQ hν hlam
  have hABC : P {ω | ¬ AnnulusBallComparison (ν ω) 0 0 m} ≤ ENNReal.ofReal (ζ' / 4) :=
    hmabc Ω P hC hcirc ν hGFF hν (hAff Ω P hC hcirc) (hCC Ω P γ γ hC hcirc) 0
  have h67 : ∀ (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ : Ω' → Measure ℂ),
      IsWholePlaneGFF P' hC' hcirc' → IsLQGMeasureOfField P' γ 0 hcirc' μ →
      ∀ ρ : ℝ, 0 < ρ → ∀ x₀ : ℂ, ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2 * ρ)) →
        P' {ω | ¬ IsVeryGoodAnnulus (μ ω) βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃} ≤
          ENNReal.ofReal (1 - (1 - ζ' / 4)) :=
    fun Ω' _ P' hC' hcirc' μ hG hμ ρ hρ x₀ hx => hN N₀ hN₀N₁ Ω' P' hC' hcirc' μ hG hμ ρ hρ x₀ hx
  have hT := s8d_phase_tail_omega P hE1 hE3 hB hU γ hγ0 hγ2 hQ0 hγQ hC hcirc hGFF ν lam hν hlam hW
    (hAff Ω P hC hcirc) (hCC Ω P γ 0 hC hcirc) (hCC Ω P γ γ hC hcirc) βminus N₀ hN₀9 a b C₁m C₁p C₂m C₂p C₃
    m ζ' hζ'0 hζ'1 ha.1 hC1m hC1p hC2m hC2p h67 hABC
  filter_upwards [hT] with x hx
  filter_upwards [hx] with N hN'
  exact le_trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg N)) hN'

end HarmonicBalls
