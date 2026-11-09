import HarmonicBalls.FirstPass.S8d.ProfileVersion
import HarmonicBalls.FirstPass.S8d.DilationIdentity
import HarmonicBalls.FirstPass.S8d.ProfileHid
import HarmonicBalls.FirstPass.S8d.ProfileBound
import HarmonicBalls.FirstPass.S8d.PhaseBound
import HarmonicBalls.FirstPass.S8d.AeHid
import HarmonicBalls.FirstPass.Frozen.S8d
import HarmonicBalls.FirstPass.Frozen.S8c
import HarmonicBalls.Proofs.GFF.ContinuousCircleDilationMixing
import HarmonicBalls.Steps.Sec5.ScaleInvariance

/-! # FIRST-PASS helper (fp-S8d, owner n4): the eventual phase count of one Omega, from the profile space

For a whole-plane GFF `(P, hC, hcirc)` and its γ-LQG measure `ν` (insertion parameter `γ`), the profile `F` is measurable
(`ProfileVersion`), `Dec` is the frozen measurable profile map (E1), and the profile law `Q = P.map F` carries the dilation
`R = continuousCircleDilation`, which is measure preserving and ergodic (`ContinuousCircleDilationMixing`). The product
ergodicity (E3, universe 0) and the profile hid identity (`ProfileHid`) feed the Birkhoff-type tail of
`localPhaseTail_ae_of_dilation_ae` (`AeHid`), applied with the profile bound (`ProfileBound`, `PhaseBound`). The conclusion
transfers back to `Ω` through `Prod.map id F`. No new mathematics. -/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- A normalized pullback of a measure is a positive finite multiple of a pushforward under dilation. -/
theorem s8d_normalizedPullback_smul (γ α₀ k : ℝ) (h : ℝ → ℂ → ℝ) (μ : Measure ℂ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ normalizedPullbackMeasure γ α₀ k h μ = c • μ.map (fun x : ℂ => k⁻¹ • x) :=
  ⟨ENNReal.ofReal (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ h k 0)))⁻¹,
    (ENNReal.ofReal_pos.mpr (by positivity)).ne', ENNReal.ofReal_ne_top, rfl⟩

/-- The eventual phase count of `ν` at the origin along the Omega-level profile, for the constants of the profile
phase bound. -/
theorem s8d_phase_tail_omega {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hE1 : LQGMeasureOfProfileMeasurableFrozen.{u}) (hE3 : PhaseTorusDoublingProductErgodicFrozen.{0})
    (hB : BirkhoffPointwiseErgodic.{0}) (hU : RadonIntegralUniqueFrozen)
    (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : (0 : ℝ) < lqgQ γ) (hγQ : γ < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (ν lam : Ω → Measure ℂ) (hν : IsLQGMeasureOfField P γ γ hcirc ν)
    (hlam : IsLQGMeasureOfField P γ 0 hcirc lam)
    (hW : ∀ᵐ ω ∂P, ∀ s : Set ℂ, MeasurableSet s → (0 : ℂ) ∉ s →
      lam ω s = ∫⁻ z in s, ENNReal.ofReal (‖z‖ ^ (γ * γ)) ∂(ν ω))
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hCCγ : LQGMeasureCoordChange P γ γ hC hcirc)
    (βminus : ℝ) (N₀ : ℕ) (hN₀ : 9 ≤ N₀) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (ha : 0 < a) (hC₁m : 0 < C₁m) (hC₁p : 0 < C₁p) (hC₂m : 0 < C₂m) (hC₂p : 0 < C₂p)
    (h67 : ∀ (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ : Ω' → Measure ℂ),
      IsWholePlaneGFF P' hC' hcirc' → IsLQGMeasureOfField P' γ 0 hcirc' μ →
      ∀ ρ : ℝ, 0 < ρ → ∀ x₀ : ℂ, ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2 * ρ)) →
        P' {ω | ¬ IsVeryGoodAnnulus (μ ω) βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃} ≤
          ENNReal.ofReal (1 - (1 - ζ / 4)))
    (hABC : P {ω | ¬ AnnulusBallComparison (ν ω) 0 0 m} ≤ ENNReal.ofReal (ζ / 4)) :
    ∀ᵐ x ∂((volume : Measure ℂ).prod P), ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (ν x.2) βminus (dyadicScale n) 0 N₀
          (a * (s8dSingK1 γ / s8dSingK2 γ)) b
          (C₁m * (s8dSingK1 γ / s8dSingK2 γ)) (C₁p * (s8dSingK2 γ / s8dSingK1 γ))
          (C₂m * (s8dSingK1 γ / s8dSingK2 γ)) (C₂p * (s8dSingK2 γ / s8dSingK1 γ)) C₃ x.1 ∧
        AnnulusBallComparison (ν x.2) n 0 m}.ncard : ℝ) := by
  classical
  obtain ⟨F, hF, -, hversion⟩ := hGFF.exists_measurable_continuous_circle_version_univ
  obtain ⟨Dec, hDecM, hDecν, hDecLim⟩ := hE1 Ω P γ γ hC hcirc ν F hGFF hν hF hversion
  have : IsProbabilityMeasure (P.map F) :=
    ⟨by rw [Measure.map_apply hF MeasurableSet.univ, Set.preimage_univ]; exact measure_univ⟩
  have hloc : ∀ᵐ y ∂(P.map F), IsLocallyFiniteMeasure (Dec y) :=
    hDecLim.mono fun y h => h.isLocallyFiniteMeasure
  have hmp := hGFF.measurePreserving_continuousCircleDilation hF hversion
  have hergQ := hGFF.ergodic_continuousCircleDilation hF hversion
  have hergT := hE3 (C(CircleParameter, ℝ)) (P.map F) continuousCircleDilation hmp hergQ
  -- local finiteness of all iterates, almost surely
  have hfin : ∀ᵐ ω ∂P, ∀ k : ℕ, IsLocallyFiniteMeasure (Dec (continuousCircleDilation^[k] (F ω))) := by
    rw [ae_all_iff]
    intro k
    exact ae_of_ae_map hF.aemeasurable ((hmp.iterate k).quasiMeasurePreserving.ae hloc)
  -- the dilation identity in the form of the product-level hypothesis
  have hdil : ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      Dec (continuousCircleDilation^[k + 1] (F ω)) =
        c • (Dec (F ω)).map (fun z : ℂ => (dyadicScale (k + 1))⁻¹ • z) := by
    intro k
    have hds : dyadicScale (k + 1) = (1 / 2 : ℝ) ^ (k + 1) := by
      simp [dyadicScale, one_div]
    filter_upwards [s8d_dilation_identity_ae P γ hγ0 hγ2 hγQ hC hcirc hGFF ν hν hCCγ hU F hF hversion
      Dec hDecν hDecLim k] with ω hω
    rw [← hds] at hω
    obtain ⟨c, hc0, hcT, hcEq⟩ := s8d_normalizedPullback_smul γ γ (dyadicScale (k + 1)) (hcirc ω) (Dec (F ω))
    exact ⟨c, hc0, hcT, hω.trans hcEq⟩
  have hK : 0 < s8dSingK1 γ / s8dSingK2 γ := by
    unfold s8dSingK1 s8dSingK2
    positivity
  have hid := fun n : ℕ => s8d_torusGood_hid_ae P F hF Dec hDecM continuousCircleDilation hmp.measurable
    βminus N₀ (a * (s8dSingK1 γ / s8dSingK2 γ)) b
    (C₁m * (s8dSingK1 γ / s8dSingK2 γ)) (C₁p * (s8dSingK2 γ / s8dSingK1 γ))
    (C₂m * (s8dSingK1 γ / s8dSingK2 γ)) (C₂p * (s8dSingK2 γ / s8dSingK1 γ)) C₃ m
    (mul_pos ha hK) hfin hdil n
  -- the profile bound, from the Omega-level bound through the profile law
  have hΩ : ∀ q : ℂ, P {ω | ¬ (PhaseVeryGoodAnnulus (ν ω) βminus 1 0 N₀
        (a * (s8dSingK1 γ / s8dSingK2 γ)) b
        (C₁m * (s8dSingK1 γ / s8dSingK2 γ)) (C₁p * (s8dSingK2 γ / s8dSingK1 γ))
        (C₂m * (s8dSingK1 γ / s8dSingK2 γ)) (C₂p * (s8dSingK2 γ / s8dSingK1 γ)) C₃ q ∧
      AnnulusBallComparison (ν ω) 0 0 m)} ≤ ENNReal.ofReal (ζ / 2) := fun q =>
    s8d_phase_failure_all_q P γ hγ0 hγ2 hα hC hcirc hGFF ν lam hlam hW hAff hCC βminus N₀ hN₀ a b C₁m C₁p
      C₂m C₂p C₃ ζ hζ ha.le hC₁m hC₁p.le hC₂m hC₂p.le h67 m hABC q
  have hbPi : ∀ q : ℂ, (P.map F) {y | ¬ (PhaseVeryGoodAnnulus (Dec y) βminus 1 0 N₀
        (a * (s8dSingK1 γ / s8dSingK2 γ)) b
        (C₁m * (s8dSingK1 γ / s8dSingK2 γ)) (C₁p * (s8dSingK2 γ / s8dSingK1 γ))
        (C₂m * (s8dSingK1 γ / s8dSingK2 γ)) (C₂p * (s8dSingK2 γ / s8dSingK1 γ)) C₃ q ∧
      AnnulusBallComparison (Dec y) 0 0 m)} ≤ ENNReal.ofReal (ζ / 2) := fun q =>
    s8d_profile_hbound P F hF Dec hDecM ν hDecν hloc βminus N₀ _ b _ _ _ _ C₃ m ζ
      (mul_pos ha hK) q (hΩ q)
  have hPi := localPhaseTail_ae_of_dilation_ae hB (P.map F) Dec hDecM hloc βminus N₀
    (a * (s8dSingK1 γ / s8dSingK2 γ)) b
    (C₁m * (s8dSingK1 γ / s8dSingK2 γ)) (C₁p * (s8dSingK2 γ / s8dSingK1 γ))
    (C₂m * (s8dSingK1 γ / s8dSingK2 γ)) (C₂p * (s8dSingK2 γ / s8dSingK1 γ)) C₃ m ζ
    (mul_pos ha hK) hζ hζ1 hbPi continuousCircleDilation hmp hergT hid
  -- transfer to Omega through Prod.map id F
  have hΦ : Measurable (Prod.map (id : ℂ → ℂ) F) := measurable_id.prodMap hF
  have hmapEq : ((volume : Measure ℂ).prod P).map (Prod.map (id : ℂ → ℂ) F) =
      (volume : Measure ℂ).prod (P.map F) := by
    rw [← Measure.map_prod_map _ _ measurable_id hF, Measure.map_id]
  have hPi2 := hPi
  rw [← hmapEq] at hPi2
  have hTr := ae_of_ae_map hΦ.aemeasurable hPi2
  have hνx : ∀ᵐ x ∂((volume : Measure ℂ).prod P), ν x.2 = Dec (F x.2) :=
    (Measure.quasiMeasurePreserving_snd).ae hDecν
  filter_upwards [hTr, hνx] with x hx hνxx
  rw [hνxx]
  exact hx

end HarmonicBalls
