import HarmonicBalls.FirstPass.S8d.SingularPhase
import HarmonicBalls.FirstPass.S8d.TranslatedDensity
import HarmonicBalls.Proofs.Sec8.PhaseTorus

/-! # FIRST-PASS helper (fp-S8d, owner n4): the phase failure bound for every phase

The phase failure bound `hbound` of the phase tail (`PhaseTailConvert.lean`, `localPhaseTail_ae_of_dilation_ae` in
`AeHid.lean`) asks, for every complex phase `q`, that the phase-shifted very-good event at the origin together with the
annulus-ball comparison fails with probability at most `ζ/2`.

* The phase event depends only on the torus class of `q` (`phaseVeryGoodAnnulus_torusPhase_ofComplex`,
  Proofs/Sec8/PhaseTorus.lean:138), and the representative `torusPhase (phaseTorusOfComplex q)` lies in `[0,1/100)²`
  (`s8d_torusPhase_norm_le`), so it is within the range `1/5` of `singular_translated_failure_le`.
* The singular translated failure event has probability at most `ζ/4` (`singular_translated_failure_le`,
  `p = 1 - ζ/4`), and the annulus-ball comparison fails with probability at most `ζ/4` for the chosen `m`
  (hypothesis `hABC`; supplied uniformly by `exists_lqg_annulusBallComparison_uniform_threshold`,
  Proofs/Sec8/UniformAnnulusThreshold.lean:14).

No new mathematics: periodicity, the translation identity, and the union bound. -/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- The singular and regular density constants `k₁ = (2^{γ²})⁻¹`, `k₂ = ((1/4)^{γ²})⁻¹`
(TranslatedDensity.lean, `translated_density_bounds`). -/
noncomputable abbrev s8dSingK1 (γ : ℝ) : ℝ := ((2 : ℝ) ^ (γ * γ))⁻¹

/-- See `s8dSingK1`. -/
noncomputable abbrev s8dSingK2 (γ : ℝ) : ℝ := (((1 : ℝ) / 4) ^ (γ * γ))⁻¹

/-- The representative of a phase-circle point lies in `[0, 1)`. -/
theorem s8d_phaseCircleRep_mem (x : PhaseCircle) : 0 ≤ phaseCircleRep x ∧ phaseCircleRep x < 1 := by
  have h := ((AddCircle.measurableEquivIco (1 : ℝ) 0) x).2
  unfold phaseCircleRep
  simpa using h

/-- The torus representative of a complex phase has modulus at most `1/5`. -/
theorem s8d_torusPhase_norm_le (p : PhaseTorus) : ‖torusPhase p‖ ≤ 1 / 5 := by
  unfold torusPhase
  have h1 := s8d_phaseCircleRep_mem p.1
  have h2 := s8d_phaseCircleRep_mem p.2
  have hA : ‖((phaseCircleRep p.1 / 100 : ℝ) : ℂ)‖ ≤ 1 / 100 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hB : ‖((phaseCircleRep p.2 / 100 : ℝ) : ℂ) * Complex.I‖ ≤ 1 / 100 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    linarith
  calc ‖((phaseCircleRep p.1 / 100 : ℝ) : ℂ) + ((phaseCircleRep p.2 / 100 : ℝ) : ℂ) * Complex.I‖
      ≤ ‖((phaseCircleRep p.1 / 100 : ℝ) : ℂ)‖ + ‖((phaseCircleRep p.2 / 100 : ℝ) : ℂ) * Complex.I‖ :=
        norm_add_le _ _
    _ ≤ 1 / 100 + 1 / 100 := add_le_add hA hB
    _ ≤ 1 / 5 := by norm_num

/-- The phase-shifted very-good event at the origin depends on the phase only through its torus class. -/
theorem s8d_phaseVeryGood_torus_invariant (η : Measure ℂ) (β : ℝ) (N : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (q : ℂ) :
    PhaseVeryGoodAnnulus η β 1 0 N a b C₁m C₁p C₂m C₂p C₃ q ↔
      PhaseVeryGoodAnnulus η β 1 0 N a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phaseTorusOfComplex q)) := by
  have h0 : dyadicScale 0 = 1 := by norm_num [dyadicScale]
  have h := phaseVeryGoodAnnulus_torusPhase_ofComplex η β 0 N a b C₁m C₁p C₂m C₂p C₃ q
  rw [h0] at h
  exact h.symm

/-- The phase failure bound for every phase `q`: the phase-shifted very-good event at the origin together with the
annulus-ball comparison at `m` fails with probability at most `ζ/2`. -/
theorem s8d_phase_failure_all_q {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : (0 : ℝ) < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (ν lam : Ω → Measure ℂ) (hlam : IsLQGMeasureOfField P γ 0 hcirc lam)
    (hW : ∀ᵐ ω ∂P, ∀ s : Set ℂ, MeasurableSet s → (0 : ℂ) ∉ s →
      lam ω s = ∫⁻ z in s, ENNReal.ofReal (‖z‖ ^ (γ * γ)) ∂(ν ω))
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (βminus : ℝ) (N₀ : ℕ) (hN₀ : 9 ≤ N₀) (a b C₁m C₁p C₂m C₂p C₃ ζ : ℝ) (hζ : 0 < ζ)
    (ha : 0 ≤ a) (hC₁m : 0 < C₁m) (hC₁p : 0 ≤ C₁p) (hC₂m : 0 < C₂m) (hC₂p : 0 ≤ C₂p)
    (h67 : ∀ (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ : Ω' → Measure ℂ),
      IsWholePlaneGFF P' hC' hcirc' → IsLQGMeasureOfField P' γ 0 hcirc' μ →
      ∀ ρ : ℝ, 0 < ρ → ∀ x₀ : ℂ, ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2 * ρ)) →
        P' {ω | ¬ IsVeryGoodAnnulus (μ ω) βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃} ≤
          ENNReal.ofReal (1 - (1 - ζ / 4)))
    (m : ℝ) (hABC : P {ω | ¬ AnnulusBallComparison (ν ω) 0 0 m} ≤ ENNReal.ofReal (ζ / 4))
    (q : ℂ) :
    P {ω | ¬ (PhaseVeryGoodAnnulus (ν ω) βminus 1 0 N₀
        (a * (s8dSingK1 γ / s8dSingK2 γ)) b
        (C₁m * (s8dSingK1 γ / s8dSingK2 γ)) (C₁p * (s8dSingK2 γ / s8dSingK1 γ))
        (C₂m * (s8dSingK1 γ / s8dSingK2 γ)) (C₂p * (s8dSingK2 γ / s8dSingK1 γ)) C₃ q ∧
      AnnulusBallComparison (ν ω) 0 0 m)} ≤ ENNReal.ofReal (ζ / 2) := by
  set q' := torusPhase (phaseTorusOfComplex q) with hq'def
  have hq' : ‖q'‖ ≤ 1 / 5 := s8d_torusPhase_norm_le _
  have hsing := singular_translated_failure_le P γ hγ0 hγ2 hα hC hcirc hGFF ν lam hlam hW hAff hCC
    βminus N₀ hN₀ a b C₁m C₁p C₂m C₂p C₃ (1 - ζ / 4) ha hC₁m hC₁p hC₂m hC₂p h67 q' hq'
  rw [show (1 : ℝ) - (1 - ζ / 4) = ζ / 4 by ring] at hsing
  have hset : ∀ ω, (PhaseVeryGoodAnnulus (ν ω) βminus 1 0 N₀
        (a * (s8dSingK1 γ / s8dSingK2 γ)) b
        (C₁m * (s8dSingK1 γ / s8dSingK2 γ)) (C₁p * (s8dSingK2 γ / s8dSingK1 γ))
        (C₂m * (s8dSingK1 γ / s8dSingK2 γ)) (C₂p * (s8dSingK2 γ / s8dSingK1 γ)) C₃ q ↔
      IsVeryGoodAnnulus ((ν ω).map (fun w : ℂ => w - q')) βminus 1 (-q') N₀
        (a * (s8dSingK1 γ / s8dSingK2 γ)) b
        (C₁m * (s8dSingK1 γ / s8dSingK2 γ)) (C₁p * (s8dSingK2 γ / s8dSingK1 γ))
        (C₂m * (s8dSingK1 γ / s8dSingK2 γ)) (C₂p * (s8dSingK2 γ / s8dSingK1 γ)) C₃) := by
    intro ω
    rw [s8d_phaseVeryGood_torus_invariant (ν ω) βminus N₀ _ _ _ _ _ _ _ q,
      phaseVeryGood_iff_isVeryGood_translate]
  have hset' : {ω | ¬ (PhaseVeryGoodAnnulus (ν ω) βminus 1 0 N₀
        (a * (s8dSingK1 γ / s8dSingK2 γ)) b
        (C₁m * (s8dSingK1 γ / s8dSingK2 γ)) (C₁p * (s8dSingK2 γ / s8dSingK1 γ))
        (C₂m * (s8dSingK1 γ / s8dSingK2 γ)) (C₂p * (s8dSingK2 γ / s8dSingK1 γ)) C₃ q ∧
      AnnulusBallComparison (ν ω) 0 0 m)} ⊆
      {ω | ¬ IsVeryGoodAnnulus ((ν ω).map (fun w : ℂ => w - q')) βminus 1 (-q') N₀
        (a * (s8dSingK1 γ / s8dSingK2 γ)) b
        (C₁m * (s8dSingK1 γ / s8dSingK2 γ)) (C₁p * (s8dSingK2 γ / s8dSingK1 γ))
        (C₂m * (s8dSingK1 γ / s8dSingK2 γ)) (C₂p * (s8dSingK2 γ / s8dSingK1 γ)) C₃} ∪
      {ω | ¬ AnnulusBallComparison (ν ω) 0 0 m} := by
    intro ω hω
    rcases not_and_or.1 hω with h | h
    · exact Or.inl fun hv => h ((hset ω).2 hv)
    · exact Or.inr h
  calc P {ω | ¬ (PhaseVeryGoodAnnulus (ν ω) βminus 1 0 N₀
        (a * (s8dSingK1 γ / s8dSingK2 γ)) b
        (C₁m * (s8dSingK1 γ / s8dSingK2 γ)) (C₁p * (s8dSingK2 γ / s8dSingK1 γ))
        (C₂m * (s8dSingK1 γ / s8dSingK2 γ)) (C₂p * (s8dSingK2 γ / s8dSingK1 γ)) C₃ q ∧
      AnnulusBallComparison (ν ω) 0 0 m)}
      ≤ P ({ω | ¬ IsVeryGoodAnnulus ((ν ω).map (fun w : ℂ => w - q')) βminus 1 (-q') N₀
        (a * (s8dSingK1 γ / s8dSingK2 γ)) b
        (C₁m * (s8dSingK1 γ / s8dSingK2 γ)) (C₁p * (s8dSingK2 γ / s8dSingK1 γ))
        (C₂m * (s8dSingK1 γ / s8dSingK2 γ)) (C₂p * (s8dSingK2 γ / s8dSingK1 γ)) C₃} ∪
        {ω | ¬ AnnulusBallComparison (ν ω) 0 0 m}) := measure_mono hset'
    _ ≤ P {ω | ¬ IsVeryGoodAnnulus ((ν ω).map (fun w : ℂ => w - q')) βminus 1 (-q') N₀
        (a * (s8dSingK1 γ / s8dSingK2 γ)) b
        (C₁m * (s8dSingK1 γ / s8dSingK2 γ)) (C₁p * (s8dSingK2 γ / s8dSingK1 γ))
        (C₂m * (s8dSingK1 γ / s8dSingK2 γ)) (C₂p * (s8dSingK2 γ / s8dSingK1 γ)) C₃}
        + P {ω | ¬ AnnulusBallComparison (ν ω) 0 0 m} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ζ / 4) + ENNReal.ofReal (ζ / 4) := add_le_add hsing hABC
    _ = ENNReal.ofReal (ζ / 2) := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1
      ring

#print axioms s8d_phase_failure_all_q

end HarmonicBalls
