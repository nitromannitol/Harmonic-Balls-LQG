import HarmonicBalls.FirstPass.S8d.TorusDoubleIterate
import HarmonicBalls.Proofs.Sec8.PhaseVeryGoodScaling
import HarmonicBalls.Proofs.Sec8.AnnulusComparisonStationarity

/-! # FIRST-PASS helper (fp-S8d, owner n4): the level-`n` torus good event under one dilation

For a measure `μ` on `ℂ` and a constant `c ∈ (0, ∞)`, let `μ' = c • μ.map (k⁻¹ • ·)` with `k = dyadicScale n`
(this is the shape of `normalizedPullbackMeasure`, Steps/Sec5/ScaleInvariance.lean:21). The level-`n` good predicate of
`μ` at the torus phase `θ` holds if and only if the level-`0` predicate of `μ'` at the doubled phase `2^n θ` holds.
The phase bookkeeping uses the iterate lattice lemma `s8d_torusPhase_double_iterate` and the outer-period invariance
`phaseVeryGoodAnnulus_outer_period`; the constant `c` is removed by `phaseVeryGoodAnnulus_smul` and
`annulusBallComparison_smul`. No new mathematics. -/

open MeasureTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

theorem s8d_dyadicScale_zero : dyadicScale 0 = 1 := by
  simp [dyadicScale]

theorem s8d_dyadicScale_mul_pow (n : ℕ) : ((dyadicScale n : ℝ) : ℂ) * (2 : ℂ) ^ n = 1 := by
  unfold dyadicScale
  push_cast
  rw [← mul_pow]
  norm_num

/-- The level-`n` good predicate of `μ` at `θ` is the level-`0` predicate of the dilated measure at `2^n θ`. -/
theorem s8d_torusGood_iterate_iff (μ μ' : Measure ℂ) (n : ℕ) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcT : c ≠ ∞)
    (hμ' : μ' = c • μ.map (fun z : ℂ => (dyadicScale n)⁻¹ • z))
    (θ : PhaseTorus) (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) :
    (PhaseVeryGoodAnnulus μ β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ (torusPhase θ) ∧
      AnnulusBallComparison μ n 0 m) ↔
    (PhaseVeryGoodAnnulus μ' β (dyadicScale 0) 0 N₀ a b C₁m C₁p C₂m C₂p C₃
        (torusPhase (phaseTorusDouble^[n] θ)) ∧
      AnnulusBallComparison μ' 0 0 m) := by
  have hk : 0 < dyadicScale n := dyadicScale_pos n
  obtain ⟨j, kk, hjk⟩ := s8d_torusPhase_double_iterate n θ
  have hlat : ((dyadicScale n / 100 : ℝ) : ℂ) * ((j : ℂ) + (kk : ℂ) * Complex.I) ∈
      Section6.scaledLattice (dyadicScale n / 100) := ⟨j, kk, rfl⟩
  have hphase : (dyadicScale n : ℝ) • torusPhase (phaseTorusDouble^[n] θ) =
      torusPhase θ + ((dyadicScale n / 100 : ℝ) : ℂ) * ((j : ℂ) + (kk : ℂ) * Complex.I) := by
    rw [hjk, Complex.real_smul]
    push_cast
    linear_combination (torusPhase θ) * s8d_dyadicScale_mul_pow n
  have hPVA1 : PhaseVeryGoodAnnulus μ β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ (torusPhase θ) ↔
      PhaseVeryGoodAnnulus μ β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃
        (torusPhase θ + ((dyadicScale n / 100 : ℝ) : ℂ) * ((j : ℂ) + (kk : ℂ) * Complex.I)) :=
    phaseVeryGoodAnnulus_outer_period μ β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ (torusPhase θ) hlat
  have hmapPVA := phaseVeryGoodAnnulus_map_inv_smul μ hk β 1 N₀ a b C₁m C₁p C₂m C₂p C₃
    (torusPhase (phaseTorusDouble^[n] θ))
  rw [mul_one] at hmapPVA
  have hP : PhaseVeryGoodAnnulus μ β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ (torusPhase θ) ↔
      PhaseVeryGoodAnnulus (c • μ.map (fun z : ℂ => (dyadicScale n)⁻¹ • z)) β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃
        (torusPhase (phaseTorusDouble^[n] θ)) := by
    rw [phaseVeryGoodAnnulus_smul _ β 1 0 N₀ a b C₁m C₁p C₂m C₂p C₃ _ hc0 hcT, hmapPVA, hphase]
    exact hPVA1
  have hA : AnnulusBallComparison μ n 0 m ↔
      AnnulusBallComparison (c • μ.map (fun z : ℂ => (dyadicScale n)⁻¹ • z)) 0 0 m := by
    rw [annulusBallComparison_smul _ 0 0 m hc0 hcT, annulusBallComparison_map_dyadic μ n 0 m, add_zero]
  subst hμ'
  rw [s8d_dyadicScale_zero]
  exact and_congr hP hA

end HarmonicBalls
