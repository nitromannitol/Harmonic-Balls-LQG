import HarmonicBalls.Proofs.Sec8.PhaseTorus

/-! # helper: the torus phase of an iterate of the doubling map

The phase torus doubling `phaseTorusDouble` (Proofs/Sec8/PhaseTorus.lean:42) multiplies both circle coordinates by `2`.
Its `m`-fold iterate has torus phase `2^m` times the original, up to the outer lattice `(1/100)ℤ²` of the torus
representative `torusPhase` (Proofs/Sec8/PhaseTorus.lean). This is the lattice bookkeeping of the dilation identity of the
phase tail (`s8d_torusPhase_double_iterate`); it uses only `phaseCircleRep_double_sub` (the representative of `2x` minus
twice the representative of `x` is an integer). No new mathematics. -/

open Complex

namespace HarmonicBalls

/-- The `m`-fold doubling of a torus phase has representative `2^m` times the original one, up to `(1/100)ℤ²`. -/
theorem s8d_torusPhase_double_iterate (m : ℕ) (θ : PhaseTorus) :
    ∃ j k : ℤ, torusPhase (phaseTorusDouble^[m] θ) =
      (2 : ℂ) ^ m * torusPhase θ + ((j : ℂ) + (k : ℂ) * Complex.I) / 100 := by
  induction m with
  | zero => exact ⟨0, 0, by simp⟩
  | succ m ih =>
    obtain ⟨j, k, hjk⟩ := ih
    obtain ⟨j1, hj1⟩ := phaseCircleRep_double_sub ((phaseTorusDouble^[m] θ).1)
    obtain ⟨j2, hj2⟩ := phaseCircleRep_double_sub ((phaseTorusDouble^[m] θ).2)
    refine ⟨2 * j + j1, 2 * k + j2, ?_⟩
    rw [Function.iterate_succ_apply']
    unfold torusPhase at hjk ⊢
    have hx1 : (phaseCircleRep (2 • (phaseTorusDouble^[m] θ).1) : ℂ) =
        2 * (phaseCircleRep (phaseTorusDouble^[m] θ).1 : ℂ) + (j1 : ℂ) := by
      have h : phaseCircleRep (2 • (phaseTorusDouble^[m] θ).1) =
          2 * phaseCircleRep (phaseTorusDouble^[m] θ).1 + (j1 : ℝ) := by linarith
      rw [h]
      push_cast
      ring
    have hx2 : (phaseCircleRep (2 • (phaseTorusDouble^[m] θ).2) : ℂ) =
        2 * (phaseCircleRep (phaseTorusDouble^[m] θ).2 : ℂ) + (j2 : ℂ) := by
      have h : phaseCircleRep (2 • (phaseTorusDouble^[m] θ).2) =
          2 * phaseCircleRep (phaseTorusDouble^[m] θ).2 + (j2 : ℝ) := by linarith
      rw [h]
      push_cast
      ring
    simp only [phaseTorusDouble] at hx1 hx2 ⊢
    push_cast at hx1 hx2 hjk ⊢
    linear_combination (2 : ℂ) * hjk + hx1 / 100 + (hx2 / 100) * Complex.I


end HarmonicBalls
