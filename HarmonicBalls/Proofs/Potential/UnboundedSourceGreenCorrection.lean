import HarmonicBalls.Proofs.Sec6.GreenMono

/-!
# Green function comparison on domains with a harmonic minorant

A harmonic minorant of the Newtonian kernel supplies the finite lower bound
needed to compare Green functions without boundedness of the larger domain.
-/

namespace HarmonicBalls

open Set

/-- An admissible harmonic minorant makes the Green kernel nonnegative, even
when the domain is unbounded. -/
theorem greenFunction_nonneg_of_harmonicMinorant {U : Set ℂ} {z : ℂ}
    {h : ℂ → ℝ} (hh : IsHarmonicMinorant U (newtonKernelEReal z) h) (x : ℂ) :
    0 ≤ greenFunction U z x := by
  by_cases hz : z ∈ U
  · by_cases hx : x ∈ U
    · by_cases hzx : z = x
      · subst x
        simp [greenFunction]
      · rw [greenFunction, ite_eq_left ⟨hz, hx, hzx⟩]
        have hbot : greatestHarmonicMinorant U (newtonKernelEReal z) x ≠ ⊥ :=
          ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hh.le_greatestHarmonicMinorant x)
        have hle : greatestHarmonicMinorant U (newtonKernelEReal z) x ≤
            (newtonKernel z x : EReal) := by
          simpa [newtonKernelEReal, Ne.symm hzx] using
            (greatestHarmonicMinorant_le (O := U) (u := newtonKernelEReal z) hx)
        have hreal := EReal.toReal_le_toReal hle hbot (EReal.coe_ne_top _)
        simp only [EReal.toReal_coe] at hreal
        linarith
    · simp [greenFunction, hx]
  · simp [greenFunction, hz]

/-- A harmonic minorant on the larger domain implies domain monotonicity for
all evaluation points, without assuming that the larger domain is bounded. -/
theorem greenFunction_le_of_subset_of_harmonicMinorant {V U : Set ℂ}
    (hVU : V ⊆ U) {z : ℂ} {h : ℂ → ℝ}
    (hh : IsHarmonicMinorant U (newtonKernelEReal z) h) (x : ℂ) :
    greenFunction V z x ≤ greenFunction U z x := by
  by_cases hz : z ∈ V
  · by_cases hx : x ∈ V
    · by_cases hzx : z = x
      · subst x
        simp [greenFunction]
      · rw [greenFunction, ite_eq_left ⟨hz, hx, hzx⟩,
          greenFunction, ite_eq_left ⟨hVU hz, hVU hx, hzx⟩]
        have hI := Section6.greatestHarmonicMinorant_anti hVU (newtonKernelEReal z) x
        have hbot : greatestHarmonicMinorant U (newtonKernelEReal z) x ≠ ⊥ :=
          ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hh.le_greatestHarmonicMinorant x)
        have hN : newtonKernelEReal z x ≠ ⊤ := by
          simp [newtonKernelEReal, Ne.symm hzx]
        have htop : greatestHarmonicMinorant V (newtonKernelEReal z) x ≠ ⊤ :=
          ne_top_of_le_ne_top hN (greatestHarmonicMinorant_le hx)
        have hreal := EReal.toReal_le_toReal hI hbot htop
        linarith
    · rw [greenFunction_of_notMem_right hx]
      exact greenFunction_nonneg_of_harmonicMinorant hh x
  · rw [greenFunction_of_notMem_left hz]
    exact greenFunction_nonneg_of_harmonicMinorant hh x

end HarmonicBalls
