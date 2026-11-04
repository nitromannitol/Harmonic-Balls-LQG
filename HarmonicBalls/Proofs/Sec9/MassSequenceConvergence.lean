import HarmonicBalls.Proofs.Sec9.MassContinuity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Pointwise convergence along summable mass sequences

The symmetric-difference mass identity upgrades summable mass gaps to
almost-everywhere eventual agreement of membership, by Borel–Cantelli.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped symmDiff

/-- Summable symmetric-difference measures imply eventual agreement of
membership almost everywhere. No measurability of the sets is required. -/
theorem ae_eventually_mem_iff_of_tsum_measure_symmDiff_ne_top
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (A : ℕ → Set X) (B : Set X)
    (hsum : (∑' n, μ (A n ∆ B)) ≠ ⊤) :
    ∀ᵐ x ∂μ, ∀ᶠ n in atTop, (x ∈ A n ↔ x ∈ B) := by
  filter_upwards [ae_eventually_notMem hsum] with x hx
  filter_upwards [hx] with n hn
  simp only [mem_symmDiff, not_or, not_and, not_not] at hn
  exact ⟨hn.1, hn.2⟩

universe u

/-- Almost surely, simultaneously for every centre and sequence of subharmonic
balls inside the unit disc, summable gaps between their real masses and the
real mass of a comparison ball imply eventual pointwise agreement for
almost every point with respect to the LQG measure. -/
theorem ae_subharmonicBall_eventually_mem_iff_of_summable_mass_gaps
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : ℕ → Set ℂ) (B : Set ℂ) (z : ℂ),
      (∀ n, closure (A n) ⊆ ball 0 1 ∧ IsSubharmonicBall (μ ω) (A n) z) →
      closure B ⊆ ball 0 1 → IsSubharmonicBall (μ ω) B z →
      (∑' n, ENNReal.ofReal |((μ ω) (A n)).toReal - ((μ ω) B).toReal|) ≠ ⊤ →
      ∀ᵐ x ∂(μ ω), ∀ᶠ n in atTop, (x ∈ A n ↔ x ∈ B) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_subharmonicBall_measureReal_symmDiff_inside_unit_disc hI2 h82
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hidentity
  intro A B z hA hBcl hB hsum
  apply ae_eventually_mem_iff_of_tsum_measure_symmDiff_ne_top
  have heq : ∀ n, μ ω (A n ∆ B) =
      ENNReal.ofReal |((μ ω) (A n)).toReal - ((μ ω) B).toReal| := by
    intro n
    rw [← hidentity (A n) B z (hA n).1 hBcl (hA n).2 hB]
    exact (ENNReal.ofReal_toReal (measure_symmDiff_ne_top
      (ne_of_lt (hA n).2.2.2.2.1) (ne_of_lt hB.2.2.2.1))).symm
  simpa only [heq] using hsum

end HarmonicBalls
