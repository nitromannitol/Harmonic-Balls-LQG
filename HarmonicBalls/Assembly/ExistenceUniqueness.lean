import HarmonicBalls.Draft.Section5

/-! # Conditional assembly of Theorem 1.1

The bridge is explicit: the frozen existence statement supplies subharmonic balls,
while the introduction requires the enlarged harmonic test class.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter

universe u

/-- Assemble the introduction's existence and uniqueness statement from Section 5,
provided its regularized families satisfy the enlarged harmonic test class. -/
theorem existenceUniquenessHarmonicBallsStmt_of_sec5_of_bridge
    (h55 : ExistenceHarmonicBallsStmt.{u}) (h56 : UniquenessHarmonicBallsStmt.{u})
    (hbridge : ∀ (μ : Measure ℂ) (Λ : ℝ → Set ℂ) (z : ℂ),
      IsRegularizedClusterFamily μ Λ z → IsHarmonicBallFamily μ Λ z) :
    ExistenceUniquenessHarmonicBallsStmt.{u} := by
  classical
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  let Λhat : Ω → ℂ → ℝ → Set ℂ := fun ω z =>
    if h : ∃ A, IsRegularizedClusterFamily (μ ω) A z then Classical.choose h else fun _ => ∅
  have hhat : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λhat ω z) z := by
    filter_upwards [h55 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
    intro z
    dsimp only [Λhat]
    simpa only [dite_eq_left (hω z)] using Classical.choose_spec (hω z)
  filter_upwards [hhat, h56 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ Λhat hhat] with ω he hu
  intro z
  exact ⟨Λhat ω z, hbridge (μ ω) (Λhat ω z) z (he z), fun A hA => hu z A hA⟩

#print axioms existenceUniquenessHarmonicBallsStmt_of_sec5_of_bridge

end HarmonicBalls
