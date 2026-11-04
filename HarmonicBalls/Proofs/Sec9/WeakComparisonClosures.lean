import HarmonicBalls.Proofs.Sec9.WeakUniquenessInclusions

/-! # Closures of subharmonic balls

The weak uniqueness sandwich identifies the closures and regularizations of
all subharmonic balls with a common centre and mass. The balls need not be
regular open.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- Sets sandwiched between the same set and the interior of its closure have
identical closures and regularizations. -/
theorem closure_eq_of_common_sandwich {X : Type*} [TopologicalSpace X]
    {C A B : Set X} (hCA : C ⊆ A) (hAC : A ⊆ interior (closure C))
    (hCB : C ⊆ B) (hBC : B ⊆ interior (closure C)) :
    closure A = closure B ∧ interior (closure A) = interior (closure B) := by
  have hA : closure A = closure C := Subset.antisymm
    (closure_minimal (hAC.trans interior_subset) isClosed_closure) (closure_mono hCA)
  have hB : closure B = closure C := Subset.antisymm
    (closure_minimal (hBC.trans interior_subset) isClosed_closure) (closure_mono hCB)
  exact ⟨hA.trans hB.symm, congrArg interior (hA.trans hB.symm)⟩

/-- On the weak-uniqueness and volume-growth events, two subharmonic balls
with common centre and mass have the same closure and regularization. -/
theorem ae_subharmonicBall_closure_eq_of_weak_uniqueness
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hweak : SubharmonicBallUniquenessWeakStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A B : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R → closure B ⊆ ball 0 R →
      IsSubharmonicBall (μ ω) A z → IsSubharmonicBall (μ ω) B z →
      μ ω A = ENNReal.ofReal t → μ ω B = ENNReal.ofReal t →
      closure A = closure B ∧ interior (closure A) = interior (closure B) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_subharmonicBall_sandwich_of_weak_uniqueness hI2 hweak
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hcompare
  intro A B z t R ht hR hz hAcl hBcl hA hB hAmass hBmass
  obtain ⟨hCA, hAC, -⟩ := hcompare A z t R ht hR hz hAcl hA hAmass
  obtain ⟨hCB, hBC, -⟩ := hcompare B z t R ht hR hz hBcl hB hBmass
  exact closure_eq_of_common_sandwich hCA hAC hCB hBC

/-- The same comparison inside the unit disk uses I2 and Lemmas 6.9 and 8.2,
without the staged affine-invariance and coordinate-change hypotheses. -/
theorem ae_subharmonicBall_closure_eq_inside_unit_disc
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h69 : OdometerHarmonicMeasureBoundStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A B : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R → closure B ⊆ ball 0 R →
      closure A ⊆ ball 0 1 → closure B ⊆ ball 0 1 →
      IsSubharmonicBall (μ ω) A z → IsSubharmonicBall (μ ω) B z →
      μ ω A = ENNReal.ofReal t → μ ω B = ENNReal.ofReal t →
      closure A = closure B ∧ interior (closure A) = interior (closure B) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_subharmonicBall_sandwich_inside_unit_disc hI2 h69 h82
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hcompare
  intro A B z t R ht hR hz hAcl hBcl hAcl1 hBcl1 hA hB hAmass hBmass
  obtain ⟨hCA, hAC, -⟩ := hcompare A z t R ht hR hz hAcl hAcl1 hA hAmass
  obtain ⟨hCB, hBC, -⟩ := hcompare B z t R ht hR hz hBcl hBcl1 hB hBmass
  exact closure_eq_of_common_sandwich hCA hAC hCB hBC

end HarmonicBalls
