import HarmonicBalls.FirstPass.S11p.GreenMeasurable
import HarmonicBalls.Proofs.Sec11.ModConstPairingLaw

/-!
# N2 for Lemma 11.16: the exterior annular Green potential

Lemma N2 as used by `PinchSecondExteriorEventStep`
(`FirstPass/S11k.lean`): the supremum `SG(μ) = annulusGreenPotentialSup μ 0 3 6` has an almost-sure version that is
measurable for the uncompleted exterior σ-algebra `comap (localModConstPairings α₀ hC (closure W)ᶜ)` of S11k, and is
almost surely finite.

The two hypotheses are the exact remaining inputs:
* `hExt`: the masses of the open subsets of `𝔸_{3,6}` are almost surely measurable for the exterior σ-algebra. This is
  NOT yet established; see the report (it needs the normalisation of the whole-plane GFF, `h^ℂ_1(0) = 0`, to recover the
  constant from the zero-mean exterior pairings, and it is not yet a numbered input).
* `hFin`: almost-sure finiteness of `SG(μ)` (or `ae_annulusGreenPotentialSup_ne_top_of_lqgVolumeGrowth`
  in `Steps/Sec11/PinchGreenFinite.lean`, which needs the Draft statement `LQGVolumeGrowthAllScalesStmt`).
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- N2 (exterior version, for `PinchSecondExteriorEventStep`): given the exterior mass hypothesis `hExt` and the a.s.
finiteness `hFin`, the annular Green potential `SG(μ) = SG_{3,6}(0)` has an a.s. equal version that is measurable for
the uncompleted exterior σ-algebra and a.s. finite. -/
theorem exists_exterior_annulusGreenPotentialSup {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (W : Set ℂ) (μ : Ω → Measure ℂ)
    (hExt : ∀ U : Set ℂ, IsOpen U → U ⊆ annulus (0 : ℂ) 3 6 →
      ∃ g : Ω → ℝ≥0∞,
        Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] g ∧
          ∀ᵐ ω ∂P, μ ω U = g ω)
    (hFin : ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ⊤) :
    ∃ G : Ω → ℝ≥0∞,
      Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] G ∧
        (∀ᵐ ω ∂P, G ω = annulusGreenPotentialSup (μ ω) 0 3 6) ∧ ∀ᵐ ω ∂P, G ω ≠ ⊤ := by
  obtain ⟨G, hGm, hGa⟩ := exists_measurable_annulusGreenPotentialSup_version P
    (MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance) μ 0 3 6 hExt
  refine ⟨G, hGm, hGa, ?_⟩
  filter_upwards [hGa, hFin] with ω h1 h2
  rw [h1]
  exact h2

end HarmonicBalls

