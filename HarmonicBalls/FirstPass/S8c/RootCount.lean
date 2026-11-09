import HarmonicBalls.FirstPass.S8c.LocalReduction
import HarmonicBalls.FirstPass.S8c.Locality
import HarmonicBalls.FirstPass.Frozen.S8c
import HarmonicBalls.Draft.Section2

/-! # Root-side eventual very-good count on the local domain (FIRST-PASS fp-S8c-8-2-local, step (iii), part 1)

For the normalised rooted law restricted to `{z ∈ D_j}`, almost surely the very-good count at the root `z`
eventually dominates `(1 - ζ) N`. Inputs: the FROZEN local joint domination `LocalRootedFieldMeasureDomination` (L1),
the measurability of the recentred good set given the unit good-annulus hypothesis `hunit` (L2, named), the named
phase tail `hL3` on the reference side (L3, open), and the full support of the LQG measure
(`LQGMeasureFullSupportStmt`, Draft/Section2.lean:109), which gives positivity of the observed ball masses.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

theorem localRadius_pos {j : ℕ} (hj : 1 ≤ j) : 0 < localRadius j := by
  unfold localRadius
  have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  positivity

/-- Root-side eventual count on the local domain, almost surely under the normalised rooted law restricted to
`{z ∈ D_j}`. -/
theorem localRoot_eventually_count_ae (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ ν lam : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hν : IsLQGMeasureOfField P γ γ hcirc ν)
    (hlam : IsLQGMeasureOfField P γ 0 hcirc lam) (j : ℕ) (hj : 1 ≤ j)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {ν' : Measure ℂ | IsGoodAnnulus ν' 1 0 a b})
    (hL3 : ∀ᵐ x ∂((volume.restrict (localDomain j)).prod P),
      localReferenceObservation ν j x ∈ recentredGoodSet β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ) :
    ∀ᵐ x ∂((P ⊗ₘ localRootKernel P lam (hGFF.aemeasurable_lqgMeasure hlam)).restrict
        (Prod.snd ⁻¹' localDomain j)),
      ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
        (veryGoodComparableScaleCount (μ x.1) β x.2 N₀ a b C₁m C₁p C₂m C₂p C₃ m N : ℝ) := by
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hG : MeasurableSet (recentredGoodSet β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ) :=
    measurableSet_recentredGoodSet β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit
  have hmem := localRoot_ae_mem_of_localDomination hL1 P γ α₀ hC hcirc μ ν lam hGFF hγ0 hγ2 hα
    hμ hν hlam j hj hG hL3
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) :=
    hμ.mono fun _ h => h.isLocallyFiniteMeasure
  -- positivity of every ball mass of μ(ω), almost surely, from full support
  have hfullμ : ∀ᵐ ω ∂P, ∀ z : ℂ, 0 < μ ω (ball z (localRadius j / 2)) := by
    filter_upwards [hfull γ α₀ hγ0 hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
    intro z
    have hr := localRadius_pos hj
    exact hω _ isOpen_ball (nonempty_ball.mpr (by positivity))
  have hpos : ∀ᵐ x ∂(P ⊗ₘ localRootKernel P lam (hGFF.aemeasurable_lqgMeasure hlam)), 0 < μ x.1 (ball x.2 (localRadius j / 2)) := by
    filter_upwards [ae_fst_of_ae_compProd P (localRootKernel P lam (hGFF.aemeasurable_lqgMeasure hlam)) hfullμ] with x hx
    exact hx x.2
  have hlocX : ∀ᵐ x ∂(P ⊗ₘ localRootKernel P lam (hGFF.aemeasurable_lqgMeasure hlam)), IsLocallyFiniteMeasure (μ x.1) :=
    ae_fst_of_ae_compProd P (localRootKernel P lam (hGFF.aemeasurable_lqgMeasure hlam)) hloc
  filter_upwards [hmem, ae_restrict_of_ae (s := Prod.snd ⁻¹' localDomain j) hpos,
    ae_restrict_of_ae (s := Prod.snd ⁻¹' localDomain j) hlocX] with x hx hxpos hxloc
  have := hxloc
  exact (veryGoodComparableScaleCount_eventually_iff_recentredGood (μ x.1) x.2 (localRadius j)
    (localRadius_pos hj) hxpos β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ).2 hx

#print axioms localRoot_eventually_count_ae

end HarmonicBalls
