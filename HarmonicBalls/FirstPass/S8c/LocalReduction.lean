import HarmonicBalls.FirstPass.S8c.Measurability
import HarmonicBalls.FirstPass.S8c.JointTransfer
import HarmonicBalls.FirstPass.Frozen.S8c

/-! # Joint local reduction of Lemma 8.2 (FIRST-PASS, fp-S8c-8-2-local)

The root observation `localRootObservation μ j` lies almost surely in a measurable set `G` of
(recentred normalised measures), under the normalised rooted law `P ⊗ₘ κ` restricted to `{z ∈ D_j}`,
provided the reference observation lies almost surely in `G` under `(volume|D_j) ⊗ P`.
The only inputs are the FROZEN joint domination `LocalRootedFieldMeasureDomination` (L1), the measurable set `G`,
and the phase-sensitive tail `hL3` on the reference side (the named open step L3). Measurability of the
observation maps is proved in `Measurability.lean`.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- Joint local transfer: the root-side observation is a.e. in `G` when the reference-side one is, given the
frozen joint domination. -/
theorem localRoot_ae_mem_of_localDomination (hL1 : LocalRootedFieldMeasureDomination.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ ν lam : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hν : IsLQGMeasureOfField P γ γ hcirc ν)
    (hlam : IsLQGMeasureOfField P γ 0 hcirc lam) (j : ℕ) (hj : 1 ≤ j)
    {G : Set (ℂ × Measure ℂ)} (hG : MeasurableSet G)
    (hL3 : ∀ᵐ x ∂((volume.restrict (localDomain j)).prod P), localReferenceObservation ν j x ∈ G) :
    ∀ᵐ x ∂((P ⊗ₘ localRootKernel P lam (hGFF.aemeasurable_lqgMeasure hlam)).restrict
        (Prod.snd ⁻¹' localDomain j)),
      localRootObservation μ j x ∈ G := by
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hLD := hL1 Ω P γ α₀ hC hcirc μ ν lam hGFF hγ0 hγ2 hα hμ hν hlam j hj
  have hμA : AEMeasurable μ P := hGFF.aemeasurable_lqgMeasure hμ
  have hνA : AEMeasurable ν P := hGFF.aemeasurable_lqgMeasure hν
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) :=
    hμ.mono fun _ h => h.isLocallyFiniteMeasure
  have hO := aemeasurable_localRootObservation P
    (localRootKernel P lam (hGFF.aemeasurable_lqgMeasure hlam)) μ hμA hloc j (localDomain j)
  have hV := aemeasurable_localReferenceObservation P ν hνA j (localDomain j)
  exact ae_mem_of_map_absolutelyContinuous _ _ P _ _ hO hV hLD hG hL3

#print axioms localRoot_ae_mem_of_localDomination

end HarmonicBalls
