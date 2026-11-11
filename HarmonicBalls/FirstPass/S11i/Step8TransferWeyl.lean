import Mathlib
import HarmonicBalls.FirstPass.Frozen.S8c
import HarmonicBalls.Proposed.LQG

/-!
# Null-set transfer from the no-insertion LQG measure to the insertion measure (Step 8, Weyl transfer)

Generic piece of the physical hypothesis `hphys` of Step 8.
Let `lam` be the LQG measure of a whole-plane GFF with no insertion (`IsLQGMeasureOfField P γ 0 hcirc lam`, the measure
`μ_g` of the route) and `μ` the LQG measure with insertion `α₀` (`IsLQGMeasureOfField P γ α₀ hcirc μ`, the measure `μ_h`).
The frozen Weyl relation `LocalLQGInsertionWeylOffOrigin` (FirstPass/Frozen/S8c.lean:73) gives, almost surely,
`lam ω s = ∫_s |z|^{γ α₀} μ ω (dz)` for every measurable `s` with `0 ∉ s`. The density `|z|^{γ α₀}` is strictly positive
off the origin, so a set which is `lam`-null is `μ`-null away from `0`. Hence a property holding `lam`-almost everywhere
holds `μ`-almost everywhere, provided the origin is an atom-free point of `μ`.

The origin is removed by non-atomicity: `μ ω {0} = 0` almost surely. This is the Proposed input
`HarmonicBalls.LQGMeasureNonatomic` (Proposed/LQG.lean:77, Fact 2.1 I of Bou-Rabee-Gwynne, arXiv:2208.11795, p. 9) at
exponent `α₀`, pending source-check; the first theorem keeps `μ ω {0} = 0` as a separate hypothesis.
-/

open MeasureTheory
open scoped ENNReal

namespace HarmonicBalls.FirstPassS11iStep8Transfer

universe u

/-- **Null-set transfer off the origin (Step 8).** Let `hWeyl` be the frozen Weyl relation of the insertion off the origin
(`LocalLQGInsertionWeylOffOrigin`, FirstPass/Frozen/S8c.lean:73), `lam` the no-insertion LQG measure and `μ` the LQG measure
with insertion `α₀` of a whole-plane GFF. If `μ` has no atom at `0` almost surely (`hatom`), then a property `p ω z` which
holds `lam ω`-almost everywhere, almost surely, holds `μ ω`-almost everywhere, almost surely. -/
theorem ae_ae_of_ae_ae_noInsertion (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ lam : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hlam : IsLQGMeasureOfField P γ 0 hcirc lam)
    (hatom : ∀ᵐ ω ∂P, μ ω {0} = 0)
    (p : Ω → ℂ → Prop) (hp : ∀ᵐ ω ∂P, ∀ᵐ z ∂(lam ω), p ω z) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), p ω z := by
  filter_upwards [hWeyl Ω P γ α₀ hC hcirc μ lam hGFF hγ hγ2 hα hμ hlam, hatom, hp] with ω hW hA hPω
  rw [ae_iff] at hPω ⊢
  obtain ⟨M, hNM, hM, hMlam⟩ := exists_measurable_superset_of_null hPω
  have hS : MeasurableSet (M \ {0}) := hM.diff (measurableSet_singleton 0)
  have h0S : (0 : ℂ) ∉ M \ {0} := fun h => h.2 rfl
  have hlamS : lam ω (M \ {0}) = 0 := measure_mono_null Set.sdiff_subset hMlam
  have hint : ∫⁻ z in M \ {0}, ENNReal.ofReal (‖z‖ ^ (γ * α₀)) ∂(μ ω) = 0 :=
    (hW _ hS h0S).symm.trans hlamS
  have hmeas : Measurable fun z : ℂ => ENNReal.ofReal (‖z‖ ^ (γ * α₀)) :=
    ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)
  have hae := (setLIntegral_eq_zero_iff hS hmeas).mp hint
  have hpos : ∀ z : ℂ, z ≠ 0 → ENNReal.ofReal (‖z‖ ^ (γ * α₀)) ≠ 0 := fun z hz =>
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) _)).ne'
  have hnot : ∀ᵐ z ∂(μ ω), z ∉ M \ {0} :=
    hae.mono fun z hz hzS => hpos z hzS.2 (hz hzS)
  have hμS : μ ω (M \ {0}) = 0 := measure_eq_zero_iff_ae_notMem.mpr hnot
  have hsub : {z : ℂ | ¬ p ω z} ⊆ {0} ∪ (M \ {0}) := fun z hz => by
    by_cases h : z = 0
    · exact Or.inl h
    · exact Or.inr ⟨hNM hz, h⟩
  refine le_antisymm ((measure_mono hsub).trans ((measure_union_le _ _).trans ?_)) zero_le
  simp [hA, hμS]

/-- **Removal of the origin by non-atomicity (Step 8).** Same conclusion as `ae_ae_of_ae_ae_noInsertion`, with the
hypothesis `μ ω {0} = 0` a.s. discharged by the non-atomicity of the insertion LQG measure, `hNa`, which is the Proposed
input `HarmonicBalls.LQGMeasureNonatomic` at exponent `α₀` (Proposed/LQG.lean:77). -/
theorem ae_ae_of_ae_ae_noInsertion_of_nonatomic (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ lam : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hlam : IsLQGMeasureOfField P γ 0 hcirc lam)
    (hNa : HarmonicBalls.LQGMeasureNonatomic P γ α₀ hC hcirc)
    (p : Ω → ℂ → Prop) (hp : ∀ᵐ ω ∂P, ∀ᵐ z ∂(lam ω), p ω z) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), p ω z := by
  have hatom : ∀ᵐ ω ∂P, μ ω {0} = 0 := by
    filter_upwards [hNa hGFF hγ hγ2 hα μ hμ] with ω hω
    exact hω 0
  exact ae_ae_of_ae_ae_noInsertion hWeyl P γ α₀ hC hcirc μ lam hGFF hγ hγ2 hα hμ hlam hatom p hp

end HarmonicBalls.FirstPassS11iStep8Transfer
