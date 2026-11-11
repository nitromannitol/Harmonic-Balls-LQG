import HarmonicBalls.FirstPass.S8c.Frequency
import HarmonicBalls.FirstPass.S8c.PhaseMean
import HarmonicBalls.FirstPass.Frozen.S8c
import HarmonicBalls.Proofs.Sec8.PhaseTorus

/-! # The torus-indexed phase tail from the Birkhoff theorem (step (vi) of LocalPhaseTailStep)

On the phase torus times the field space, the doubling map `(θ, ω) ↦ (2θ, R ω)` (`phaseTorusDouble` of
Proofs/Sec8/PhaseTorus.lean, and a measure-preserving dilation `R` of the field space) carries the level-`n` good
events to the level-`0` good event: `Gn n = T^[n]⁻¹' G` (G-8-2 section 3, eq. (10)). If the level-0 event has
probability at least `1 - ζ/2` on every phase section, the Birkhoff ergodic theorem for an ergodic `T` gives, almost
surely on the torus times the field space, eventually `(1 - ζ) N` good levels in each block `[N+1, 2N]`.
This is the torus form of the phase tail (`hphase` of Proofs/Sec8/PhaseTorusLebesgue.lean). The two named inputs are
the ergodicity of `T` (G-8-2 section 3, mixing of the GFF dilation) and the identity (10).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- The product of the phase probability measure on the torus with the field law `P`. -/
noncomputable abbrev phaseTorusFieldMeasure {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) :
    Measure (PhaseTorus × Ω) :=
  ((volume : Measure PhaseCircle).prod (volume : Measure PhaseCircle)).prod P

/-- The torus-indexed block frequency of good levels, almost surely, from Birkhoff's theorem. -/
theorem ae_frequency_of_torus_dilation (hB : BirkhoffPointwiseErgodic.{u}) {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (R : Ω → Ω)
    (hR : MeasurePreserving R P P)
    (hergT : Ergodic (fun p : PhaseTorus × Ω => (phaseTorusDouble p.1, R p.2))
      (phaseTorusFieldMeasure P))
    (G : Set (PhaseTorus × Ω)) (hG : MeasurableSet G) (ζ : ℝ) (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (hsec : ∀ θ : PhaseTorus, P (Prod.mk θ ⁻¹' G)ᶜ ≤ ENNReal.ofReal (ζ / 2))
    (Gn : ℕ → Set (PhaseTorus × Ω))
    (hid : ∀ n : ℕ, Gn n = (fun p : PhaseTorus × Ω => (phaseTorusDouble p.1, R p.2))^[n] ⁻¹' G) :
    ∀ᵐ p ∂(phaseTorusFieldMeasure P), ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤
        ∑ n ∈ Finset.Icc (N + 1) (2 * N), (Gn n).indicator (1 : PhaseTorus × Ω → ℝ) p := by
  set T : PhaseTorus × Ω → PhaseTorus × Ω := fun p => (phaseTorusDouble p.1, R p.2) with hT_def
  have hT : MeasurePreserving T (phaseTorusFieldMeasure P) (phaseTorusFieldMeasure P) :=
    measurePreserving_phaseTorusDouble.prod hR
  have hmean : 1 - ζ < ∫ z, G.indicator (1 : PhaseTorus × Ω → ℝ) z ∂(phaseTorusFieldMeasure P) := by
    have h := integral_indicator_prod_ge ((volume : Measure PhaseCircle).prod (volume : Measure PhaseCircle))
      P hG (ζ / 2) (by linarith) (by linarith) hsec
    linarith
  have hf : Measurable (G.indicator (1 : PhaseTorus × Ω → ℝ)) := measurable_one.indicator hG
  have hbd : ∀ y, |G.indicator (1 : PhaseTorus × Ω → ℝ) y| ≤ 1 := by
    intro y
    by_cases hy : y ∈ G
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  have key := ae_eventually_frequency_of_birkhoff hB (phaseTorusFieldMeasure P) T
    (G.indicator (1 : PhaseTorus × Ω → ℝ)) ζ hT hergT hf hbd hmean
  filter_upwards [key] with p hp
  have hsum : ∀ n : ℕ, (Gn n).indicator (1 : PhaseTorus × Ω → ℝ) p =
      G.indicator (1 : PhaseTorus × Ω → ℝ) (T^[n] p) := by
    intro n
    rw [hid n]
    by_cases hy : T^[n] p ∈ G
    · simp [Set.indicator_of_mem hy, Set.indicator_of_mem (show p ∈ T^[n] ⁻¹' G from hy)]
    · simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem (show p ∉ T^[n] ⁻¹' G from hy)]
  simp only [hsum]
  exact hp


end HarmonicBalls
