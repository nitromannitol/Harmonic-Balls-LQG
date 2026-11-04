import HarmonicBalls.Proofs.Sec8.ObservedBallRootTransfer
import HarmonicBalls.Proofs.Sec8.PhaseLocalLawTransfer
import Mathlib.MeasureTheory.Measure.Support

/-! # Rooted transfer through a local observable

The phase-frequency argument uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. The local decoder and the observed
rooted-law domination remain explicit hypotheses.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

/-- At almost every point of a locally finite measure, every fixed positive
radius ball has finite nonzero mass after recentering. -/
theorem ae_recentered_ball_mass_ne_zero_ne_top (μ : Measure ℂ)
    [IsLocallyFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ z ∂μ, μ.map (fun v : ℂ => v - z) (ball 0 ε) ≠ 0 ∧
      μ.map (fun v : ℂ => v - z) (ball 0 ε) ≠ ∞ := by
  filter_upwards [Measure.support_mem_ae (μ := μ)] with z hz
  have heq : μ.map (fun v : ℂ => v - z) (ball 0 ε) = μ (ball z ε) := by
    rw [Measure.map_apply (by fun_prop) measurableSet_ball]
    congr 1
    ext v
    simp [Metric.mem_ball, dist_eq_norm]
  rw [heq]
  exact ⟨(Measure.mem_support_iff_forall z).1 hz _ (ball_mem_nhds z hε) |>.ne',
    measure_ball_lt_top.ne⟩

/-- A decoder for a normalized neighborhood of the recentered measure is
sufficient for observable rooted transfer of very-good-scale frequency. -/
theorem ae_ae_veryGoodComparableScaleFrequency_of_observed_local_ball_rooted_law
    {Ω Ξ F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace F]
    (P : Measure Ω) [SFinite P] (R : Measure Ξ) [SFinite R]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hpos : ∀ z, w z ≠ 0) (hfin : ∀ z, w z ≠ ∞)
    (observe : Ω → F) (hobserve : Measurable observe)
    (decode : F × ℂ → {ν : Measure ℂ // IsLocallyFiniteMeasure ν})
    (hdecode : Measurable decode) (ε : ℝ) (hε : 0 < ε)
    (hdecodeeq : ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω,
      (decode (observe ω, z)).val =
        normalizedRestriction ((μ ω).map (fun v : ℂ => v - z)) (ball 0 ε))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    (ρ : ℕ → Measure ℂ) (shift : ℕ → ℂ × Ξ → F)
    (hshift : ∀ n, Measurable (shift n)) (Q : ℕ → ℂ → Measure F)
    (hrooted : ∀ n : ℕ,
      (P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
        (ball 0 ((n : ℝ) + 1)) measurableSet_ball (fun _ => 1) measurable_const)).map
          (fun x => (observe x.1, x.2)) ≪ shiftedRootReferenceLaw (ρ n) R (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, R.map (fun ω => shift n (z, ω)) ≪ Q n z)
    (hfixed : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ f ∂Q n z, ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤
        ({k : ℕ | k ∈ Icc (N + 1) (2 * N) ∧
          PhaseVeryGoodAnnulus (decode (f, z)).val β (dyadicScale k) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phaseTorusOfComplex (-z))) ∧
          AnnulusBallComparison (decode (f, z)).val k 0 m}.ncard : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ (veryGoodComparableScaleCount (μ ω) β z N₀
        a b C₁m C₁p C₂m C₂p C₃ m N : ℝ) := by
  let p : F × ℂ → Prop := fun x => ∀ᶠ N : ℕ in atTop,
    (1 - ζ) * (N : ℝ) ≤
      ({k : ℕ | k ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (decode x).val β (dyadicScale k) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phaseTorusOfComplex (-x.2))) ∧
        AnnulusBallComparison (decode x).val k 0 m}.ncard : ℝ)
  have hp : MeasurableSet {x : F × ℂ | p x} := by
    have hm := measurableSet_phaseTorus_blockFrequency β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit
    have hf : Measurable (fun x : F × ℂ => (phaseTorusOfComplex (-x.2), decode x)) :=
      (measurable_phaseTorusOfComplex.comp
        (measurable_snd : Measurable (Prod.snd : F × ℂ → ℂ)).neg).prodMk hdecode
    have hpre := hm.preimage hf
    simp only [Set.preimage_ofPred_eq] at hpre
    exact hpre
  have ht := ae_ae_of_observed_unweighted_ball_rooted_law P R μ hμ hloc w hw hpos hfin
    observe hobserve ρ shift hshift Q hp hrooted hac hfixed
  filter_upwards [ht, hloc, hdecodeeq] with ω htω hlocω hdω
  let : IsLocallyFiniteMeasure (μ ω) := hlocω
  have hmω := ae_recentered_ball_mass_ne_zero_ne_top (μ ω) hε
  filter_upwards [htω, hmω, hdω] with z hz hm hd
  have hz' := (phaseVeryGoodComparable_blockFrequency_iff_normalizedRestriction
    ((μ ω).map (fun v : ℂ => v - z)) hε hm.1 hm.2 β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ
    (fun _ => torusPhase (phaseTorusOfComplex (-z)))).2 (by simpa only [p, hd] using hz)
  filter_upwards [hz'] with N hN
  simpa only [veryGoodComparableScaleCount_eq_centered_torus] using hN

#print axioms ae_recentered_ball_mass_ne_zero_ne_top
#print axioms ae_ae_veryGoodComparableScaleFrequency_of_observed_local_ball_rooted_law

end HarmonicBalls
