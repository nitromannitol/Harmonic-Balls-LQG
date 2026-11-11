import HarmonicBalls.Proofs.Sec8.ObservedFrequencyEvent
import HarmonicBalls.Proofs.Sec8.CommonApproximationLaw

/-! # Frequency events from observed mass approximations

The phase-frequency argument uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. Convergence of the approximations
under the rooted law remains an explicit hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- If normalized masses are limits in measure of functions of the observed
field and root, the frequency event has an observed representative. -/
theorem exists_observed_frequency_event_of_mass_approximations
    {A F : Type*} [MeasurableSpace A] [MeasurableSpace F]
    (P : Measure A) [IsProbabilityMeasure P] (obs : A → F × ℂ) (hobs : Measurable obs)
    (μ : A → Measure ℂ) (ε : ℝ) (hε : 0 < ε)
    (hμ : AEMeasurable μ P) (hloc : ∀ᵐ x ∂P, IsLocallyFiniteMeasure (μ x))
    (hmass : ∀ᵐ x ∂P,
      ((μ x).map (fun v : ℂ => v - (obs x).2)) (ball 0 ε) ≠ 0 ∧
      ((μ x).map (fun v : ℂ => v - (obs x).2)) (ball 0 ε) ≠ ∞)
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ V ∈ S, MeasurableSet V)
    (f : S → ℕ → F × ℂ → ℝ) (hf : ∀ V n, Measurable (f V n))
    (hlim : ∀ V, TendstoInMeasure P (fun n x => f V n (obs x)) atTop
      (fun x => (normalizedRestriction
        ((μ x).map (fun v : ℂ => v - (obs x).2)) (ball 0 ε) V.val).toReal))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {η : Measure ℂ | IsGoodAnnulus η 1 0 a b}) :
    ∃ E : Set (F × ℂ), MeasurableSet E ∧
      ∀ᵐ x ∂P, (obs x ∈ E ↔ ∀ᶠ N : ℕ in atTop,
        (1 - ζ) * (N : ℝ) ≤ (veryGoodComparableScaleCount (μ x) β (obs x).2 N₀
          a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)) := by
  apply exists_observed_frequency_event_of_countable_ratios P obs hobs μ ε hε hμ hloc hmass
    S hcount hgen hpi hsets ?_ β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit
  intro V hV
  let i : S := ⟨V, hV⟩
  obtain ⟨g, hgm, hg, _⟩ := exists_common_limit_of_tendstoInMeasure P P obs obs
    (f i) (hf i) _ _ (hlim i) (hlim i)
  refine ⟨fun x => ENNReal.ofReal (g (obs x)), ?_, ?_⟩
  · let : MeasurableSpace A := MeasurableSpace.comap obs inferInstance
    exact ENNReal.measurable_ofReal.comp (hgm.comp (comap_measurable obs))
  · filter_upwards [hg] with x hx
    have he := congrArg ENNReal.ofReal hx.symm
    rw [ENNReal.ofReal_toReal (measure_ne_top
      (normalizedRestriction ((μ x).map (fun v : ℂ => v - (obs x).2)) (ball 0 ε)) V)] at he
    simpa only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply (hsets V hV), ENNReal.div_eq_inv_mul] using he

end HarmonicBalls
