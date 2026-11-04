import HarmonicBalls.Proofs.Sec8.FiniteMeasureApproximationLaw
import HarmonicBalls.Proofs.Sec8.PhaseLocalLawTransfer
import HarmonicBalls.Proofs.Sec8.CenteredMeasureLaw

/-! # Local phase law from common normalized mass approximations

The imported Section 8 phase argument uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization of the ergodic theorem.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace HarmonicBalls

/-- Shared approximations on a countable generating π-system provide the
locally finite-measure law domination required by the phase transfer. -/
theorem localNormalizedMeasure_law_absolutelyContinuous_of_common_approximations
    {E Ω Ξ : Type*} [MeasurableSpace E] [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) (X : Ω → E) (Y : Ξ → E)
    (hX : Measurable X) (hY : Measurable Y) (hdom : Q.map Y ≪ P.map X)
    (U : Ω → {μ : Measure ℂ // IsLocallyFiniteMeasure μ})
    (V : Ξ → {μ : Measure ℂ // IsLocallyFiniteMeasure μ})
    (hU : Measurable U) (hV : Measurable V) (ε : ℝ)
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ A ∈ S, MeasurableSet A) (huniv : univ ∈ S)
    (f : S → ℕ → E → ℝ) (hf : ∀ A n, Measurable (f A n))
    (hu : ∀ A, TendstoInMeasure P (fun n ω => f A n (X ω)) atTop
      (fun ω => (normalizedRestriction (U ω).val (Metric.ball 0 ε) A.val).toReal))
    (hv : ∀ A, TendstoInMeasure Q (fun n ω => f A n (Y ω)) atTop
      (fun ω => (normalizedRestriction (V ω).val (Metric.ball 0 ε) A.val).toReal)) :
    Q.map (fun ω => localNormalizedMeasure ε (V ω)) ≪
      P.map (fun ω => localNormalizedMeasure ε (U ω)) := by
  apply absolutelyContinuous_subtype_of_map
  have hV' : Measurable (fun ω => localNormalizedMeasure ε (V ω)) :=
    (measurable_localNormalizedMeasure ε).comp hV
  have hU' : Measurable (fun ω => localNormalizedMeasure ε (U ω)) :=
    (measurable_localNormalizedMeasure ε).comp hU
  rw [Measure.map_map measurable_subtype_coe hV', Measure.map_map measurable_subtype_coe hU']
  exact normalizedRestriction_law_absolutelyContinuous_of_common_approximations P Q X Y
    hX hY hdom (fun ω => (U ω).val) (fun ω => (V ω).val)
    (measurable_subtype_coe.comp hU) (measurable_subtype_coe.comp hV)
    (Metric.ball 0 ε) Metric.isOpen_ball.measurableSet S hcount hgen hpi hsets huniv f hf hu hv

#print axioms localNormalizedMeasure_law_absolutelyContinuous_of_common_approximations

end HarmonicBalls
