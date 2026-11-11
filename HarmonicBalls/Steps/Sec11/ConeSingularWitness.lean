import HarmonicBalls.Steps.Sec11.ConeSingularComparison
import HarmonicBalls.Proofs.GFF.ConeMassLocalRepresentation

/-! # Measurable cone-event witnesses under singular Weyl scaling -/

namespace HarmonicBalls

/-! The cone-probability development uses Leonardo Bonanno's
Lattice-Probability formalization, including its Cameron-Martin port through
the local smooth-shift and fixed-shift decoder developments. -/

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- The probability of an ordinary cone event is a lower bound for a
measurable subset of the corresponding singular cone event. -/
theorem exists_cone_measurable_subset_of_singular_weight
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {μ ν : Ω → Measure ℂ} {r e M : ℝ} {z : ℂ} {Q : Set ℂ}
    (hr : 0 < r) (hM : 0 ≤ M) (hQ : IsCone Q)
    (hd : r / 100 ≤ infDist (0 : ℂ) (annulus z r (6 * r)))
    (hμ : AEMeasurable μ P)
    (hweyl : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ) :
    ∃ A ⊆ {ω | coneMassEvent (μ ω) Q M r z}, MeasurableSet A ∧
      P {ω | coneMassEvent (ν ω) Q (M * ((1201 : ℝ) ^ |e|) ^ 2) r z} ≤ P A := by
  have hQm : MeasurableSet Q := by
    rcases hQ with h | h
    · exact h.2.1.measurableSet
    · simpa using h.2.1.measurableSet.compl
  have hqm : MeasurableSet (annulus z r (2 * r) ∩ coneAt Q z) :=
    (measurableSet_ball.diff measurableSet_closedBall).inter
      ((Homeomorph.addRight z).measurableEmbedding.measurableSet_image.mpr hQm)
  have hn : NullMeasurableSet {ω | coneMassEvent (μ ω) Q M r z} P :=
    hμ.nullMeasurableSet_preimage (measurableSet_coneMassEvent Q M r z hqm)
  obtain ⟨A, hsub, hAm, hAeq⟩ := hn.exists_measurable_subset_ae_eq
  refine ⟨A, hsub, hAm, ?_⟩
  rw [measure_congr hAeq]
  apply measure_mono_ae
  filter_upwards [hweyl] with ω hω hevent
  exact coneMassEvent_of_singular_weight hr hM hd hω hevent

end HarmonicBalls
