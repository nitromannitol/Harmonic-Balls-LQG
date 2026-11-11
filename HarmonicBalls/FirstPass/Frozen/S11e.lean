import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Defs.GFF

/-!
# Frozen inputs for Lemma 11.15 and 11.17

FROZEN inputs of `firstPass_11_15`. Each is a `def ... : Prop` (never an axiom). The field-level input is
stated for realized LQG metrics (`IsLQGMetricOfField`, almost everywhere) and only for carriers in `Type`, the form
chosen for the statement (never quantify over all `IsLQGMetric`).
-/

namespace HarmonicBalls

open MeasureTheory

/-- FROZEN. Pointwise almost-everywhere measurability of the LQG metric as a function of the field: for a
whole-plane GFF realization `(hC, hcirc)` on a probability space (carrier in `Type`, `γ ∈ (0,2)`) and a realized LQG
metric `D` with zero exponent (`IsLQGMetricOfField P γ ξ 0 hC D`, i.e. `D` is almost surely the Weyl-scaled metric `D_h`
of the field), every evaluation `ω ↦ D ω x y` is almost everywhere measurable.
Source: measurability of the LQG metric `h ↦ D_h` at field level (Gwynne-Miller 2021, Section 1.2, p. 6; locator pending),
the Fact 2.2 measurability used in Bou-Rabee-Gwynne (arXiv:2208.11795, Fact 2.2, p. 9; locator pending).
Used by: firstPass_11_15 (`HarmonicBalls/FirstPass/S11e.lean`), through `exists_measurable_version_of_continuous`
(`HarmonicBalls/FirstPass/S11e/MeasurableVersion.lean`). Truth check TRUE: the
measurable metric functional supplies a measurable version, and the realized metric is required to agree only almost
surely. Source: Gwynne-Miller, arXiv:1905.00383v3, §1.2, p. 6, the unnumbered measurable-map
definition and Axioms I and III, (1.8). -/
def LQGMetricPointwiseAEMeasurableFrozen : Prop :=
  ∀ (γ ξ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → IsLQGMetricOfField P γ ξ 0 hC D →
    ∀ x y : ℂ, AEMeasurable (fun ω => D ω x y) P

end HarmonicBalls
