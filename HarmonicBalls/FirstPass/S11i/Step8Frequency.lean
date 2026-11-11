import HarmonicBalls.FirstPass.S11i.HzoomScale
import HarmonicBalls.FirstPass.S11i.CertificateCanonical

/-!
# The Step-8 frequency at the unit-scale event `F`

* `step8Frequency P γ hC F = P[alphaCanon γ hC ∈ ballRestrictPairing 7 ⁻¹' F]`: the corrected limit `q_F` of the
  unit-ball frequency at insertion `γ` (paper: `p = P_can[E^{h^γ}_1(0;M)]`).
* `step8Frequency_eq_of_isWholePlaneGFF`: two whole-plane GFF models on one probability space give the same `q_F`
  (`S11iCert.prob_ballRestrict_alphaCanon_indep`). So the single `q` of `UnitBallFrequencyModelsStmt` is well defined.
* `unitBallFrequencyModels_at_step8Frequency`: `UnitBallFrequencyModelsStmt` at `q_F` reduces to the model-level
  unit-scale identification `hPer` (named input, pending in `HzoomScale`).
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls.FirstPassS11iStep8Frequency

open HarmonicBalls HarmonicBalls.S11iCert HarmonicBalls.FirstPassS11iHzoom

/-- **The Step-8 frequency** `q_F = P[alphaCanon γ hC ∈ F]` for the unit-scale certificate event `F`. -/
noncomputable def step8Frequency {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (F : Set (ModConstTestPairings (ball (0 : ℂ) 7))) : ℝ :=
  (P {ω | ballRestrictPairing 7 (alphaCanon γ hC ω) ∈ F}).toReal

/-- **Model independence of the Step-8 frequency.** On one probability space, two whole-plane GFF models give the same
canonical probability of a measurable unit-scale event `F`. -/
theorem step8Frequency_eq_of_isWholePlaneGFF {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (hh' : IsWholePlaneGFF P hC' hcirc') (γ : ℝ)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F) :
    step8Frequency P γ hC F = step8Frequency P γ hC' F := by
  unfold step8Frequency
  rw [prob_ballRestrict_alphaCanon_indep hh hh' γ F hF]

/-- **Unit-ball frequency at the Step-8 frequency.** `UnitBallFrequencyModelsStmt` carries one limit `q` for all
whole-plane models; at `q = q_F` the model dependence disappears (`step8Frequency_eq_of_isWholePlaneGFF`), so the
statement reduces to the model-level unit-scale identification `hPer` at the model's own `q_F` (named input, pending). -/
theorem unitBallFrequencyModels_at_step8Frequency {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ ξ : ℝ} {hC₀ : Ω → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω → ℝ → ℂ → ℝ}
    (hh₀ : IsWholePlaneGFF P hC₀ hcirc₀)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    (U V W T Q' Q : Set ℂ) (δ M : ℝ)
    (hPer : ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ) (μ' : Ω → Measure ℂ) (D' : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC' hcirc' → IsLQGMeasureOfField P γ 0 hcirc' μ' → IsLQGMetricOfField P γ ξ 0 hC' D' →
        UnitBallFrequencyStmt P (step8Frequency P γ hC' F) U V W T Q' Q δ M μ' D') :
    UnitBallFrequencyModelsStmt P γ ξ (step8Frequency P γ hC₀ F) U V W T Q' Q δ M := by
  intro hC' hcirc' μ' D' hG hμ hD
  rw [step8Frequency_eq_of_isWholePlaneGFF hh₀ hG γ hF]
  exact hPer hC' hcirc' μ' D' hG hμ hD

end HarmonicBalls.FirstPassS11iStep8Frequency

