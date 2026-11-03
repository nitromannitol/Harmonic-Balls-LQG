import HarmonicBalls.Steps.Sec3.Basic

/-!
# Lemma 3.4 from Appendix A

`ClusterConservationOfMassStmt` (Draft/Section3.lean; lemma:conservation-of-mass, line 649): a.s., for all `r, t > 0`
and `z ∈ B_r`, `μ_h(Λ_{B_r;z}(t)) ≤ t`, the odometer `u_{B_r;z}(t)` vanishes on `∂B_r`, and
`μ_h(Λ_{B_r;z}(t)) = t` when `closure Λ_{B_r;z}(t) ⊂ B_r` and `μ_h(∂Λ_{B_r;z}(t)) = 0`. From Lemmas A.4 (line 3772)
and A.5 (line 3788) via `Λ_{B_r;z}(t) = Λ_t`, `u_{B_r;z}(t) = v_t` (lines 3574-3578).

## Steps consumed

* `ObstacleOdometerZeroBoundaryGeneral` (Steps/SecA/ObstacleOdometerZeroBoundary.lean) — Lemma A.4 for every radius
  and pole.
* `ObstacleConservationOfMassGeneral` (Steps/SecA/ObstacleConservationOfMass.lean) — Lemma A.5 for every radius and
  pole.
* `ObstacleCompatibilityShiftStep` (Steps/SecA/ObstacleCompatibility.lean) — the substitution.
* `LQGVolumeGrowthAllScalesStmt` (Input I2) — the a.s. event.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- **Lemma 3.4, deterministic form** (for a Radon measure with the volume growth condition on `B_r`). -/
theorem cluster_conservationOfMass_of_general (hA4 : ObstacleOdometerZeroBoundaryGeneral)
    (hA5 : ObstacleConservationOfMassGeneral) (hS : ObstacleCompatibilityShiftStep) {μ : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) {r βm βp : ℝ} (hr : 0 < r) (hV : VolumeGrowth μ r βm βp) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) r) {t : ℝ} (ht : 0 < t) :
    μ (cluster μ r z t) ≤ ENNReal.ofReal t ∧
    (∀ x ∈ sphere (0 : ℂ) r, odometer μ r z t x = 0) ∧
    (closure (cluster μ r z t) ⊆ ball 0 r → μ (frontier (cluster μ r z t)) = 0 →
      μ (cluster μ r z t) = ENNReal.ofReal t) := by
  obtain ⟨-, -, hΛ, hu⟩ := hS μ hμ r βm βp hr hV z hz t ht
  obtain ⟨hle, heq, -⟩ := hA5 μ hμ r βm βp hr hV z hz t ht
  rw [hΛ]
  exact ⟨hle, fun x hx => (hu (sphere_subset_closedBall hx)).trans (hA4 μ hμ r βm βp hr hV z hz t ht x hx),
    heq⟩

/-- **Lemma 3.4 from Appendix A** (line 614, lines 3574-3578). -/
theorem clusterConservationOfMass_of_steps (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hA4 : ObstacleOdometerZeroBoundaryGeneral) (hA5 : ObstacleConservationOfMassGeneral)
    (hS : ObstacleCompatibilityShiftStep) : ClusterConservationOfMassStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hae] with ω hω
  intro r t hr ht z hz
  exact cluster_conservationOfMass_of_general hA4 hA5 hS hω.1 hr (hω.2 r hr) hz ht

end HarmonicBalls
