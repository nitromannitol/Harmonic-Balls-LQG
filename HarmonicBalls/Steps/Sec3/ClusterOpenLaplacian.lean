import HarmonicBalls.Steps.Sec3.Basic

/-!
# Lemma 3.2 from Appendix A

`ClusterOpenLaplacianStmt` (Draft/Section3.lean; lemma:non-coincidence-open-harmonic, line 627): a.s., for all
`t, r > 0` and `z ∈ B_r`, the cluster `Λ = Λ_{B_r;z}(t)` is open and connected, and there is a Radon measure
`0 ≤ ν ≤ μ_h` on `B_r` with `Δ v_{B_r;z}(t) = μ_h|_Λ + ν|_{∂Λ}` and `Δ u_{B_r;z}(t) = -t δ_z + μ_h|_Λ + ν|_{∂Λ}`
on `B_r`. From Lemma A.2 (line 3652, openness and connectedness of `Λ_t`) and eq:laplacian-of-v-general
(lines 3840-3846, the Laplacian of the odometer, established in the proof of Lemma A.5) via the substitution
`Λ_{B_r;z}(t) = Λ_t`, `u_{B_r;z}(t) = v_t` (lines 3574-3578).

## Steps consumed

* `ObstacleNonCoincidenceHarmonicGeneral` (Steps/SecA/ObstacleNonCoincidenceHarmonic.lean) — Lemma A.2 for every
  radius and pole.
* `ShiftedOdometerLaplacianGeneral` (Steps/SecA/ObstacleConservationOfMass.lean) — eq:laplacian-of-v-general for every
  radius and pole, with `ν ≤ μ`. The printed Lemma 3.2 asserts the Laplacian identity, which the paper derives only
  inside the proof of Lemma A.5 (lines 3797-3803) and restates at line 3840; no numbered Appendix A statement contains
  it.
* `ObstacleCompatibilityShiftStep` (Steps/SecA/ObstacleCompatibility.lean) — the substitution.
* `GreenFunctionBallStmt` (Prop 2.3, Draft/Section2.lean; proved as `greenFunctionBall`, Steps/Sec2, not imported
  here because Proofs/Potential/GreenBall.lean and Steps/SecA/Basic.lean both declare
  `HarmonicBalls.continuousOn_greenFunction_ball_of_stmt`) — `Δ G_{B_r}(z,·) = -δ_z`, for the identity of `v`.
* `LQGVolumeGrowthAllScalesStmt` (Input I2) — the a.s. event.

## The reduction (proved)

`Λ_{B_r;z}(t) = Λ_t` gives openness and connectedness. `ν ≤ μ` gives `ν` Radon and `ν|_{B_r} ≪ μ|_{B_r}`,
`ν|_{B_r} ≤ μ|_{B_r}`. The odometer identity transfers by `u_{B_r;z}(t) = v_t` on the closed ball. The identity of
`v` follows from `v_{B_r;z}(t) = u_{B_r;z}(t) - t G_{B_r}(z,·)` (eq:limit-odometer, the definition of `odometer`)
and Prop 2.3: the two `t δ_z` cancel.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- **Lemma 3.2, deterministic form** (for a Radon measure with the volume growth condition on `B_r`). -/
theorem cluster_open_laplacian_of_general (h23 : GreenFunctionBallStmt)
    (hA2 : ObstacleNonCoincidenceHarmonicGeneral) (hA5 : ShiftedOdometerLaplacianGeneral)
    (hS : ObstacleCompatibilityShiftStep) {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {r βm βp : ℝ}
    (hr : 0 < r) (hV : VolumeGrowth μ r βm βp) {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) {t : ℝ} (ht : 0 < t) :
    IsOpen (cluster μ r z t) ∧ IsConnected (cluster μ r z t) ∧
    ∃ ν : Measure ℂ, IsLocallyFiniteMeasure ν ∧
      ν.restrict (ball 0 r) ≪ μ.restrict (ball 0 r) ∧
      ν.restrict (ball 0 r) ≤ μ.restrict (ball 0 r) ∧
      HasLaplacian (leastSupersolution μ r z t)
        (μ.restrict (cluster μ r z t) + ν.restrict (frontier (cluster μ r z t))) 0 (ball 0 r) ∧
      HasLaplacian (odometer μ r z t)
        (μ.restrict (cluster μ r z t) + ν.restrict (frontier (cluster μ r z t)))
        (ENNReal.ofReal t • Measure.dirac z) (ball 0 r) := by
  obtain ⟨-, -, hΛ, hu⟩ := hS μ hμ r βm βp hr hV z hz t ht
  obtain ⟨hopen, hconn, -⟩ := hA2 μ hμ r βm βp hr hV z hz t ht
  obtain ⟨ν, hνμ, hΔ⟩ := hA5 μ hμ r βm βp hr hV z hz t ht
  rw [hΛ]
  have hodo : HasLaplacian (odometer μ r z t)
      (μ.restrict (nonCoincidenceSet μ r z t) + ν.restrict (frontier (nonCoincidenceSet μ r z t)))
      (ENNReal.ofReal t • Measure.dirac z) (ball 0 r) :=
    hΔ.congr_eqOn measurableSet_ball fun x hx => (hu (ball_subset_closedBall hx)).symm
  have hle : ν.restrict (ball 0 r) ≤ μ.restrict (ball 0 r) := Measure.restrict_mono subset_rfl hνμ
  refine ⟨hopen, hconn, ν, Measure.isLocallyFiniteMeasure_of_le hνμ,
    Measure.absolutelyContinuous_of_le hle, hle, ?_, hodo⟩
  have hv := hodo.sub_const_mul ht.le (h23 r hr z hz).1
  convert hv using 1
  funext x
  simp only [odometer]
  ring

/-- **Lemma 3.2 from Appendix A** (line 614, lines 3574-3578, 3840-3846). -/
theorem clusterOpenLaplacian_of_steps (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h23 : GreenFunctionBallStmt)
    (hA2 : ObstacleNonCoincidenceHarmonicGeneral) (hA5 : ShiftedOdometerLaplacianGeneral)
    (hS : ObstacleCompatibilityShiftStep) : ClusterOpenLaplacianStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hae] with ω hω
  intro t r ht hr z hz
  exact cluster_open_laplacian_of_general h23 hA2 hA5 hS hω.1 hr (hω.2 r hr) hz ht

end HarmonicBalls
