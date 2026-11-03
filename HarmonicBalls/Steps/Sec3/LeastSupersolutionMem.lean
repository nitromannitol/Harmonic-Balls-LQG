import HarmonicBalls.Steps.Sec3.Basic

/-!
# Lemma 3.1 from Appendix A

`LeastSupersolutionMemStmt` (Draft/Section3.lean; lemma:basic-properties, line 621): a.s., for all `t, r > 0` and
`z ∈ B_r`, the least supersolution `v_{B_r;z}(t)` is finite, continuous and an element of `S_{B_r;z}(t)`.
"These results ... are proved in Appendix A" (line 614): Lemma A.1 (line 3589) via the substitution
`v_{B_r;z}(t) = ṽ_t - q_{B_r}` (lines 3574-3578).

## Steps consumed

* `ObstacleLeastSuperharmonicMajorantGeneral` (Steps/SecA/ObstacleLeastSuperharmonicMajorant.lean) — Lemma A.1 for
  every radius `R > 0` and pole `z ∈ B_R`; the printed Lemma A.1 (`R = 1`, `z = 0`, line 3545) does not suffice, see
  the gap in Steps/Sec3/Basic.lean.
* `ObstacleCompatibilityShiftStep` (Steps/SecA/ObstacleCompatibility.lean) — the substitution.
* `LQGVolumeGrowthAllScalesStmt` (Input I2, Draft/Section2.lean) — the a.s. event (lines 3528-3530).

## The reduction (proved)

Finiteness: `w ∈ S_{B_r;z}(t)` gives `w + q_{B_r} ∈ S̃(t)`, so a lower bound `b` for `S̃(t)` at `x` gives the lower
bound `b - q_{B_r}(x)` for `S_{B_r;z}(t)`. Membership: `v_{B_r;z}(t) + q_{B_r} = ṽ_t ∈ S̃(t)` on the closed ball, and
membership in `S̃(t)` depends only on the values there. Continuity is part of membership.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- **Lemma 3.1, deterministic form** (for a Radon measure with the volume growth condition on `B_r`). -/
theorem leastSupersolution_mem_of_general (hA1 : ObstacleLeastSuperharmonicMajorantGeneral)
    (hS : ObstacleCompatibilityShiftStep) {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {r βm βp : ℝ}
    (hr : 0 < r) (hV : VolumeGrowth μ r βm βp) {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) {t : ℝ} (ht : 0 < t) :
    (∀ x ∈ closedBall (0 : ℂ) r, BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutions μ r z t)) ∧
    ContinuousOn (leastSupersolution μ r z t) (closedBall 0 r) ∧
    leastSupersolution μ r z t ∈ supersolutions μ r z t := by
  obtain ⟨hbdd, -, hmem, -, -⟩ := hA1 μ hμ r βm βp hr hV z hz t ht
  obtain ⟨hiff, hv, -, -⟩ := hS μ hμ r βm βp hr hV z hz t ht
  have hmem' : leastSupersolution μ r z t ∈ supersolutions μ r z t := by
    refine (hiff _).2 (mem_shiftedSupersolutions_of_eqOn hmem fun x hx => ?_)
    show _ = leastSupersolution μ r z t x + greenPotentialBall μ r x
    rw [hv x hx]
    ring
  refine ⟨fun x hx => ?_, hmem'.1, hmem'⟩
  obtain ⟨b, hb⟩ := hbdd x hx
  refine ⟨b - greenPotentialBall μ r x, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  have hbw : b ≤ w x + greenPotentialBall μ r x := hb ⟨_, (hiff w).1 hw, rfl⟩
  show b - greenPotentialBall μ r x ≤ w x
  linarith

/-- **Lemma 3.1 from Appendix A** (line 614, lines 3574-3578). -/
theorem leastSupersolutionMem_of_steps (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hA1 : ObstacleLeastSuperharmonicMajorantGeneral) (hS : ObstacleCompatibilityShiftStep) :
    LeastSupersolutionMemStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hae] with ω hω
  intro t r ht hr z hz
  exact leastSupersolution_mem_of_general hA1 hS hω.1 hr (hω.2 r hr) hz ht

end HarmonicBalls
