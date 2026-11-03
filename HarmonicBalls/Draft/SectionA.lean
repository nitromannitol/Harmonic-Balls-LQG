import HarmonicBalls.Defs.Obstacle

/-!
# Appendix A: statements of Lemmas A.1-A.6 (obstacle problem for Radon measures)

Statements of the numbered results of Appendix A (sec:obstacle-appendix, lines 3522-3900) of the corrected draft of
Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795).

## Setting

A Radon measure `μ` on `ℂ` (`IsLocallyFiniteMeasure μ`) satisfying the volume growth condition (eq:volume-growth,
line 3526) on `B_R` with exponents `β⁻, β⁺ > 0` (`VolumeGrowth μ R βminus βplus`, with the upper exponent `β⁺` of
[C2]). Lemmas A.1-A.5 are stated, as in the paper (line 3547), for `R = 1` and the pole `z = 0`; Lemma A.6 concerns
the balls `B_s`, `s ≤ R`, with pole `0`.

## Conventions

* Lemmas A.1-A.5 concern the shifted obstacle problem of `HarmonicBalls/Defs/Obstacle.lean` with `R = 1`, `z = 0`:
  the obstacle `β_t = obstacle μ 1 0 t` (eq:obstacle, line 3551), `S̃(t) = shiftedSupersolutions μ 1 0 t`
  (eq:shifted-supersolutions, line 3556), the least superharmonic majorant `ṽ_t = shiftedLeastSupersolution μ 1 0 t`
  (eq:appendix-least-supersolution, line 3563), the odometer `v_t = shiftedOdometer μ 1 0 t`
  (eq:appendix-limit-odometer, line 3567) and the non-coincidence set `Λ_t = nonCoincidenceSet μ 1 0 t`
  (eq:appendix-non-co-set, line 3572). These are defined (line 3550) for `t > 0`, a hypothesis of every statement.
* Lemma A.6 concerns the clusters `Λ^{B_s}_t = cluster μ s 0 t` of the (unshifted) obstacle problem of Section 3.1
  with `μ` in place of `μ_h` (line 3838).
* "Finite" for `ṽ_t` (an infimum, possibly `-∞` a priori) is the bounded below property of the set of values of
  elements of `S̃(t)` at every point of the closed ball. Differential identities are distributional (line 325,
  `HasLaplacian`). "Connected" is `IsConnected`.

## Corrections applied

[C2] (upper exponent `β⁺` in eq:volume-growth, line 3527) through `VolumeGrowth`; [C4] (`μ_h` → `μ` in the
conclusion of Lemma A.5, line 3789). See `~/paper-fleets/hb/CORRECTIONS-PROPOSED.md`.
-/

namespace HarmonicBalls

open MeasureTheory Metric

/-- Lemma A.1 (lemma:appendix-basic-properties, line 3589). For a Radon measure `μ` satisfying the volume growth
condition (eq:volume-growth, line 3526) on `B_1` and all `t > 0`, the least superharmonic majorant `ṽ_t`
(eq:appendix-least-supersolution, line 3563) of the obstacle `β_t = -t G_{B_1}(0,·) + q_{B_1}` (eq:obstacle,
line 3551) is finite, continuous, and an element of `S̃(t)` (eq:shifted-supersolutions, line 3556).

"Finite" is the bounded below property of `{w(x) : w ∈ S̃(t)}` at every `x` of the closed unit ball; it is automatic
off the pole (`bddBelow_shiftedSupersolutions`), so its content is finiteness at `0`. "Continuous" is continuity on
the closed unit ball. Corrections applied: [C2] (through `VolumeGrowth`). -/
def ObstacleLeastSuperharmonicMajorantStmt : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ βminus βplus : ℝ, VolumeGrowth μ 1 βminus βplus →
  ∀ t : ℝ, 0 < t →
    (∀ x ∈ closedBall (0 : ℂ) 1, BddBelow ((fun w : ℂ → ℝ => w x) '' shiftedSupersolutions μ 1 0 t)) ∧
    ContinuousOn (shiftedLeastSupersolution μ 1 0 t) (closedBall 0 1) ∧
    shiftedLeastSupersolution μ 1 0 t ∈ shiftedSupersolutions μ 1 0 t

/-- Lemma A.2 (lemma:appendix-non-coincedence-open-harmonic, line 3652). For a Radon measure `μ` satisfying the volume
growth condition on `B_1` and all `t > 0`, the non-coincidence set `Λ_t` (eq:appendix-non-co-set, line 3572) is open
and connected and `Δ ṽ_t = 0` on `Λ_t`.

The identity `Δ ṽ_t = 0` is distributional (line 325) on the open set `Λ_t`: `HasLaplacian ṽ_t 0 0 Λ_t` (for the
continuous `ṽ_t` of Lemma A.1 it is equivalent, by Weyl's lemma, to harmonicity on `Λ_t`, line 3650).
Corrections applied: [C2] (through `VolumeGrowth`). -/
def ObstacleNonCoincidenceHarmonicStmt : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ βminus βplus : ℝ, VolumeGrowth μ 1 βminus βplus →
  ∀ t : ℝ, 0 < t →
    IsOpen (nonCoincidenceSet μ 1 0 t) ∧ IsConnected (nonCoincidenceSet μ 1 0 t) ∧
    HasLaplacian (shiftedLeastSupersolution μ 1 0 t) 0 0 (nonCoincidenceSet μ 1 0 t)

/-- Lemma A.3 (lemma:appendix-monotonicity, line 3731). For a Radon measure `μ` satisfying the volume growth
condition on `B_1`: if `t₁ ≤ t₂`, then `Λ_{t₁} ⊆ Λ_{t₂}`.

The non-coincidence sets are defined for `t > 0` (line 3550), hence `0 < t₁`. Corrections applied: [C2] (through
`VolumeGrowth`). -/
def ObstacleMonotoneStmt : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ βminus βplus : ℝ, VolumeGrowth μ 1 βminus βplus →
  ∀ t₁ t₂ : ℝ, 0 < t₁ → t₁ ≤ t₂ → nonCoincidenceSet μ 1 0 t₁ ⊆ nonCoincidenceSet μ 1 0 t₂

/-- Lemma A.4 (lemma:appendix-zero-boundary, line 3772). For a Radon measure `μ` satisfying the volume growth
condition on `B_1` and all `t > 0`, the odometer `v_t = ṽ_t - β_t` (eq:appendix-limit-odometer, line 3567) vanishes
on `∂B_1`. Corrections applied: [C2] (through `VolumeGrowth`). -/
def ObstacleOdometerZeroBoundaryStmt : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ βminus βplus : ℝ, VolumeGrowth μ 1 βminus βplus →
  ∀ t : ℝ, 0 < t → ∀ x ∈ sphere (0 : ℂ) 1, shiftedOdometer μ 1 0 t x = 0

/-- Lemma A.5 (lemma:appendix-conservation-of-mass, line 3788). For a Radon measure `μ` satisfying the volume growth
condition on `B_1` and all `t > 0`, `μ(Λ_t) ≤ t`; moreover, if `closure Λ_t ⊂ B_1` and `μ(∂Λ_t) = 0`, then
`μ(Λ_t) = t`.

Corrections applied: [C4] (the printed conclusion `μ_h(Λ_t) = t`, line 3789, reads `μ(Λ_t) = t`); [C2] (through
`VolumeGrowth`). -/
def ObstacleConservationOfMassStmt : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ βminus βplus : ℝ, VolumeGrowth μ 1 βminus βplus →
  ∀ t : ℝ, 0 < t →
    μ (nonCoincidenceSet μ 1 0 t) ≤ ENNReal.ofReal t ∧
    (closure (nonCoincidenceSet μ 1 0 t) ⊆ ball 0 1 → μ (frontier (nonCoincidenceSet μ 1 0 t)) = 0 →
      μ (nonCoincidenceSet μ 1 0 t) = ENNReal.ofReal t)

/-- Lemma A.6 (lemma:appendix-cluster-compatibility, line 3851). Suppose that the Radon measure `μ` satisfies the
volume growth condition (eq:volume-growth, line 3526) on `B_R`. For all `t > 0` and `0 < s₁ ≤ R`, if
`closure Λ^{B_{s₂}}_t ⊂ B_{s₁}` for some `s₂ ∈ [s₁, R]`, then `Λ^{B_s}_t = Λ^{B_{s₂}}_t` for all `s ∈ [s₁, R]`.

`Λ^{B_s}_t = cluster μ s 0 t` is the cluster of the obstacle problem of Section 3.1 on `B_s` with measure `μ` and
pole `0` (line 3838). The printed statement leaves `t` unbound (line 3853); it is universally quantified. The radius
`s₁` is positive (balls `B_s` have `s > 0`, line 330); without `0 < s₁` the statement fails for `s₁ ≤ s₂ ≤ 0 < s`
(then `Λ^{B_{s₂}}_t = ∅` while `0 ∈ Λ^{B_s}_t`). Corrections applied: [C2] (through `VolumeGrowth`). -/
def ObstacleCompatibilityStmt : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, VolumeGrowth μ R βminus βplus →
  ∀ t : ℝ, 0 < t → ∀ s₁ : ℝ, 0 < s₁ → s₁ ≤ R →
    ∀ s₂ ∈ Set.Icc s₁ R, closure (cluster μ s₂ 0 t) ⊆ ball 0 s₁ →
      ∀ s ∈ Set.Icc s₁ R, cluster μ s 0 t = cluster μ s₂ 0 t

end HarmonicBalls
