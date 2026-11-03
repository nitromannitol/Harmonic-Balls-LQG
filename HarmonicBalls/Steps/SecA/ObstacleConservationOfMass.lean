import HarmonicBalls.Steps.SecA.ObstacleNonCoincidenceHarmonic
import HarmonicBalls.Steps.SecA.ObstacleOdometerZeroBoundary

/-!
# Lemma A.5 (lemma:appendix-conservation-of-mass, line 3788): carving of the proof

`ObstacleConservationOfMassStmt` (Draft/SectionA.lean): for `t > 0`, `μ(Λ_t) ≤ t`, and `μ(Λ_t) = t` if
`closure Λ_t ⊂ B_1` and `μ(∂Λ_t) = 0`. Printed proof: lines 3792-3828. Stated for a general radius `R > 0` and
pole `z ∈ B_R`: `ObstacleConservationOfMassGeneral`, which also records the intermediate identity
`t = μ(Λ_t) + ν(∂Λ_t)` of lines 3822-3825 (needed for the repair G3 of Prop 4.1), and
`ShiftedOdometerLaplacianGeneral`, the decomposition eq:laplacian-of-v (lines 3797-3803) and its general-ball
form eq:laplacian-of-v-general (lines 3840-3846), used by Lemma A.6.

## Steps (difficulty in brackets)

* `ObstacleConservationOfMassStep1` — **gap G1** (GRAPH.md): the odometer is subharmonic off the pole,
  `Δ v_t ≥ 0` on `B_R \ {z}`. The printed proof asserts `0 ≤ ν` in eq:laplacian-of-v without proof; Lemmas A.1
  and A.2 give only `Δ ṽ_t ≤ 0` on `B_R` and `Δ ṽ_t = 0` on `Λ_t`. Repair by the subharmonic gluing I7 (the
  argument of lines 1418-1421, AG01 Thm 3.2.2). [medium, 1-2 rounds]
* `ObstacleConservationOfMassStep2` — eq:laplacian-of-v: from `Δ ṽ_t ≤ 0` on `B_R`, `Δ ṽ_t = 0` on `Λ_t`,
  `Δ G = -δ_z`, `Δ q = -μ`, Step 1 and `v_t = 0` off `Λ_t`, there is `0 ≤ ν ≤ μ` with
  `Δ v_t = -t δ_z + μ|_{Λ_t} + ν|_{∂Λ_t}` (stated for general open `U ⊇ Λ`). [hard, 2-3 rounds: positive
  distributions are Radon measures (Riesz–Markov–Kakutani, Mathlib `RealRMK`), comparison of measures on open sets]
* `ObstacleConservationOfMassStep3` — eq:weak-integration-by-parts and the sign of the normal derivative
  (lines 3804-3820): if `v ≥ 0` is continuous on `closedBall 0 R \ {z}`, vanishes on `∂B_R` and
  `Δ v = σ - t δ_z` on `B_R`, then `σ(B_R) ≤ t`, with equality if `v` vanishes off a compact subset of `B_R`.
  The printed proof cites Pon16 Prop 7.3 and Lemma 12.15 (no External input exists for them); the step is stated
  as a self-contained claim. An elementary route: for `|z| < r < R`, `r d/dr M(v; 0, r) = (2π)⁻¹ (σ(B_r) - t)`,
  `M(v; 0, r) → 0` as `r → R` and `M(v; 0, r) ≥ 0`; for the equality case test against `φ = 1` near the compact
  set. [hard, 2-3 rounds]

Shared steps used by the reduction (Basic.lean): `GreenPotentialBallContinuousStep`,
`GreenPotentialBallLaplacianStep`; also Lemmas A.1, A.2, A.4 (general forms) and Prop 2.3
(`GreenFunctionBallStmt`).

## The reduction (proved)

`shiftedOdometerLaplacianGeneral_of_steps` (eq:laplacian-of-v) and `obstacleConservationOfMassGeneral_of_steps`:
Step 3 applied to `σ = μ|_{Λ_t} + ν|_{∂Λ_t}` gives `μ(Λ_t) + ν(∂Λ_t ∩ B_R) ≤ t`; if `closure Λ_t ⊂ B_R`, `v_t`
vanishes off the compact `closure Λ_t`, so `μ(Λ_t) + ν(∂Λ_t) = t`, and `ν(∂Λ_t) ≤ μ(∂Λ_t) = 0`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- eq:laplacian-of-v (lines 3797-3803) and eq:laplacian-of-v-general (lines 3840-3846) for a general radius
`R > 0` and pole `z ∈ B_R`: there is a measure `0 ≤ ν ≤ μ` (hence `ν ≪ μ`, Radon) with
`Δ v_t = -t δ_z + μ|_{Λ_t} + ν|_{∂Λ_t}` on `B_R`. -/
def ShiftedOdometerLaplacianGeneral : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ z ∈ ball (0 : ℂ) R, ∀ t : ℝ, 0 < t →
    ∃ ν : Measure ℂ, ν ≤ μ ∧
      HasLaplacian (shiftedOdometer μ R z t)
        (μ.restrict (nonCoincidenceSet μ R z t) + ν.restrict (frontier (nonCoincidenceSet μ R z t)))
        (ENNReal.ofReal t • Measure.dirac z) (ball 0 R)

/-- Lemma A.5 for a general radius `R > 0` and pole `z ∈ B_R` (the paper's case is `R = 1`, `z = 0`), with the
identity `t = μ(Λ_t) + ν(∂Λ_t)` of lines 3822-3825 when `closure Λ_t ⊂ B_R`. -/
def ObstacleConservationOfMassGeneral : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ z ∈ ball (0 : ℂ) R, ∀ t : ℝ, 0 < t →
    μ (nonCoincidenceSet μ R z t) ≤ ENNReal.ofReal t ∧
    (closure (nonCoincidenceSet μ R z t) ⊆ ball 0 R → μ (frontier (nonCoincidenceSet μ R z t)) = 0 →
      μ (nonCoincidenceSet μ R z t) = ENNReal.ofReal t) ∧
    ∃ ν : Measure ℂ, ν ≤ μ ∧
      HasLaplacian (shiftedOdometer μ R z t)
        (μ.restrict (nonCoincidenceSet μ R z t) + ν.restrict (frontier (nonCoincidenceSet μ R z t)))
        (ENNReal.ofReal t • Measure.dirac z) (ball 0 R) ∧
      (closure (nonCoincidenceSet μ R z t) ⊆ ball 0 R →
        μ (nonCoincidenceSet μ R z t) + ν (frontier (nonCoincidenceSet μ R z t)) = ENNReal.ofReal t)

/-! ## Steps -/

/-- **Lemma A.5, Step 1 (gap G1; repair I7).** The odometer `v_t = ṽ_t - β_t` satisfies `Δ v_t ≥ 0` on
`B_R \ {z}`. The printed proof asserts `0 ≤ ν` in eq:laplacian-of-v (line 3802) without proof; it does not follow
from Lemmas A.1-A.2. Repair (GRAPH.md, G1 and I7, the argument of lines 1418-1421): `v_t ≥ 0` is continuous on
`closedBall 0 R \ {z}` (Lemma A.1, Prop 2.3, `GreenPotentialBallContinuousStep`), `Δ v_t = μ ≥ 0` on
`Λ_t \ {z}` (Lemma A.2, `GreenPotentialBallLaplacianStep`, Prop 2.3), so `v_t` satisfies the sub-mean-value
inequality on small circles centred in `Λ_t \ {z}`; where `v_t = 0` the sub-mean-value inequality holds trivially
since `v_t ≥ 0`; by the local characterization of subharmonicity (AG01 Thm 3.2.2, cited at line 3672) `v_t` is
subharmonic on `B_R \ {z}`; pass to the distributional notion with `LaplacianLEOfSuperharmonicStep` applied to
`-v_t`. Uses: Lemmas A.1, A.2 (general forms), `SuperharmonicOfLaplacianLEStep`,
`LaplacianLEOfSuperharmonicStep`. Difficulty: medium (1-2 rounds). -/
def ObstacleConservationOfMassStep1 : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ z ∈ ball (0 : ℂ) R, ∀ t : ℝ, 0 < t →
    LaplacianGE (shiftedOdometer μ R z t) 0 (ball 0 R \ {z})

/-- **Lemma A.5, Step 2 (eq:laplacian-of-v, lines 3797-3803), for a general open set.** Let `Λ ⊆ U` be open,
`z ∈ Λ`, `μ` Radon, `t ≥ 0`, and `v = w - (-t G + q)` (for the obstacle problem: `w = ṽ_t`, `G = G_{B_R}(z,·)`,
`q = q_{B_R}`, so that `v = v_t`). If `Δw ≤ 0` on `U`, `Δw = 0` on `Λ`, `ΔG = -δ_z` and `Δq = -μ` on `U`,
`Δv ≥ 0` on `U \ {z}` (Step 1) and `v = 0` on `U \ Λ`, then `Δv = -t δ_z + μ|_Λ + ν|_{∂Λ}` on `U` for a measure
`ν ≤ μ`. Route: `σ = Δv + t δ_z = Δw + μ` satisfies `σ ≤ μ` on `U`, `σ ≥ 0` on `U \ {z}` and `σ = μ` on `Λ ∋ z`,
so `σ` is a positive distribution, hence a Radon measure (Riesz–Markov–Kakutani), with `σ ≤ μ`, `σ = μ` on `Λ`
and `σ = 0` on `U \ closure Λ` (where `v = 0`); take `ν = σ|_{∂Λ ∩ U}`. Difficulty: hard (2-3 rounds). -/
def ObstacleConservationOfMassStep2 : Prop :=
  ∀ (U Λ : Set ℂ) (z : ℂ) (μ : Measure ℂ) (t : ℝ) (w G q : ℂ → ℝ),
    IsOpen U → IsOpen Λ → Λ ⊆ U → z ∈ Λ → IsLocallyFiniteMeasure μ → 0 ≤ t →
    LaplacianLE w 0 U → HasLaplacian w 0 0 Λ →
    HasLaplacian G 0 (Measure.dirac z) U → HasLaplacian q 0 μ U →
    LaplacianGE (fun x => w x - (-t * G x + q x)) 0 (U \ {z}) →
    (∀ x ∈ U \ Λ, w x - (-t * G x + q x) = 0) →
    ∃ ν : Measure ℂ, ν ≤ μ ∧
      HasLaplacian (fun x => w x - (-t * G x + q x)) (μ.restrict Λ + ν.restrict (frontier Λ))
        (ENNReal.ofReal t • Measure.dirac z) U

/-- **Lemma A.5, Step 3 (eq:weak-integration-by-parts and the sign of the normal derivative, lines 3804-3827).**
Let `R > 0`, `z ∈ B_R`, `t ≥ 0`, `σ` a measure and `v` with `Δv = σ - t δ_z` on `B_R`, `v ≥ 0` on `B_R \ {z}`,
`v` continuous on `closedBall 0 R \ {z}` and `v = 0` on `∂B_R`. Then `σ(B_R) ≤ t`, with equality if `v` vanishes
on `B_R` off a compact subset of `B_R`. Printed argument: the weak normal derivative of Pon16 Prop 7.3 gives
`-t + σ(B_R) = ∫_{∂B_R} ∂v/∂n dσ_{∂B_R}`, nonpositive by Pon16 Lemma 12.15 since `v ≥ 0 = v|_{∂B_R}`, and zero
when `v` vanishes near `∂B_R` (lines 3812-3815). No External input exists for Pon16; the step is a self-contained
claim. Elementary route: for `|z| < r < R`, `r d/dr M(v; 0, r) = (2π)⁻¹ (σ(B_r) - t)` (a.e. `r`), `M(v; 0, r) ≥ 0`
and `M(v; 0, r) → 0` as `r → R` (uniform continuity on an annulus at `∂B_R`), so `σ(B_r) ≤ t` for all `r < R`;
for the equality case test `Δv = σ - t δ_z` against `φ = 1` near the compact set. Difficulty: hard
(2-3 rounds). -/
def ObstacleConservationOfMassStep3 : Prop :=
  ∀ (R : ℝ) (z : ℂ) (t : ℝ) (σ : Measure ℂ) (v : ℂ → ℝ), 0 < R → z ∈ ball (0 : ℂ) R → 0 ≤ t →
    HasLaplacian v σ (ENNReal.ofReal t • Measure.dirac z) (ball 0 R) →
    (∀ x ∈ ball (0 : ℂ) R, x ≠ z → 0 ≤ v x) →
    ContinuousOn v (closedBall 0 R \ {z}) →
    (∀ x ∈ sphere (0 : ℂ) R, v x = 0) →
    σ (ball 0 R) ≤ ENNReal.ofReal t ∧
      ((∃ K : Set ℂ, IsCompact K ∧ K ⊆ ball 0 R ∧ ∀ x ∈ ball (0 : ℂ) R \ K, v x = 0) →
        σ (ball 0 R) = ENNReal.ofReal t)

/-! ## Glue -/

/-- The odometer vanishes on `B_R \ Λ_t` (eq:appendix-non-co-set, line 3572, with `ṽ_t ≥ β_t`). -/
theorem shiftedOdometer_eq_zero_of_notMem {μ : Measure ℂ} {R t : ℝ} {z x : ℂ}
    (hne : (shiftedSupersolutions μ R z t).Nonempty) (hx : x ∈ ball (0 : ℂ) R)
    (hxΛ : x ∉ nonCoincidenceSet μ R z t) : shiftedOdometer μ R z t x = 0 := by
  have hxz : x ≠ z := fun h => hxΛ ⟨hx, Or.inl h⟩
  have hnlt : ¬ obstacle μ R z t x < shiftedLeastSupersolution μ R z t x := fun h => hxΛ ⟨hx, Or.inr h⟩
  have hle := obstacle_le_shiftedLeastSupersolution hne (ball_subset_closedBall hx) hxz
  simp only [shiftedOdometer]
  linarith [not_lt.1 hnlt]

/-! ## The reduction -/

/-- **eq:laplacian-of-v for a general radius and pole, from the steps.** -/
theorem shiftedOdometerLaplacianGeneral_of_steps (hA1 : ObstacleLeastSuperharmonicMajorantGeneral)
    (hA2 : ObstacleNonCoincidenceHarmonicGeneral) (h23 : GreenFunctionBallStmt)
    (hΔq : GreenPotentialBallLaplacianStep) (h1 : ObstacleConservationOfMassStep1)
    (h2 : ObstacleConservationOfMassStep2) : ShiftedOdometerLaplacianGeneral := by
  intro μ hμ R βm βp hR hV z hz t ht
  obtain ⟨-, -, hvS, -, -⟩ := hA1 μ hμ R βm βp hR hV z hz t ht
  obtain ⟨hopen, -, hharm⟩ := hA2 μ hμ R βm βp hR hV z hz t ht
  exact h2 (ball 0 R) (nonCoincidenceSet μ R z t) z μ t (shiftedLeastSupersolution μ R z t)
    (greenFunction (ball 0 R) z) (greenPotentialBall μ R) isOpen_ball hopen (fun x hx => hx.1)
    ⟨hz, Or.inl rfl⟩ hμ ht.le hvS.2.1 hharm (h23 R hR z hz).1 (hΔq μ hμ R βm βp hR hV)
    (h1 μ hμ R βm βp hR hV z hz t ht)
    (fun x hx => shiftedOdometer_eq_zero_of_notMem ⟨_, hvS⟩ hx.1 hx.2)

/-- **Lemma A.5, general radius and pole, from its steps.** -/
theorem obstacleConservationOfMassGeneral_of_steps (hA1 : ObstacleLeastSuperharmonicMajorantGeneral)
    (hA2 : ObstacleNonCoincidenceHarmonicGeneral) (hA4 : ObstacleOdometerZeroBoundaryGeneral)
    (h23 : GreenFunctionBallStmt) (hq : GreenPotentialBallContinuousStep) (hΔq : GreenPotentialBallLaplacianStep)
    (h1 : ObstacleConservationOfMassStep1) (h2 : ObstacleConservationOfMassStep2)
    (h3 : ObstacleConservationOfMassStep3) : ObstacleConservationOfMassGeneral := by
  intro μ hμ R βm βp hR hV z hz t ht
  obtain ⟨ν, hνμ, hΔv⟩ :=
    shiftedOdometerLaplacianGeneral_of_steps hA1 hA2 h23 hΔq h1 h2 μ hμ R βm βp hR hV z hz t ht
  obtain ⟨-, hvc, hvS, -, -⟩ := hA1 μ hμ R βm βp hR hV z hz t ht
  have hne : (shiftedSupersolutions μ R z t).Nonempty := ⟨_, hvS⟩
  have hΛsub : nonCoincidenceSet μ R z t ⊆ ball 0 R := fun x hx => hx.1
  have hv0 : ∀ x ∈ ball (0 : ℂ) R, x ≠ z → 0 ≤ shiftedOdometer μ R z t x := fun x hx hxz =>
    shiftedOdometer_nonneg hne (ball_subset_closedBall hx) hxz
  have hvcont : ContinuousOn (shiftedOdometer μ R z t) (closedBall 0 R \ {z}) :=
    (hvc.mono sdiff_subset).sub (continuousOn_obstacle h23 hR hz (hq μ hμ R βm βp hR hV))
  obtain ⟨hle, heq⟩ := h3 R z t _ (shiftedOdometer μ R z t) hR hz ht.le hΔv hv0 hvcont
    (hA4 μ hμ R βm βp hR hV z hz t ht)
  have hσ : (μ.restrict (nonCoincidenceSet μ R z t) + ν.restrict (frontier (nonCoincidenceSet μ R z t)))
      (ball 0 R) = μ (nonCoincidenceSet μ R z t) + ν (ball 0 R ∩ frontier (nonCoincidenceSet μ R z t)) := by
    rw [Measure.add_apply, Measure.restrict_apply measurableSet_ball, Measure.restrict_apply measurableSet_ball,
      inter_eq_right.2 hΛsub]
  rw [hσ] at hle heq
  have hid : closure (nonCoincidenceSet μ R z t) ⊆ ball 0 R →
      μ (nonCoincidenceSet μ R z t) + ν (frontier (nonCoincidenceSet μ R z t)) = ENNReal.ofReal t := by
    intro hcl
    have h := heq ⟨closure (nonCoincidenceSet μ R z t),
      ((isBounded_ball.subset hΛsub).isCompact_closure), hcl, fun x hx =>
        shiftedOdometer_eq_zero_of_notMem hne hx.1 fun hxΛ => hx.2 (subset_closure hxΛ)⟩
    rwa [inter_eq_right.2 (frontier_subset_closure.trans hcl)] at h
  refine ⟨le_self_add.trans hle, fun hcl hfr => ?_, ν, hνμ, hΔv, hid⟩
  have hν0 : ν (frontier (nonCoincidenceSet μ R z t)) = 0 :=
    le_antisymm ((Measure.le_iff'.1 hνμ _).trans hfr.le) zero_le
  have := hid hcl
  rwa [hν0, add_zero] at this

/-- The general form of Lemma A.5 gives the printed statement (`R = 1`, `z = 0`). -/
theorem obstacleConservationOfMass_of_general (h : ObstacleConservationOfMassGeneral) :
    ObstacleConservationOfMassStmt := fun μ hμ βm βp hV t ht =>
  ⟨(h μ hμ 1 βm βp one_pos hV 0 (mem_ball_self one_pos) t ht).1,
    (h μ hμ 1 βm βp one_pos hV 0 (mem_ball_self one_pos) t ht).2.1⟩

/-- **Lemma A.5 from its steps** (and Lemmas A.1, A.2, A.4, Prop 2.3, the shared steps). -/
theorem obstacleConservationOfMass_of_steps (hA1 : ObstacleLeastSuperharmonicMajorantGeneral)
    (hA2 : ObstacleNonCoincidenceHarmonicGeneral) (hA4 : ObstacleOdometerZeroBoundaryGeneral)
    (h23 : GreenFunctionBallStmt) (hq : GreenPotentialBallContinuousStep) (hΔq : GreenPotentialBallLaplacianStep)
    (h1 : ObstacleConservationOfMassStep1) (h2 : ObstacleConservationOfMassStep2)
    (h3 : ObstacleConservationOfMassStep3) : ObstacleConservationOfMassStmt :=
  obstacleConservationOfMass_of_general
    (obstacleConservationOfMassGeneral_of_steps hA1 hA2 hA4 h23 hq hΔq h1 h2 h3)

end HarmonicBalls
