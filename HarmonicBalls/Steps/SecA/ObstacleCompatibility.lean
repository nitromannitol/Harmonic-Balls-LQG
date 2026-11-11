import HarmonicBalls.Steps.SecA.Basic

/-!
# Lemma A.6 (lemma:appendix-cluster-compatibility, line 3851): carving of the proof

`ObstacleCompatibilityStmt` (Draft/SectionA.lean): under the volume growth condition on `B_R`, if
`closure Λ^{B_{s₂}}_t ⊂ B_{s₁}` for some `s₂ ∈ [s₁, R]`, then `Λ^{B_s}_t = Λ^{B_{s₂}}_t` for all `s ∈ [s₁, R]`.
Here `Λ^{B_s}_t = cluster μ s 0 t` and `u^{B_s}_t = odometer μ s 0 t` belong to the unshifted problem of Section 3.1
with `μ` in place of `μ_h` (line 3838). Printed proof: lines 3856-3895.

## Steps (difficulty in brackets)

* `ObstacleCompatibilityStep1` — eq:monotonicity-domains (lines 3862-3880): `u^{B_{r₁}}_t ≤ u^{B_{r₂}}_t` on
  `B_{r₁}` for `r₁ ≤ r₂ ≤ R` (competitor `ŵ_t`).
* `ObstacleCompatibilityStep2` — eq:monotonicity-domains-two (lines 3882-3890): under the hypothesis
  `closure Λ^{B_{s₂}}_t ⊂ B_{s₁}`, `u^{B_R}_t ≤ u^{B_{s₁}}_t` on `B_{s₁}` and `u^{B_R}_t ≤ 0` on `B_R \ B_{s₁}`
  (the extension of `u^{B_{s₁}}_t` by `0`; subharmonic comparison on `Λ^{B_R}_t`).
* `ObstacleCompatibilityShiftStep` — auxiliary, used inside Steps 1-2 (and by the Section 3 lemmas), not by the
  reduction: the substitution of lines 3574-3578, `v_{B_R;z}(t) = ṽ_t - q_{B_R}`, `Λ_{B_R;z}(t) = Λ_t`,
  `u_{B_R;z}(t) = v_t`, which transfers Lemmas A.1, A.4 and eq:laplacian-of-v-general (`ShiftedOdometerLaplacianGeneral`,
  ObstacleConservationOfMass.lean) to the unshifted problem on every `B_s`, `s ≤ R` ("the results proved so far in
  this appendix apply to `v^{B_R}, Λ^{B_R}, u^{B_R}`", line 3838; `VolumeGrowth.mono`, line 3858).

## The reduction (proved)

`obstacleCompatibility_of_steps`: for `s ∈ [s₁, R]` and `x ∈ B_{s₁} \ {0}`, Steps 1-2 give
`u^{B_{s₁}} ≤ u^{B_s} ≤ u^{B_R} ≤ u^{B_{s₁}}` at `x` (line 3892); for `x ∈ B_s \ B_{s₁}`,
`u^{B_s}(x) ≤ u^{B_R}(x) ≤ 0`. Hence `Λ^{B_s}_t = Λ^{B_{s₁}}_t` for every `s ∈ [s₁, R]`, in particular for `s₂`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-! ## Steps -/

/-- **Lemma A.6, auxiliary step (the substitution of lines 3574-3578).** Under the volume growth condition on
`B_R`, `w ∈ S_{B_R;z}(t)` iff `w + q_{B_R} ∈ S̃(t)`, the least supersolutions differ by `q_{B_R}` on the closed ball,
the cluster is the non-coincidence set and the odometers agree on the closed ball. Route: `Δ q_{B_R} = -μ` and the
continuity of `q_{B_R}` (`GreenPotentialBallLaplacianStep`, `GreenPotentialBallContinuousStep`); at the pole the
identity of the infima needs their finiteness (Lemma A.1, general form). Used inside Steps 1-2 and by the
Section 3 lemmas; not a hypothesis of the reduction. -/
def ObstacleCompatibilityShiftStep : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ z ∈ ball (0 : ℂ) R, ∀ t : ℝ, 0 < t →
    (∀ w : ℂ → ℝ, w ∈ supersolutions μ R z t ↔
      (fun x => w x + greenPotentialBall μ R x) ∈ shiftedSupersolutions μ R z t) ∧
    (∀ x ∈ closedBall (0 : ℂ) R,
      leastSupersolution μ R z t x = shiftedLeastSupersolution μ R z t x - greenPotentialBall μ R x) ∧
    cluster μ R z t = nonCoincidenceSet μ R z t ∧
    EqOn (odometer μ R z t) (shiftedOdometer μ R z t) (closedBall 0 R)

/-- **Lemma A.6, Step 1 (eq:monotonicity-domains, lines 3862-3880).** For `0 < r₁ ≤ r₂ ≤ R`,
`u^{B_{r₁}}_t ≤ u^{B_{r₂}}_t` on `B_{r₁}` off the pole. Printed argument: the competitor
`ŵ_t = v^{B_{r₂}}_t - t (G_{B_{r₁}}(0,·) - G_{B_{r₂}}(0,·))` lies in `S_{B_{r₁}}(t)` (`Δ ŵ_t ≤ μ` since
`ΔG_B(0,·) = -δ_0`; `ŵ_t ≥ -t G_{B_{r₁}}(0,·)` since `v^{B_{r₂}}_t ≥ -t G_{B_{r₂}}(0,·)`), so
`v^{B_{r₁}}_t ≤ ŵ_t`. Since `G_{B_{r₁}}(0,x) - G_{B_{r₂}}(0,x) = (2π)⁻¹ log (r₁/r₂)` on `closedBall 0 r₁ \ {0}`, in
Lean take `ŵ_t = v^{B_{r₂}}_t + (t/2π) log (r₂/r₁)` (the printed formula differs at the pole by the junk value of
`greenFunction`). Uses: `ObstacleCompatibilityShiftStep` with Lemma A.1 (general form) at radius `r₂`
(`v^{B_{r₂}}_t ∈ S_{B_{r₂}}(t)`), the explicit Green function of a centred disc
`G_{B_r}(0,x) = (2π)⁻¹ log (r/|x|)` (cf. `greenBall`, Defs/Green.lean), `Δ (const) = 0`. -/
def ObstacleCompatibilityStep1 : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ t : ℝ, 0 < t → ∀ r₁ r₂ : ℝ, 0 < r₁ → r₁ ≤ r₂ → r₂ ≤ R →
    ∀ x ∈ ball (0 : ℂ) r₁, x ≠ 0 → odometer μ r₁ 0 t x ≤ odometer μ r₂ 0 t x

/-- **Lemma A.6, Step 2 (eq:monotonicity-domains-two, lines 3882-3890).** If `0 < s₁ ≤ s₂ ≤ R` and
`closure Λ^{B_{s₂}}_t ⊂ B_{s₁}`, then `u^{B_R}_t ≤ ū` on `B_R \ {0}`, where `ū = u^{B_{s₁}}_t` on `B_{s₁}` and
`ū = 0` on `B_R \ B_{s₁}`. Printed argument: by Step 1, `Λ^{B_{s₁}}_t ⊆ Λ^{B_{s₂}}_t`, so `u^{B_{s₁}}_t` vanishes
near `∂B_{s₁}` and its extension `ū` by `0` satisfies `Δ ū = -t δ_0 + μ|_{Λ^{B_{s₁}}} + ν_{s₁}|_{∂Λ^{B_{s₁}}}`
on `B_R`; by eq:laplacian-of-v-general at `s₁` and `R` (`ν_{s₁} ≤ μ`), `u^{B_R}_t - ū` is subharmonic on
`Λ^{B_R}_t` (the poles cancel; use the continuous representative at `0`) and `≤ 0` on `∂Λ^{B_R}_t`
(`u^{B_R}_t = 0` there, by Lemma A.4 on `∂B_R`, and `ū ≥ 0`); the maximum principle gives `u^{B_R}_t ≤ ū` on
`Λ^{B_R}_t`, and off `Λ^{B_R}_t`, `u^{B_R}_t = 0 ≤ ū`. Uses: Step 1, `ObstacleCompatibilityShiftStep`,
Lemmas A.1, A.4 and `ShiftedOdometerLaplacianGeneral` (general forms, at radii `s₁` and `R`), the maximum
principle for continuous subharmonic functions. -/
def ObstacleCompatibilityStep2 : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ t : ℝ, 0 < t → ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ ≤ s₂ → s₂ ≤ R →
    closure (cluster μ s₂ 0 t) ⊆ ball 0 s₁ →
      (∀ x ∈ ball (0 : ℂ) s₁, x ≠ 0 → odometer μ R 0 t x ≤ odometer μ s₁ 0 t x) ∧
      (∀ x ∈ ball (0 : ℂ) R, x ∉ ball (0 : ℂ) s₁ → odometer μ R 0 t x ≤ 0)

/-! ## The reduction -/

/-- **Lemma A.6 from its steps** (line 3892). -/
theorem obstacleCompatibility_of_steps (h1 : ObstacleCompatibilityStep1) (h2 : ObstacleCompatibilityStep2) :
    ObstacleCompatibilityStmt := by
  intro μ hμ R βm βp hV t ht s₁ hs₁ hs₁R s₂ hs₂ hcl s hs
  have hR : 0 < R := hs₁.trans_le hs₁R
  obtain ⟨hA, hB⟩ := h2 μ hμ R βm βp hR hV t ht s₁ s₂ hs₁ hs₂.1 hs₂.2 hcl
  have key : ∀ s ∈ Icc s₁ R, cluster μ s 0 t = cluster μ s₁ 0 t := by
    intro s hs
    ext x
    simp only [mem_cluster_iff]
    constructor
    · rintro ⟨hxs, hx⟩
      by_cases hx0 : x = 0
      · exact ⟨hx0 ▸ mem_ball_self hs₁, Or.inl hx0⟩
      · have hpos := hx.resolve_left hx0
        have hsR := h1 μ hμ R βm βp hR hV t ht s R (hs₁.trans_le hs.1) hs.2 le_rfl x hxs hx0
        by_cases hxs₁ : x ∈ ball (0 : ℂ) s₁
        · exact ⟨hxs₁, Or.inr (hpos.trans_le (hsR.trans (hA x hxs₁ hx0)))⟩
        · exact absurd (hB x (ball_subset_ball hs.2 hxs) hxs₁) (not_le.2 (hpos.trans_le hsR))
    · rintro ⟨hxs₁, hx⟩
      refine ⟨ball_subset_ball hs.1 hxs₁, ?_⟩
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      · exact Or.inr ((hx.resolve_left hx0).trans_le
          (h1 μ hμ R βm βp hR hV t ht s₁ s hs₁ hs.1 hs.2 x hxs₁ hx0))
  rw [key s hs, key s₂ hs₂]

end HarmonicBalls
