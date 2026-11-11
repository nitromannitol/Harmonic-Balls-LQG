import HarmonicBalls.Steps.Sec3.Basic

/-!
# Lemma 3.5 from Appendix A (Lemma A.6 with a general pole)

`ClusterCompatibilityStmt` (Draft/Section3.lean; lemma:cluster-compatibility, line 657): for each `R > 0`, a.s.,
for all `t > 0`, `s₁ ≤ R` and `z ∈ B_{s₁}`, if `closure Λ_{B_{s₂};z}(t) ⊂ B_{s₁}` for some `s₂ ∈ [s₁, R]`, then
`Λ_{B_s;z}(t) = Λ_{B_{s₂};z}(t)` for all `s ∈ [s₁, R]`. The paper derives it from Lemma A.6 (line 3851).

## Gap: Lemma A.6 has pole `0` only

Lemma A.6 and its proof (lines 3838-3895) concern the clusters `Λ^{B_s}_t` with pole `0` ("we will also only consider
the case where `z` is the origin", line 3546); Lemma 3.5 needs every pole `z ∈ B_{s₁}`. Since the balls `B_s`,
`s ∈ [s₁, R]`, are all centred at `0`, neither a translation nor a rescaling reduces the pole `z` to `0`, and the
printed `ObstacleCompatibilityStmt` (pole `0`) does not imply Lemma 3.5. The printed proof does carry over, with one
change in its first step: for `z ≠ 0` the difference `G_{B_{r₁}}(z,·) - G_{B_{r₂}}(z,·)` entering the competitor
`ŵ_t` of eq:intermediate-inequality-monotonicity (line 3868) is harmonic on `B_{r₁}` but no longer constant (for
`z = 0` it is `(2π)⁻¹ log (r₁/r₂)`). This file states the general-pole forms of Steps 1-2 of Lemma A.6
(Steps/SecA/ObstacleCompatibility.lean) as explicit steps, proves the general-pole Lemma A.6 from them (the reduction,
with the pole `z` in place of `0`), and reduces Lemma 3.5 to it. The pole-`0` steps and statement are special cases
(`obstacleCompatibilityStep1_of_pole`, `obstacleCompatibilityStep2_of_pole`, `obstacleCompatibility_of_general`).

## Steps (difficulty in brackets)

* `ObstacleCompatibilityPoleStep1` — eq:monotonicity-domains (lines 3862-3880) with pole `z`:
  `u_{B_{r₁};z}(t) ≤ u_{B_{r₂};z}(t)` on `B_{r₁}` off the pole for `z ∈ B_{r₁}`, `r₁ ≤ r₂ ≤ R`.
* `ObstacleCompatibilityPoleStep2` — eq:monotonicity-domains-two (lines 3882-3890) with pole `z`.

## The reductions (proved)

* `obstacleCompatibilityGeneral_of_steps`: Steps 1-2 give `u_{B_{s₁};z} ≤ u_{B_s;z} ≤ u_{B_R;z} ≤ u_{B_{s₁};z}` on
  `B_{s₁} \ {z}` and `u_{B_s;z} ≤ u_{B_R;z} ≤ 0` on `B_s \ B_{s₁}` (line 3892), hence `Λ_{B_s;z}(t) = Λ_{B_{s₁};z}(t)`
  for every `s ∈ [s₁, R]`.
* `clusterCompatibility_of_steps`: on the a.s. event of Input I2 (`ae_isLocallyFiniteMeasure_volumeGrowth`).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- Lemma A.6 (lemma:appendix-cluster-compatibility, line 3851) for a general pole: under the volume growth condition
on `B_R`, for all `t > 0`, `s₁ ≤ R` and `z ∈ B_{s₁}`, if `closure Λ_{B_{s₂};z}(t) ⊂ B_{s₁}` for some
`s₂ ∈ [s₁, R]`, then `Λ_{B_s;z}(t) = Λ_{B_{s₂};z}(t)` for all `s ∈ [s₁, R]`. The printed Lemma A.6 is the case
`z = 0` (`obstacleCompatibility_of_general`). -/
def ObstacleCompatibilityGeneral : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, VolumeGrowth μ R βminus βplus →
  ∀ t : ℝ, 0 < t → ∀ s₁ : ℝ, s₁ ≤ R → ∀ z ∈ ball (0 : ℂ) s₁,
    ∀ s₂ ∈ Icc s₁ R, closure (cluster μ s₂ z t) ⊆ ball 0 s₁ →
      ∀ s ∈ Icc s₁ R, cluster μ s z t = cluster μ s₂ z t

/-! ## Steps -/

/-- **Lemma A.6, Step 1 with a general pole (eq:monotonicity-domains, lines 3862-3880).** For `r₁ ≤ r₂ ≤ R` and
`z ∈ B_{r₁}`, `u_{B_{r₁};z}(t) ≤ u_{B_{r₂};z}(t)` on `B_{r₁}` off the pole. Printed argument (pole `0`): the
competitor `ŵ_t = v_{B_{r₂};z}(t) - t h_z`, `h_z = G_{B_{r₁}}(z,·) - G_{B_{r₂}}(z,·)`, lies in `S_{B_{r₁};z}(t)`, so
`v_{B_{r₁};z}(t) ≤ ŵ_t`, i.e. `u_{B_{r₁};z}(t) ≤ u_{B_{r₂};z}(t)` (eq:intermediate-inequality-monotonicity,
line 3866). For `z ≠ 0`, `h_z` is not constant; what the argument needs is: (i) `Δ h_z = 0` on `B_{r₁}`
(distributionally; Prop 2.3 at radii `r₁` and `r₂`, the two `δ_z` cancel, `HasLaplacian` restricted from `B_{r₂}` to
`B_{r₁}`), so `Δ ŵ_t = Δ v_{B_{r₂};z}(t) ≤ μ` on `B_{r₁}`; (ii) `h_z` extends continuously to the closed ball
`closedBall 0 r₁` including the pole (removable singularity: `h_z = I_{B_{r₂}}[N_z] - I_{B_{r₁}}[N_z]` off the pole,
the difference of the greatest harmonic minorants of `greenFunction`, or the explicit `greenBall`, Defs/Green.lean),
and `ŵ_t` takes that extension's value at `z` (the printed formula is junk at the pole); (iii) the obstacle:
`ŵ_t ≥ -t G_{B_{r₂}}(z,·) - t h_z = -t G_{B_{r₁}}(z,·)` off the pole. Uses: `ObstacleCompatibilityShiftStep` and
Lemma A.1 (general form, `ObstacleLeastSuperharmonicMajorantGeneral`) at radius `r₂` (`v_{B_{r₂};z}(t) ∈ S_{B_{r₂};z}(t)`,
continuous on the closed ball), Prop 2.3 (`GreenFunctionBallStmt`), `LaplacianLE.mono_set`,
`LaplacianLE.congr_eqOn` (Steps/SecA/Basic.lean). -/
def ObstacleCompatibilityPoleStep1 : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ t : ℝ, 0 < t → ∀ r₁ r₂ : ℝ, r₁ ≤ r₂ → r₂ ≤ R → ∀ z ∈ ball (0 : ℂ) r₁,
    ∀ x ∈ ball (0 : ℂ) r₁, x ≠ z → odometer μ r₁ z t x ≤ odometer μ r₂ z t x

/-- **Lemma A.6, Step 2 with a general pole (eq:monotonicity-domains-two, lines 3882-3890).** If `s₁ ≤ s₂ ≤ R`,
`z ∈ B_{s₁}` and `closure Λ_{B_{s₂};z}(t) ⊂ B_{s₁}`, then `u_{B_R;z}(t) ≤ ū` on `B_R \ {z}`, where
`ū = u_{B_{s₁};z}(t)` on `B_{s₁}` and `ū = 0` on `B_R \ B_{s₁}`. Printed argument (pole `0`), unchanged for a pole
`z`: by Step 1, `Λ_{B_{s₁};z}(t) ⊆ Λ_{B_{s₂};z}(t)`, so `u_{B_{s₁};z}(t)` vanishes near `∂B_{s₁}` and
`Δ ū = -t δ_z + μ|_{Λ_{B_{s₁};z}} + ν_{s₁}|_{∂Λ_{B_{s₁};z}}` on `B_R`; with eq:laplacian-of-v-general at `R`
(`ν_{s₁} ≤ μ`), `u_{B_R;z}(t) - ū` is subharmonic on `Λ_{B_R;z}(t)` (the poles `-t δ_z` cancel) and `≤ 0` on its
boundary (Lemma A.4 on `∂B_R`, `ū ≥ 0`); the maximum principle concludes. Uses: `ObstacleCompatibilityPoleStep1`,
`ObstacleCompatibilityShiftStep`, Lemmas A.1, A.4 and `ShiftedOdometerLaplacianGeneral` (general forms, radii `s₁`
and `R`, pole `z`), the maximum principle for continuous subharmonic functions. -/
def ObstacleCompatibilityPoleStep2 : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
  ∀ t : ℝ, 0 < t → ∀ s₁ s₂ : ℝ, s₁ ≤ s₂ → s₂ ≤ R → ∀ z ∈ ball (0 : ℂ) s₁,
    closure (cluster μ s₂ z t) ⊆ ball 0 s₁ →
      (∀ x ∈ ball (0 : ℂ) s₁, x ≠ z → odometer μ R z t x ≤ odometer μ s₁ z t x) ∧
      (∀ x ∈ ball (0 : ℂ) R, x ∉ ball (0 : ℂ) s₁ → odometer μ R z t x ≤ 0)

/-! ## The reductions -/

/-- **Lemma A.6 with a general pole, from its steps** (line 3892). -/
theorem obstacleCompatibilityGeneral_of_steps (h1 : ObstacleCompatibilityPoleStep1)
    (h2 : ObstacleCompatibilityPoleStep2) : ObstacleCompatibilityGeneral := by
  intro μ hμ R βm βp hV t ht s₁ hs₁R z hz s₂ hs₂ hcl s hs
  have hR : 0 < R := (pos_of_mem_ball hz).trans_le hs₁R
  obtain ⟨hA, hB⟩ := h2 μ hμ R βm βp hR hV t ht s₁ s₂ hs₂.1 hs₂.2 z hz hcl
  have key : ∀ s ∈ Icc s₁ R, cluster μ s z t = cluster μ s₁ z t := by
    intro s hs
    ext x
    simp only [mem_cluster_iff]
    constructor
    · rintro ⟨hxs, hx⟩
      by_cases hxz : x = z
      · exact ⟨hxz ▸ hz, Or.inl hxz⟩
      · have hpos := hx.resolve_left hxz
        have hsR := h1 μ hμ R βm βp hR hV t ht s R hs.2 le_rfl z (ball_subset_ball hs.1 hz) x hxs hxz
        by_cases hxs₁ : x ∈ ball (0 : ℂ) s₁
        · exact ⟨hxs₁, Or.inr (hpos.trans_le (hsR.trans (hA x hxs₁ hxz)))⟩
        · exact absurd (hB x (ball_subset_ball hs.2 hxs) hxs₁) (not_le.2 (hpos.trans_le hsR))
    · rintro ⟨hxs₁, hx⟩
      refine ⟨ball_subset_ball hs.1 hxs₁, ?_⟩
      by_cases hxz : x = z
      · exact Or.inl hxz
      · exact Or.inr ((hx.resolve_left hxz).trans_le
          (h1 μ hμ R βm βp hR hV t ht s₁ s hs.1 hs.2 z hz x hxs₁ hxz))
  rw [key s hs, key s₂ hs₂]

/-- The printed Lemma A.6 (pole `0`) is the case `z = 0` of the general-pole form. -/
theorem obstacleCompatibility_of_general (h : ObstacleCompatibilityGeneral) : ObstacleCompatibilityStmt :=
  fun μ hμ R βm βp hV t ht s₁ hs₁ hs₁R s₂ hs₂ hcl s hs =>
    h μ hμ R βm βp hV t ht s₁ hs₁R 0 (mem_ball_self hs₁) s₂ hs₂ hcl s hs

/-- The pole-`0` Step 1 of Lemma A.6 is the case `z = 0` of `ObstacleCompatibilityPoleStep1`. -/
theorem obstacleCompatibilityStep1_of_pole (h : ObstacleCompatibilityPoleStep1) : ObstacleCompatibilityStep1 :=
  fun μ hμ R βm βp hR hV t ht r₁ r₂ hr₁ hr₁₂ hr₂R x hx hx0 =>
    h μ hμ R βm βp hR hV t ht r₁ r₂ hr₁₂ hr₂R 0 (mem_ball_self hr₁) x hx hx0

/-- The pole-`0` Step 2 of Lemma A.6 is the case `z = 0` of `ObstacleCompatibilityPoleStep2`. -/
theorem obstacleCompatibilityStep2_of_pole (h : ObstacleCompatibilityPoleStep2) : ObstacleCompatibilityStep2 :=
  fun μ hμ R βm βp hR hV t ht s₁ s₂ hs₁ hs₁₂ hs₂R hcl =>
    h μ hμ R βm βp hR hV t ht s₁ s₂ hs₁₂ hs₂R 0 (mem_ball_self hs₁) hcl

/-- **Lemma 3.5 from Appendix A** (Lemma A.6 with a general pole, on the a.s. event of lines 3528-3530). -/
theorem clusterCompatibility_of_general (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hA6 : ObstacleCompatibilityGeneral) : ClusterCompatibilityStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ R hR
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hae] with ω hω
  intro t ht s₁ hs₁R z hz s₂ hs₂ hcl s hs
  exact hA6 (μ ω) hω.1 R βm βp (hω.2 R hR) t ht s₁ hs₁R z hz s₂ hs₂ hcl s hs

/-- **Lemma 3.5 from its steps.** -/
theorem clusterCompatibility_of_steps (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h1 : ObstacleCompatibilityPoleStep1) (h2 : ObstacleCompatibilityPoleStep2) : ClusterCompatibilityStmt.{u} :=
  clusterCompatibility_of_general hI2 (obstacleCompatibilityGeneral_of_steps h1 h2)

end HarmonicBalls
