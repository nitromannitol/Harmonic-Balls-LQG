import HarmonicBalls.Steps.Sec3.Basic
import HarmonicBalls.Draft.Section4
import HarmonicBalls.Proofs.Potential.GreenPositivity

/-!
# Section 4: shared material for the reductions of Proposition 4.1 and Lemmas 4.2-4.3

Glue used by the reductions `<result>_of_steps` of Section 4 (sec:basic-properties-cluster, lines 663-804) to the
statements of Sections 2-3 and to Appendix A.

## Contents

* `ae_isLocallyFiniteMeasure_volumeGrowth_of_exponents`: the almost sure event of Section 3.2 (Input I2 and the Radon
  property of `μ_h`) for exponents `β⁻, β⁺` fixed in advance in the ranges of [C1]. Lemma 4.2 needs the exponents
  before the probability space, since its Hölder exponent is deterministic.
* `volumeGrowthExponentPlus`, `volumeGrowthExponentMinus`: a choice of such exponents depending on `γ, α₀` only.
* Glue on the obstacle problem of `B_r` with pole `z`: the least supersolution vanishes on `∂B_r` where the odometer
  does; the odometer vanishes on `B_r \ Λ_{B_r;z}(t)`; it is continuous on `closedBall 0 r \ {z}`.
* `restrict_add_restrict_frontier_le`: for `Λ` open and `ν ≤ μ` on `B`, the measure `μ|_Λ + ν|_{∂Λ}` of Lemma 3.2 is
  `≤ μ` on `B`.
* Lower bounds for `G_{B_r}(z,·)`: it tends to `+∞` at the pole (`exists_le_greenFunction_ball_near_pole`) and is
  bounded below by a positive constant on every ball `B_s(z)` with `|z| + s < r`
  (`exists_pos_le_greenFunction_ball`).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-! ## The almost sure event with fixed exponents -/

/-- The exponent `β⁺ = min {(2-γ)²/2, γ(Q-α₀)} / 2`, in the range `(0, min {(2-γ)²/2, γ(Q-α₀)})` of [C1]. -/
noncomputable def volumeGrowthExponentPlus (γ α₀ : ℝ) : ℝ := min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) / 2

/-- The exponent `β⁻ = max {(2+γ)²/2, γ(Q-α₀)} + 1`, in the range `(max {(2+γ)²/2, γ(Q-α₀)}, ∞)` of [C1]. -/
noncomputable def volumeGrowthExponentMinus (γ α₀ : ℝ) : ℝ := max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) + 1

theorem volumeGrowthExponents_mem {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) :
    0 < volumeGrowthExponentPlus γ α₀ ∧
      volumeGrowthExponentPlus γ α₀ < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) ∧
      max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < volumeGrowthExponentMinus γ α₀ := by
  have h1 : 0 < (2 - γ) ^ 2 / 2 := by
    have : 0 < 2 - γ := by linarith
    positivity
  have h2 : 0 < γ * (lqgQ γ - α₀) := mul_pos hγ (sub_pos.2 hα)
  have hm : 0 < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) := lt_min h1 h2
  exact ⟨half_pos hm, half_lt_self hm, lt_add_one _⟩

/-- **The almost sure event of Section 3.2 with exponents fixed in advance** (lines 3528-3530). For `0 < γ < 2`,
`α₀ < Q` and exponents `β⁺ ∈ (0, min {(2-γ)²/2, γ(Q-α₀)})`, `β⁻ > max {(2+γ)²/2, γ(Q-α₀)}`, almost surely `μ_h` is
a Radon measure satisfying the volume growth condition eq:volume-growth on every ball `B_R`. From Input I2
(`LQGVolumeGrowthAllScalesStmt`) and the Radon property in `IsLQGMeasureOfField`. -/
theorem ae_isLocallyFiniteMeasure_volumeGrowth_of_exponents (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) {βplus βminus : ℝ} (hβp : 0 < βplus)
    (hβp' : βplus < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)))
    (hβm : max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < βminus) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧ ∀ R : ℝ, 0 < R → VolumeGrowth (μ ω) R βminus βplus := by
  have hβm0 : 0 < βminus :=
    ((mul_pos hγ (sub_pos.2 hα)).trans_le (le_max_right _ _)).trans hβm
  filter_upwards [hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ, hμ] with ω hω hlim
  refine ⟨hlim.isLocallyFiniteMeasure, fun R hR => ?_⟩
  obtain ⟨r₀, hr₀, h⟩ := hω R hR βplus βminus hβp hβp' hβm
  exact ⟨hβm0, hβp, r₀, hr₀, h⟩

/-! ## Glue on the obstacle problem -/

section Obstacle

variable {μ : Measure ℂ} {r t : ℝ} {z x : ℂ}

theorem notMem_ball_of_mem_sphere (hx : x ∈ sphere (0 : ℂ) r) : x ∉ ball (0 : ℂ) r := by
  rw [mem_sphere] at hx
  rw [mem_ball, hx]
  exact lt_irrefl _

/-- Where the odometer vanishes on `∂B_r`, so does the least supersolution (`G_{B_r}(z,·) = 0` off `B_r`). -/
theorem leastSupersolution_eq_zero_of_mem_sphere (hu : ∀ x ∈ sphere (0 : ℂ) r, odometer μ r z t x = 0)
    (hx : x ∈ sphere (0 : ℂ) r) : leastSupersolution μ r z t x = 0 := by
  have h := hu x hx
  rwa [odometer, greenFunction_of_notMem_right (notMem_ball_of_mem_sphere hx), mul_zero, add_zero] at h

/-- The odometer vanishes on `B_r \ Λ_{B_r;z}(t)` (eq:non-co-set, line 592, and `v ≥ -t G_{B_r}(z,·)`). -/
theorem odometer_eq_zero_of_notMem_cluster (ht : 0 ≤ t) (hx : x ∈ ball (0 : ℂ) r) (hxΛ : x ∉ cluster μ r z t) :
    odometer μ r z t x = 0 := by
  rw [mem_cluster_iff, not_and, not_or] at hxΛ
  obtain ⟨hxz, hpos⟩ := hxΛ hx
  exact le_antisymm (not_lt.1 hpos) (odometer_nonneg ht (ball_subset_closedBall hx) hxz)

/-- The odometer `u = v + t G_{B_r}(z,·)` is continuous on `closedBall 0 r \ {z}` if `v` is continuous on the closed
ball (Lemma 3.1), by Proposition 2.3. -/
theorem continuousOn_odometer (h23 : GreenFunctionBallStmt) (hr : 0 < r) (hz : z ∈ ball (0 : ℂ) r)
    (hv : ContinuousOn (leastSupersolution μ r z t) (closedBall 0 r)) :
    ContinuousOn (odometer μ r z t) (closedBall 0 r \ {z}) :=
  (hv.mono sdiff_subset).add (continuousOn_const.mul (continuousOn_greenFunction_ball_of_stmt h23 hr hz))

end Obstacle

/-- For `Λ` open and `ν ≤ μ` on `B`, the measure `μ|_Λ + ν|_{∂Λ}` (the Laplacian of the least supersolution,
Lemma 3.2) is `≤ μ` on `B`: `Λ` and `∂Λ` are disjoint. -/
theorem restrict_add_restrict_frontier_le {μ ν : Measure ℂ} {Λ B : Set ℂ} (hΛ : IsOpen Λ) (hB : MeasurableSet B)
    (hle : ν.restrict B ≤ μ.restrict B) :
    (μ.restrict Λ + ν.restrict (frontier Λ)).restrict B ≤ μ.restrict B := by
  rw [Measure.restrict_add, Measure.restrict_comm hB, Measure.restrict_comm hB]
  calc (μ.restrict B).restrict Λ + (ν.restrict B).restrict (frontier Λ)
      ≤ (μ.restrict B).restrict Λ + (μ.restrict B).restrict (frontier Λ) :=
        add_le_add_right (Measure.restrict_mono subset_rfl hle) _
    _ = (μ.restrict B).restrict (Λ ∪ frontier Λ) :=
        (Measure.restrict_union (disjoint_frontier_iff_isOpen.2 hΛ).symm
          isClosed_frontier.measurableSet).symm
    _ ≤ μ.restrict B := Measure.restrict_le_self

/-! ## Lower bounds for the Green function of a ball -/

/-- `G_{B_r}(z,·) → +∞` at the pole: for every `K` there is `ε ∈ (0, r - |z|)` with `K ≤ G_{B_r}(z,x)` for
`0 < |x - z| < ε` (from `log_div_le_greenFunction`; cf. lines 703-708). -/
theorem exists_le_greenFunction_ball_near_pole {r : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) (K : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < r - ‖z‖ ∧
      ∀ x : ℂ, 0 < ‖x - z‖ → ‖x - z‖ < ε → K ≤ greenFunction (ball 0 r) z x := by
  rw [mem_ball_zero_iff] at hz
  set ρ := (r - ‖z‖) / 2 with hρ_def
  have hρ : 0 < ρ := by rw [hρ_def]; linarith
  have he : 0 < Real.exp (-(2 * Real.pi * K)) := Real.exp_pos _
  refine ⟨min (ρ / 2) (ρ * Real.exp (-(2 * Real.pi * K))), lt_min (half_pos hρ) (mul_pos hρ he), ?_, ?_⟩
  · exact (min_le_left _ _).trans_lt (by rw [hρ_def]; linarith)
  intro x hx0 hxε
  have hxρ2 : ‖x - z‖ < ρ / 2 := hxε.trans_le (min_le_left _ _)
  have hxe : ‖x - z‖ < ρ * Real.exp (-(2 * Real.pi * K)) := hxε.trans_le (min_le_right _ _)
  have hsub : closedBall x ρ ⊆ ball (0 : ℂ) r := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    rw [mem_ball_zero_iff]
    calc ‖y‖ = ‖(y - x) + (x - z) + z‖ := by congr 1; ring
      _ ≤ ‖y - x‖ + ‖x - z‖ + ‖z‖ := norm_add₃_le
      _ < r := by rw [hρ_def] at hy hxρ2; linarith
  have hzx0 : 0 < ‖z - x‖ := by rwa [norm_sub_rev]
  have hzxρ : ‖z - x‖ < ρ := by rw [norm_sub_rev]; linarith
  have hG := log_div_le_greenFunction isBounded_ball hρ hsub hzx0 hzxρ
  have hlog : 2 * Real.pi * K < Real.log (ρ / ‖z - x‖) := by
    rw [Real.lt_log_iff_exp_lt (div_pos hρ hzx0), lt_div_iff₀ hzx0, norm_sub_rev]
    calc Real.exp (2 * Real.pi * K) * ‖x - z‖
        < Real.exp (2 * Real.pi * K) * (ρ * Real.exp (-(2 * Real.pi * K))) :=
          mul_lt_mul_of_pos_left hxe (Real.exp_pos _)
      _ = ρ := by rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  have hpi : 0 < (2 * Real.pi)⁻¹ := inv_pos.2 (by positivity)
  calc K = (2 * Real.pi)⁻¹ * (2 * Real.pi * K) := by field_simp
    _ ≤ (2 * Real.pi)⁻¹ * Real.log (ρ / ‖z - x‖) := mul_le_mul_of_nonneg_left hlog.le hpi.le
    _ ≤ greenFunction (ball 0 r) z x := hG

/-- `G_{B_r}(z,·)` is bounded below by a positive constant on `B_s(z) \ {z}` when `|z| + s < r` (Proposition 2.3:
positivity and continuity off the pole, compactness; near the pole `exists_le_greenFunction_ball_near_pole`).
Used for the second claim of Proposition 4.1 (line 710). -/
theorem exists_pos_le_greenFunction_ball (h23 : GreenFunctionBallStmt) {r s : ℝ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) r) (hs : ‖z‖ + s < r) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ ball z s, x ≠ z → c ≤ greenFunction (ball 0 r) z x := by
  have hr : 0 < r := (norm_nonneg z).trans_lt (mem_ball_zero_iff.1 hz)
  obtain ⟨η, hη, -, hnear⟩ := exists_le_greenFunction_ball_near_pole hz 1
  set A := closedBall z s \ ball z η with hA_def
  have hAc : IsCompact A := (isCompact_closedBall z s).diff isOpen_ball
  have hAsub : A ⊆ closedBall (0 : ℂ) r \ {z} := by
    rintro x ⟨hx, hxη⟩
    refine ⟨?_, fun h => hxη (by rw [mem_singleton_iff.1 h]; exact mem_ball_self hη)⟩
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [mem_closedBall_zero_iff]
    calc ‖x‖ = ‖(x - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ r := by linarith
  have hfar : ∀ x ∈ ball z s, ¬ ‖x - z‖ < η → x ∈ A := fun x hx hxη =>
    ⟨ball_subset_closedBall hx, by rw [mem_ball, dist_eq_norm]; exact hxη⟩
  have hnear' : ∀ x : ℂ, x ≠ z → ‖x - z‖ < η → 1 ≤ greenFunction (ball 0 r) z x := fun x hxz hxη =>
    hnear x (norm_pos_iff.2 (sub_ne_zero.2 hxz)) hxη
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · refine ⟨1, one_pos, fun x hx hxz => hnear' x hxz ?_⟩
    by_contra hxη
    have := hfar x hx hxη
    rw [hAe] at this
    exact this
  obtain ⟨x₀, hx₀A, hmin⟩ :=
    hAc.exists_isMinOn hAne ((continuousOn_greenFunction_ball_of_stmt h23 hr hz).mono hAsub)
  have hx₀ := hAsub hx₀A
  have hx₀b : x₀ ∈ ball (0 : ℂ) r := by
    have h1 := hx₀A.1
    rw [mem_closedBall, dist_eq_norm] at h1
    rw [mem_ball_zero_iff]
    calc ‖x₀‖ = ‖(x₀ - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖x₀ - z‖ + ‖z‖ := norm_add_le _ _
      _ < r := by linarith
  have hpos : 0 < greenFunction (ball 0 r) z x₀ := (h23 r hr z hz).2.1 x₀ hx₀b hx₀.2
  refine ⟨min 1 (greenFunction (ball 0 r) z x₀), lt_min one_pos hpos, fun x hx hxz => ?_⟩
  by_cases hxη : ‖x - z‖ < η
  · exact (min_le_left _ _).trans (hnear' x hxz hxη)
  · exact (min_le_right _ _).trans (hmin (hfar x hx hxη))

end HarmonicBalls
