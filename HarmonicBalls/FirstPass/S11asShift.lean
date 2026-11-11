import HarmonicBalls.FirstPass.S11ai.RootedInstance

/-!
# Block 3 of the measure half of the rooted local rescaling: the physical Cameron–Martin shift

Let `u` be an admissible root shift at `(α₀, z, b)` (`FirstPassS11ai.AdmissibleRootShift`): `u(w) = -α₀ log|z + w|` on
`ball 0 b`, with compact support and zero unit-circle mean. In the physical frame the shift is `x ↦ u(x - z)`, which equals
`-α₀ log|x|` on `ball z b` (the background insertion at the physical origin, Duplantier–Sheffield). Subtracting the
constant multiple of a smooth bump `χ` supported in `ball p (‖z‖/2)`, `p = -z/‖z‖`, with unit-circle mean one about `0` and
mean zero about `z` (Armitage–Gardiner: mean-value normalisation), gives a smooth compactly supported `f` with zero
unit-circle mean about the origin and about the root `z`, and `f = u(· - z)` on `closedBall z b`. This is the shift of the
rooted Cameron–Martin reweighting in Block 4.

Deterministic: no probabilistic input. The only Mathlib facts used are circle averages of continuous functions,
periodicity of `circleMap`, and the `ContDiffBump` construction.
-/

open Metric Filter Topology Set Complex
open scoped ContDiff Real

namespace FirstPassS11asShift

/-- A continuous nonnegative function whose value at `circleMap 0 1 θ₀` is positive has positive unit-circle mean about `0`.
Proof: the integrand is positive on an arc of length `2δ` around `θ₀`; over one period it is nonnegative. -/
theorem circleAverage_pos_of_pos_at {g : ℂ → ℝ} (hg : Continuous g) (hnn : ∀ x, 0 ≤ g x) {θ₀ : ℝ}
    (hθ : 0 < g (circleMap 0 1 θ₀)) : 0 < Real.circleAverage g 0 1 := by
  have hh : Continuous fun θ : ℝ => g (circleMap 0 1 θ) := hg.comp (continuous_circleMap 0 1)
  have hper : Function.Periodic (fun θ : ℝ => g (circleMap 0 1 θ)) (2 * π) :=
    (periodic_circleMap 0 1).comp g
  have hopen : IsOpen {θ : ℝ | (0 : ℝ) < g (circleMap 0 1 θ)} := isOpen_lt continuous_const hh
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hopen.mem_nhds hθ)
  have hδpos : 0 < min (ε / 2) π := lt_min (half_pos hε) Real.pi_pos
  have hδπ : min (ε / 2) π ≤ π := min_le_right _ _
  have hδε : min (ε / 2) π < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  set δ : ℝ := min (ε / 2) π with hδ
  have hpos : ∀ θ ∈ Ioo (θ₀ - δ) (θ₀ + δ), 0 < g (circleMap 0 1 θ) := by
    intro θ hθ'
    have hmem : θ ∈ ball θ₀ ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [hθ'.1, hθ'.2]
    exact hball hmem
  have hA : 0 < ∫ θ in (θ₀ - δ)..(θ₀ + δ), g (circleMap 0 1 θ) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hh.intervalIntegrable _ _) hpos (by linarith)
  have hB : 0 ≤ ∫ θ in (θ₀ + δ)..(θ₀ - δ + 2 * π), g (circleMap 0 1 θ) :=
    intervalIntegral.integral_nonneg (by linarith) fun θ _ => hnn _
  have hsplit : ∫ θ in (θ₀ - δ)..(θ₀ - δ + 2 * π), g (circleMap 0 1 θ) =
      (∫ θ in (θ₀ - δ)..(θ₀ + δ), g (circleMap 0 1 θ)) +
        ∫ θ in (θ₀ + δ)..(θ₀ - δ + 2 * π), g (circleMap 0 1 θ) :=
    (intervalIntegral.integral_add_adjacent_intervals (hh.intervalIntegrable _ _)
      (hh.intervalIntegrable _ _)).symm
  have hper' : ∫ θ in (θ₀ - δ)..(θ₀ - δ + 2 * π), g (circleMap 0 1 θ) =
      ∫ θ in (0 : ℝ)..(2 * π), g (circleMap 0 1 θ) := by
    simpa only [zero_add] using hper.intervalIntegral_add_eq (θ₀ - δ) 0
  have htot : 0 < ∫ θ in (0 : ℝ)..(2 * π), g (circleMap 0 1 θ) := by
    rw [← hper']
    linarith
  unfold Real.circleAverage
  rw [smul_eq_mul]
  exact mul_pos (inv_pos.2 (by positivity)) htot

/-- **Circle bump.** For `z ≠ 0` there is a smooth, compactly supported, nonnegative `χ` with unit-circle mean one about `0`,
unit-circle mean zero about `z`, and `χ = 0` on `closedBall z 1`. The bump is a `ContDiffBump` centred at `p = -z/‖z‖`
(a unit vector), with outer radius `‖z‖/2`: its support lies at distance at least `‖z‖` from every point of `closedBall z 1`. -/
theorem exists_circle_bump {z : ℂ} (hz : z ≠ 0) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x, 0 ≤ χ x) ∧
      Real.circleAverage χ 0 1 = 1 ∧ Real.circleAverage χ z 1 = 0 ∧ ∀ x ∈ closedBall z 1, χ x = 0 := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hzc : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hzn.ne'
  obtain ⟨p, hp⟩ : ∃ p : ℂ, p = -(z / (‖z‖ : ℂ)) := ⟨_, rfl⟩
  have he : ‖z / (‖z‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hzn.le, div_self hzn.ne']
  have hpn : ‖p‖ = 1 := by rw [hp, norm_neg, he]
  have hzeq : (‖z‖ : ℂ) * (z / (‖z‖ : ℂ)) = z := by field_simp
  have hpz : ‖p - z‖ = 1 + ‖z‖ := by
    have hsub : p - z = -((1 + ‖z‖ : ℝ) : ℂ) * (z / (‖z‖ : ℂ)) := by
      rw [hp]
      push_cast
      linear_combination hzeq
    rw [hsub, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg (show (0 : ℝ) ≤ 1 + ‖z‖ by positivity), he, mul_one]
  let B : ContDiffBump p :=
    { rIn := ‖z‖ / 4
      rOut := ‖z‖ / 2
      rIn_pos := div_pos hzn (by norm_num)
      rIn_lt_rOut := by linarith }
  have hB_smooth : ContDiff ℝ (⊤ : ℕ∞) (B : ℂ → ℝ) := B.contDiff
  have hB_compact : HasCompactSupport (B : ℂ → ℝ) := B.hasCompactSupport
  have hB_nonneg : ∀ x, 0 ≤ (B : ℂ → ℝ) x := fun x => B.nonneg
  have hBp : (B : ℂ → ℝ) p = 1 :=
    B.one_of_mem_closedBall (mem_closedBall_self (by positivity))
  -- vanishing on `closedBall z 1`: there `‖x - p‖ ≥ ‖z‖ > ‖z‖/2 = rOut`
  have hBv : ∀ x ∈ closedBall z 1, (B : ℂ → ℝ) x = 0 := by
    intro x hx
    have hx1 : dist x z ≤ 1 := hx
    rw [dist_eq_norm] at hx1
    apply B.zero_of_le_dist
    show ‖z‖ / 2 ≤ dist x p
    rw [dist_eq_norm]
    have htri : ‖p - z‖ ≤ ‖p - x‖ + ‖x - z‖ := by
      have := norm_add_le (p - x) (x - z)
      rwa [sub_add_sub_cancel] at this
    rw [norm_sub_rev p x] at htri
    linarith
  have hcont : Continuous (B : ℂ → ℝ) := hB_smooth.continuous
  have hBz : Real.circleAverage (B : ℂ → ℝ) z 1 = 0 := by
    have hEq : Set.EqOn (B : ℂ → ℝ) (fun _ => (0 : ℝ)) (sphere z |(1 : ℝ)|) := by
      intro x hx
      have hx1 : dist x z = 1 := by rwa [mem_sphere, abs_one] at hx
      exact hBv x (mem_closedBall.2 hx1.le)
    rw [Real.circleAverage_congr_sphere hEq]
    exact Real.circleAverage_const 0 z 1
  have hBpos : 0 < Real.circleAverage (B : ℂ → ℝ) 0 1 := by
    have hcp : circleMap 0 1 (Complex.arg p) = p := by
      have h := Complex.norm_mul_exp_arg_mul_I p
      rw [hpn, Complex.ofReal_one, one_mul] at h
      simpa [circleMap] using h
    apply circleAverage_pos_of_pos_at hcont hB_nonneg (θ₀ := Complex.arg p)
    rw [hcp, hBp]
    exact one_pos
  refine ⟨(Real.circleAverage (B : ℂ → ℝ) 0 1)⁻¹ • (B : ℂ → ℝ), ContDiff.const_smul (Real.circleAverage (B : ℂ → ℝ) 0 1)⁻¹ hB_smooth,
    hB_compact.smul_left (f := fun _ : ℂ => (Real.circleAverage (B : ℂ → ℝ) 0 1)⁻¹), ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 hBpos.le) (hB_nonneg x)
  · rw [Real.circleAverage_smul, smul_eq_mul, inv_mul_cancel₀ hBpos.ne']
  · rw [Real.circleAverage_smul, hBz, smul_zero]
  · intro x hx
    simp [hBv x hx]

/-- **Block 3: the physical-frame Cameron–Martin shift of the rooted field.** For an admissible root shift `u` at
`(α₀, z, b)` there is a smooth compactly supported `f` with zero unit-circle mean about `0` and about `z`, which equals
`u(· - z)` on `closedBall z b` and `-α₀ log‖·‖` on `ball z b`. -/
theorem exists_rooted_shift {α₀ b : ℝ} {z : ℂ} {u : ℂ → ℝ}
    (hu : FirstPassS11ai.AdmissibleRootShift α₀ z b u) :
    ∃ f : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      Real.circleAverage f 0 1 = 0 ∧ Real.circleAverage f z 1 = 0 ∧
      (∀ x ∈ closedBall z b, f x = u (x - z)) ∧ (∀ x ∈ ball z b, f x = -α₀ * Real.log ‖x‖) := by
  obtain ⟨hb, hbz, hb1, hsm, hcs, hcirc, hlog⟩ := hu
  have hzpos : 0 < ‖z‖ := by linarith
  have hz : z ≠ 0 := norm_pos_iff.1 hzpos
  obtain ⟨χ, hχs, hχc, -, hχ0, hχz, hχv⟩ := exists_circle_bump hz
  have hũs : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℂ => u (x - z)) :=
    hsm.comp (contDiff_id.sub contDiff_const)
  have hũc : HasCompactSupport (fun x : ℂ => u (x - z)) :=
    hcs.comp_homeomorph (Homeomorph.subRight z)
  have hũcont : Continuous (fun x : ℂ => u (x - z)) := hũs.continuous
  have hχcont : Continuous χ := hχs.continuous
  -- translation invariance of the unit-circle mean: the mean of `u(· - z)` about `z` is the mean of `u` about `0`
  have htrans : Real.circleAverage (fun x : ℂ => u (x - z)) z 1 = Real.circleAverage u 0 1 := by
    unfold Real.circleAverage
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    simp [circleMap]
  have hχzero : ∀ x ∈ closedBall z b, χ x = 0 := fun x hx =>
    hχv x (closedBall_subset_closedBall (by linarith) hx)
  refine ⟨(fun x : ℂ => u (x - z)) - (Real.circleAverage (fun x : ℂ => u (x - z)) 0 1) • χ, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact hũs.sub (ContDiff.const_smul (Real.circleAverage (fun x : ℂ => u (x - z)) 0 1) hχs)
  · exact hũc.sub (hχc.smul_left (f := fun _ : ℂ => Real.circleAverage (fun x : ℂ => u (x - z)) 0 1))
  · rw [Real.circleAverage_sub hũcont.continuousOn.circleIntegrable'
      (hχcont.const_smul (Real.circleAverage (fun x : ℂ => u (x - z)) 0 1)).continuousOn.circleIntegrable', Real.circleAverage_smul, hχ0, smul_eq_mul, mul_one,
      sub_self]
  · rw [Real.circleAverage_sub hũcont.continuousOn.circleIntegrable'
      (hχcont.const_smul (Real.circleAverage (fun x : ℂ => u (x - z)) 0 1)).continuousOn.circleIntegrable', Real.circleAverage_smul, hχz, htrans, hcirc,
      smul_zero, sub_zero]
  · intro x hx
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hχzero x hx, mul_zero, sub_zero]
  · intro x hx
    have hxz : ‖x - z‖ < b := by
      have := hx
      rw [mem_ball, dist_eq_norm] at this
      exact this
    have hxb : x - z ∈ ball (0 : ℂ) b := by
      rw [mem_ball_zero_iff]
      exact hxz
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hχzero x (ball_subset_closedBall hx), mul_zero, sub_zero]
    rw [hlog (x - z) hxb, add_sub_cancel]

end FirstPassS11asShift
