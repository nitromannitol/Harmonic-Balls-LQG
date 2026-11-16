import HarmonicBalls.Proofs.Potential.BrownianUniformBallOccupation

/-! # Endpoint Brownian occupation kernels

Planar Brownian increments and ordered simultaneous visits satisfy endpoint
small-ball bounds with a truncated inverse-time kernel.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- The planar increment small-ball bound with its endpoint inverse-time kernel. -/
theorem planarBrownianMotion_increment_smallBall_le_inv_time (x z : ℂ)
    {s t : ℝ≥0} (hts : t ≠ s) {r : ℝ} (hr : 0 ≤ r) :
    planarBrownianMotion x {b | ‖b t - b s - z‖ < r} ≤
      min 1 (ENNReal.ofReal ((2 / Real.pi) * r ^ 2 / |(t : ℝ) - (s : ℝ)|)) := by
  let u : ℝ := |(t : ℝ) - (s : ℝ)|
  have hu : 0 < u := by
    dsimp [u]
    apply abs_pos.mpr
    exact sub_ne_zero.mpr (by exact_mod_cast hts)
  let a : ℝ := 2 * r / Real.sqrt (2 * Real.pi * u)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hs : (Real.sqrt (2 * Real.pi * u)) ^ 2 = 2 * Real.pi * u :=
    Real.sq_sqrt (by positivity)
  have hs0 : Real.sqrt (2 * Real.pi * u) ≠ 0 := by positivity
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hu0 : u ≠ 0 := ne_of_gt hu
  have haeq : a ^ 2 = (2 / Real.pi) * r ^ 2 / u := by
    dsimp [a]
    field_simp
    nlinarith [hs]
  have h := planarBrownianMotion_increment_smallBall_le_uniform_center x z hts hr
  have hsmall' : planarBrownianMotion x {b | ‖b t - b s - z‖ < r} ≤
      min 1 (ENNReal.ofReal (a ^ 2)) := by
    simpa only [a, u, coe_nndist, Real.dist_eq, ENNReal.ofReal_pow ha] using h
  simpa only [haeq, u] using hsmall'

/-- Ordered simultaneous visits are bounded by a product of truncated endpoint kernels. -/
theorem planarBrownianMotion_joint_ball_le_inv_time (x z : ℂ) {n : ℕ}
    (t : Fin (n + 1) → ℝ≥0) (ht : StrictMono t) {r : ℝ} (hr : 0 ≤ r) :
    planarBrownianMotion x {b | ∀ i, ‖b (t i) - z‖ < r} ≤
      ∏ i : Fin n, min 1 (ENNReal.ofReal ((2 / Real.pi) * (2 * r) ^ 2 /
        |(t i.succ : ℝ) - (t i.castSucc : ℝ)|)) := by
  let f : Fin n → ContinuousPath ℂ → ℂ :=
    fun i b => b (t i.succ) - b (t i.castSucc)
  let A : Set ℂ := ball 0 (2 * r)
  have hi : iIndepFun f (planarBrownianMotion x) :=
    planarBrownianMotion_hasIndepIncrements x n t ht.monotone
  have hsub : {b : ContinuousPath ℂ | ∀ i, ‖b (t i) - z‖ < r} ⊆
      ⋂ i : Fin n, f i ⁻¹' A := by
    intro b hb
    simp only [mem_iInter, mem_preimage]
    intro i
    simp only [f, A, Metric.mem_ball, dist_zero_right]
    have hnorm := norm_sub_le (b (t i.succ) - z) (b (t i.castSucc) - z)
    have heq : (b (t i.succ) - z) - (b (t i.castSucc) - z) =
        b (t i.succ) - b (t i.castSucc) := by abel
    rw [heq] at hnorm
    linarith [hb i.succ, hb i.castSucc]
  calc
    _ ≤ planarBrownianMotion x (⋂ i : Fin n, f i ⁻¹' A) := measure_mono hsub
    _ = ∏ i : Fin n, planarBrownianMotion x (f i ⁻¹' A) := by
      simpa using hi.measure_inter_preimage_eq_mul Finset.univ
        (sets := fun _ => A) (fun _ _ => isOpen_ball.measurableSet)
    _ ≤ _ := by
      apply Finset.prod_le_prod
      intro i _
      have hne : t i.succ ≠ t i.castSucc :=
        ne_of_gt (ht (Fin.castSucc_lt_succ (i := i)))
      have hbound := planarBrownianMotion_increment_smallBall_le_inv_time x 0 hne
        (show 0 ≤ 2 * r by positivity)
      convert hbound using 1
      congr 1
      ext b
      simp [f, A, Metric.mem_ball, dist_zero_right]

/-- The ordered endpoint bound extends to distinct, unordered time tuples. -/
theorem planarBrownianMotion_joint_ball_le_sum_inv_time (x z : ℂ) {n : ℕ}
    (t : Fin (n + 1) → ℝ≥0) (ht : Function.Injective t) {r : ℝ} (hr : 0 ≤ r) :
    planarBrownianMotion x {b | ∀ i, ‖b (t i) - z‖ < r} ≤
      ∑ σ : Equiv.Perm (Fin (n + 1)), ∏ i : Fin n,
        min 1 (ENNReal.ofReal ((2 / Real.pi) * (2 * r) ^ 2 /
          |(t (σ i.succ) : ℝ) - (t (σ i.castSucc) : ℝ)|)) := by
  classical
  let σ := Tuple.sort t
  have hmono : StrictMono (t ∘ σ) :=
    (Tuple.monotone_sort t).strictMono_of_injective (ht.comp σ.injective)
  have h := planarBrownianMotion_joint_ball_le_inv_time x z (t ∘ σ) hmono hr
  have hsets : {b : ContinuousPath ℂ | ∀ i, ‖b (t (σ i)) - z‖ < r} =
      {b : ContinuousPath ℂ | ∀ i, ‖b (t i) - z‖ < r} := by
    ext b
    simp only [mem_ofPred_eq]
    exact (σ.surjective.forall (p := fun i => ‖b (t i) - z‖ < r)).symm
  change planarBrownianMotion x {b | ∀ i, ‖b (t (σ i)) - z‖ < r} ≤ _ at h
  rw [hsets] at h
  have hs : (∏ i : Fin n, min 1 (ENNReal.ofReal ((2 / Real.pi) * (2 * r) ^ 2 /
      |(t (σ i.succ) : ℝ) - (t (σ i.castSucc) : ℝ)|))) ≤
      ∑ τ : Equiv.Perm (Fin (n + 1)), ∏ i : Fin n,
        min 1 (ENNReal.ofReal ((2 / Real.pi) * (2 * r) ^ 2 /
          |(t (τ i.succ) : ℝ) - (t (τ i.castSucc) : ℝ)|)) := by
    apply Finset.single_le_sum (f := fun τ : Equiv.Perm (Fin (n + 1)) =>
      ∏ i : Fin n, min 1 (ENNReal.ofReal ((2 / Real.pi) * (2 * r) ^ 2 /
        |(t (τ i.succ) : ℝ) - (t (τ i.castSucc) : ℝ)|)))
    · intro τ hτ
      exact bot_le
    · exact Finset.mem_univ σ
  exact h.trans (by simpa only [Function.comp_apply] using hs)

/-- Occupation moments are controlled by endpoint kernel integrals. -/
theorem planarBrownianMotion_occupation_moment_le_inv_time (x z : ℂ) {n : ℕ}
    {r : ℝ} (hr : 0 ≤ r) (ν : Measure ℝ≥0)
    [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    (∫⁻ b : ContinuousPath ℂ, (ν {t | ‖b t - z‖ < r}) ^ (n + 1)
      ∂(planarBrownianMotion x)) ≤
    ∫⁻ t : Fin (n + 1) → ℝ≥0,
      ∑ σ : Equiv.Perm (Fin (n + 1)), ∏ i : Fin n,
        min 1 (ENNReal.ofReal ((2 / Real.pi) * (2 * r) ^ 2 /
          |(t (σ i.succ) : ℝ) - (t (σ i.castSucc) : ℝ)|))
      ∂(Measure.pi (fun _ : Fin (n + 1) => ν)) := by
  rw [planarBrownianMotion_occupation_moment_eq]
  apply lintegral_mono_ae
  filter_upwards [ae_injective_pi_of_atomless (n + 1) ν] with t ht
  exact planarBrownianMotion_joint_ball_le_sum_inv_time x z t ht hr

end HarmonicBalls
