import HarmonicBalls.Steps.Sec3.Section3
import HarmonicBalls.Proofs.SecA.ObstacleMonotone

/-!
# Section 3: the potential `q_{B_R}`, the substitution of lines 3574-3578, Lemmas 3.1 and 3.3

* `greenPotentialBallLaplacianStep_holds`: `Δ q_{B_R} = -μ` on `B_R` (property 2 of `q_{B_R}`, line 3539; AG01
  Thm 4.3.8) under the volume growth condition. For a test function `φ`,
  `∫ q Δφ = ∫_{B_R} ∫ G_{B_R}(y,x) Δφ(x) dx μ(dy) = -∫ φ dμ` by Fubini and `ΔG_{B_R}(y,·) = -δ_y` (Prop 2.3,
  `greenFunctionBall`); the product integrability comes from `∫ G_{B_R}(y,x) μ(dy) = q(x)` being bounded.
* `obstacleCompatibilityShiftStep_holds`: `w ∈ S_{B_R;z}(t) ↔ w + q ∈ S̃(t)`, `v = ṽ - q` on the closed ball, the
  cluster is the non-coincidence set and the odometers agree.
* `obstacleOdometerZeroBoundaryGeneral_holds` (Lemma A.4, general form).
* `leastSupersolutionMem_proved` (Lemma 3.1) and `clusterMonotone_proved` (Lemma 3.3), with Input I2
  (`LQGVolumeGrowthAllScalesStmt`, worker c2's task) as the only hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory Metric Filter Topology Set Laplacian

universe u

/-- The Green function of `B_R` is jointly Borel measurable. -/
theorem measurable_greenFunction_ball_uncurry (R : ℝ) :
    Measurable (fun p : ℂ × ℂ => greenFunction (ball (0 : ℂ) R) p.1 p.2) := by
  classical
  have heq : (fun p : ℂ × ℂ => greenFunction (ball (0 : ℂ) R) p.1 p.2) = fun p =>
      if p.1 ∈ ball (0 : ℂ) R ∧ p.2 ∈ ball (0 : ℂ) R ∧ p.1 ≠ p.2 then greenBall R p.1 p.2 else 0 := by
    funext p
    split_ifs with h
    · exact greenFunction_ball h.1 h.2.1 h.2.2
    · rw [greenFunction, ite_eq_right_iff]
      exact fun hc => absurd hc h
  rw [heq]
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_ball.preimage measurable_fst).inter
      ((measurableSet_ball.preimage measurable_snd).inter isClosed_diagonal.measurableSet.compl)
  · unfold greenBall
    fun_prop

/-- `y ↦ G_{B_R}(y,x)` is `μ`-integrable on `B_R` for `x` in the closed ball, under the volume growth condition. -/
theorem integrable_greenFunction_ball_left {μ : Measure ℂ} [IsLocallyFiniteMeasure μ] {R βm βp : ℝ} (hR : 0 < R)
    (hV : VolumeGrowth μ R βm βp) {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) R) :
    Integrable (fun y => greenFunction (ball (0 : ℂ) R) y x) (μ.restrict (ball 0 R)) := by
  obtain ⟨hI, -⟩ := greenPotential_ball_holderOnWith hR hV (memLp_top_const (1 : ℝ))
  refine (hI x hx).congr ?_
  filter_upwards with y
  simp only [mul_one]
  exact greenFunction_ball_comm R x y

/-- **`Δ q_{B_R} = -μ` on `B_R`** (`GreenPotentialBallLaplacianStep`). -/
theorem greenPotentialBallLaplacianStep_holds : GreenPotentialBallLaplacianStep := by
  intro μ hμ R βm βp hR hV
  have := hμ
  set q := greenPotentialBall μ R with hqdef
  have hqc : ContinuousOn q (closedBall 0 R) := greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV
  refine ⟨(hqc.mono ball_subset_closedBall).locallyIntegrableOn measurableSet_ball, fun φ hφ => ?_⟩
  have hφc : Continuous φ := hφ.1.continuous
  refine ⟨integrable_zero_measure, hφc.integrable_of_hasCompactSupport hφ.2.1, ?_⟩
  rw [integral_zero_measure, zero_sub]
  set ν := μ.restrict (ball (0 : ℂ) R) with hνdef
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set G : ℂ → ℂ → ℝ := fun y x => greenFunction (ball (0 : ℂ) R) y x with hGdef
  have hΔc : Continuous (Δ φ) := continuous_laplacian_of_contDiff (hφ.1.of_le (by norm_cast))
  have hΔ0 : ∀ x, x ∉ ball (0 : ℂ) R → Δ φ x = 0 := fun x hx =>
    laplacian_eq_zero_of_notMem_tsupport fun h => hx (hφ.2.2 h)
  have hΔi : Integrable (Δ φ) := hΔc.integrable_of_hasCompactSupport (hasCompactSupport_laplacian hφ.2.1)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hqc
  set f : ℂ → ℂ → ℝ := fun x y => G y x * Δ φ x with hfdef
  have hfm : Measurable (Function.uncurry f) :=
    ((measurable_greenFunction_ball_uncurry R).comp (measurable_snd.prodMk measurable_fst)).mul
      (hΔc.measurable.comp measurable_fst)
  have hG0 : ∀ y x, 0 ≤ G y x := fun y x => greenFunction_nonneg isBounded_ball y x
  have hprod : Integrable (Function.uncurry f) (volume.prod ν) := by
    refine (integrable_prod_iff hfm.aestronglyMeasurable).2 ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · by_cases hx : x ∈ ball (0 : ℂ) R
      · show Integrable (fun y => greenFunction (ball (0 : ℂ) R) y x * Δ φ x) ν
        exact (integrable_greenFunction_ball_left hR hV (ball_subset_closedBall hx)).mul_const _
      · have h0 : (fun y => Function.uncurry f (x, y)) = fun _ => 0 := by
          funext y
          simp [hfdef, hΔ0 x hx]
        rw [h0]
        exact integrable_zero _ _ _
    · refine Integrable.mono' (hΔi.norm.const_mul B)
        (hfm.norm.stronglyMeasurable.integral_prod_right' (ν := ν)).aestronglyMeasurable
        (Eventually.of_forall fun x => ?_)
      have hn : (fun y => ‖Function.uncurry f (x, y)‖) = fun y => G y x * ‖Δ φ x‖ := by
        funext y
        simp only [Function.uncurry_apply_pair, hfdef, norm_mul, Real.norm_of_nonneg (hG0 y x)]
      show ‖∫ y, ‖Function.uncurry f (x, y)‖ ∂ν‖ ≤ B * ‖Δ φ x‖
      rw [hn, integral_mul_const]
      by_cases hx : x ∈ ball (0 : ℂ) R
      · have hqx : ∫ y, G y x ∂ν = q x := rfl
        rw [hqx, norm_mul, norm_norm]
        exact mul_le_mul_of_nonneg_right (hB x (ball_subset_closedBall hx)) (norm_nonneg _)
      · rw [hΔ0 x hx]
        simp
  have h1 : ∫ x, q x * Δ φ x = ∫ x, ∫ y, f x y ∂ν := by
    congr 1
    funext x
    rw [integral_mul_const]
    rfl
  rw [h1, integral_integral_swap hprod]
  have h2 : ∀ᵐ y ∂ν, ∫ x, f x y = -φ y := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have h := ((greenFunctionBall R hR y hy).1.2 φ hφ).2.2
    rw [integral_zero_measure, integral_dirac, zero_sub] at h
    exact h
  rw [integral_congr_ae h2, integral_neg]
  congr 1
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hφ.2.2 h)

/-- **The substitution of lines 3574-3578** (`ObstacleCompatibilityShiftStep`). -/
theorem obstacleCompatibilityShiftStep_holds : ObstacleCompatibilityShiftStep := by
  intro μ hμ R βm βp hR hV z hz t ht
  have := hμ
  set q := greenPotentialBall μ R with hqdef
  have hqc : ContinuousOn q (closedBall 0 R) := greenPotentialBallContinuousStep_holds μ hμ R βm βp hR hV
  have hΔq := greenPotentialBallLaplacianStep_holds μ hμ R βm βp hR hV
  have hqloc : LocallyIntegrableOn q (ball 0 R) := hΔq.1
  have hφμ : ∀ φ : ℂ → ℝ, IsTestFunction (ball 0 R) φ → Integrable φ μ := fun φ hφ =>
    hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have hqΔ : ∀ φ : ℂ → ℝ, IsTestFunction (ball 0 R) φ → ∫ x, q x * Δ φ x = -∫ x, φ x ∂μ := fun φ hφ => by
    have h := (hΔq.2 φ hφ).2.2
    rw [integral_zero_measure, zero_sub] at h
    exact h
  have hmem : ∀ w : ℂ → ℝ, w ∈ supersolutions μ R z t ↔
      (fun x => w x + q x) ∈ shiftedSupersolutions μ R z t := by
    intro w
    constructor
    · rintro ⟨hwc, hwL, hwo⟩
      refine ⟨hwc.add hqc, ⟨hwL.1.add hqloc, fun φ hφ hφ0 _ => ?_⟩, fun x hx hxz => ?_⟩
      · have h1 := hwL.2 φ hφ hφ0 (hφμ φ hφ)
        rw [integral_zero_measure]
        have e : (fun x => (w x + q x) * Δ φ x) = fun x => w x * Δ φ x + q x * Δ φ x := by
          funext x; ring
        rw [e, integral_add (integrable_mul_laplacian_of_test hwL.1 hφ)
          (integrable_mul_laplacian_of_test hqloc hφ), hqΔ φ hφ]
        linarith
      · have := hwo x hx hxz
        simp only [obstacle, ← hqdef]
        linarith
    · rintro ⟨hwc, hwL, hwo⟩
      have hwc' : ContinuousOn w (closedBall 0 R) :=
        (hwc.sub hqc).congr fun x _ => by simp
      have e : (fun x => (w x + q x) - q x) = w := funext fun x => add_sub_cancel_right _ _
      have hwloc : LocallyIntegrableOn w (ball 0 R) := e ▸ hwL.1.sub hqloc
      refine ⟨hwc', ⟨hwloc, fun φ hφ hφ0 _ => ?_⟩, fun x hx hxz => ?_⟩
      · have h1 := hwL.2 φ hφ hφ0 integrable_zero_measure
        rw [integral_zero_measure] at h1
        have e' : (fun x => (w x + q x) * Δ φ x) = fun x => w x * Δ φ x + q x * Δ φ x := by
          funext x; ring
        rw [e', integral_add (integrable_mul_laplacian_of_test hwloc hφ)
          (integrable_mul_laplacian_of_test hqloc hφ), hqΔ φ hφ] at h1
        linarith
      · have := hwo x hx hxz
        simp only [obstacle, ← hqdef] at this
        linarith
  obtain ⟨hbdd, -, -, -, -⟩ := obstacleLeastSuperharmonicMajorantGeneral_holds μ hμ R βm βp hR hV z hz t ht
  have hqS : q ∈ shiftedSupersolutions μ R z t :=
    greenPotentialBall_mem_shiftedSupersolutions ht.le hqc hΔq.laplacianLE
  have hls : ∀ x ∈ closedBall (0 : ℂ) R,
      leastSupersolution μ R z t x = shiftedLeastSupersolution μ R z t x - q x := by
    intro x hx
    have himg : (fun w : ℂ → ℝ => w x) '' supersolutions μ R z t =
        (fun a => a - q x) '' ((fun u : ℂ → ℝ => u x) '' shiftedSupersolutions μ R z t) := by
      ext a
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w x + q x, ⟨fun y => w y + q y, (hmem w).1 hw, rfl⟩, by ring⟩
      · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
        refine ⟨fun y => u y - q y, (hmem _).2 ?_, rfl⟩
        convert hu using 1
        funext y
        ring
    rw [leastSupersolution, himg, shiftedLeastSupersolution]
    exact (Monotone.map_csInf_of_continuousAt (continuousAt_id.sub continuousAt_const)
      (fun a b h => sub_le_sub_right h _)
      (⟨q x, q, hqS, rfl⟩ : ((fun u : ℂ → ℝ => u x) '' shiftedSupersolutions μ R z t).Nonempty)
      (hbdd x hx)).symm
  refine ⟨hmem, hls, ?_, fun x hx => ?_⟩
  · ext x
    simp only [cluster, nonCoincidenceSet, obstacle]
    constructor
    · rintro ⟨hxb, h⟩
      refine ⟨hxb, h.imp id fun h => ?_⟩
      rw [hls x (ball_subset_closedBall hxb)] at h
      linarith
    · rintro ⟨hxb, h⟩
      refine ⟨hxb, h.imp id fun h => ?_⟩
      rw [hls x (ball_subset_closedBall hxb)]
      linarith
  · simp only [odometer, shiftedOdometer, obstacle, hls x hx, ← hqdef]
    ring

/-- **Lemma A.4, general radius and pole.** -/
theorem obstacleOdometerZeroBoundaryGeneral_holds : ObstacleOdometerZeroBoundaryGeneral :=
  obstacleOdometerZeroBoundaryGeneral_of_steps greenPotentialBallContinuousStep_holds
    greenPotentialBallLaplacianStep_holds

/-- **Lemma 3.1** (lemma:basic-properties, line 621), given Input I2. -/
theorem leastSupersolutionMem_proved (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) : LeastSupersolutionMemStmt.{u} :=
  leastSupersolutionMem_of_steps hI2 obstacleLeastSuperharmonicMajorantGeneral_holds
    obstacleCompatibilityShiftStep_holds

/-- **Lemma 3.3** (lemma:monotonicity, line 644, with [C13]), given Input I2. -/
theorem clusterMonotone_proved (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) : ClusterMonotoneStmt.{u} :=
  clusterMonotone_of_steps hI2 obstacleMonotoneGeneral_holds obstacleCompatibilityShiftStep_holds

end HarmonicBalls
