import HarmonicBalls.Proofs.Sec9.DiscCirclePotentialRegularity
import HarmonicBalls.Proofs.Sec9.GreenCircleCutoffIntegral
import HarmonicBalls.Proofs.Potential.GreenPotentialExceptionalSet

/-!
# Disc circle tests and Green potentials

A mean-value inequality for negative circle potentials bounds the Green potential off the center.
-/

namespace HarmonicBalls

open Metric Filter Topology Set MeasureTheory

/-- Shrinking circle tests bound the Green potential at a point distinct from the center. -/
theorem greenPotential_le_of_circle_tests
    {R : ℝ} {x z : ℂ} {r : ℕ → ℝ} {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hx : x ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R) (hxz : x ≠ z)
    (hμ : μ (ball (0 : ℂ) R)ᶜ = 0) (hatom : μ {x} = 0)
    (hr : ∀ n, 0 < r n) (hanti : Antitone r) (hrlim : Tendsto r atTop (𝓝 0))
    (hsub : ∀ n, closedBall x (r n) ⊆ ball 0 R)
    (htest : ∀ n, μ.real univ * (-greenPotential (ball 0 R)
        (Section6.normalizedCircleMeasure x (r n)) z) ≤
      ∫ y, -greenPotential (ball 0 R) (Section6.normalizedCircleMeasure x (r n)) y ∂μ) :
    Integrable (greenFunction (ball 0 R) x) μ ∧
    (∫⁻ y, Function.update (fun y => ENNReal.ofReal |greenFunction (ball 0 R) x y|)
      x ⊤ y ∂μ) < ⊤ ∧
    greenPotential (ball 0 R) μ x ≤ μ.real univ * greenFunction (ball 0 R) z x := by
  let C : ℕ → ℂ → ℝ := fun n y => Real.circleAverage (greenFunction (ball 0 R) y) x (r n)
  have hball : ∀ᵐ y ∂μ, y ∈ ball (0 : ℂ) R := ae_iff.mpr hμ
  have hceq : ∀ n, ∀ᵐ y ∂μ, C n y =
      greenPotential (ball 0 R) (Section6.normalizedCircleMeasure x (r n)) y := by
    intro n
    filter_upwards [hball] with y hy
    change C n y = ∫ w, greenFunction (ball 0 R) y w ∂(Section6.normalizedCircleMeasure x (r n))
    rw [← discCirclePotential_eq_integral (hr n) (hsub n) hy]
    dsimp [C]
    rw [circleAverage_greenFunction_ball_eq_log_max (hr n) hy (hsub n)]
    simp [discCirclePotential, greatestHarmonicMinorantBall_comm]
  have hcint : ∀ n, Integrable (C n) μ := by
    intro n
    have hh := (continuousOn_discCirclePotential (hr n) (hsub n)).integrableOn_compact
      (μ := μ) (isCompact_closedBall (0 : ℂ) R)
    have hae : ∀ᵐ y ∂μ, y ∈ closedBall (0 : ℂ) R := hball.mono fun _ hy => ball_subset_closedBall hy
    change Integrable _ (μ.restrict (closedBall (0 : ℂ) R)) at hh
    rw [Measure.restrict_eq_self_of_ae_mem hae] at hh
    apply hh.congr
    filter_upwards [hball] with y hy
    dsimp [C]
    rw [circleAverage_greenFunction_ball_eq_log_max (hr n) hy (hsub n)]
    simp [discCirclePotential, greatestHarmonicMinorantBall_comm]
  have hn : ∀ n, ∀ᵐ y ∂μ, 0 ≤ C n y := fun n => Filter.Eventually.of_forall fun y =>
    Real.circleAverage_nonneg_of_nonneg (fun w _ => greenFunction_nonneg isBounded_ball y w)
  have hzEq : ∀ n, C n z = greenPotential (ball 0 R)
      (Section6.normalizedCircleMeasure x (r n)) z := by
    intro n
    change C n z = ∫ w, greenFunction (ball 0 R) z w ∂(Section6.normalizedCircleMeasure x (r n))
    rw [← discCirclePotential_eq_integral (hr n) (hsub n) hz]
    dsimp [C]
    rw [circleAverage_greenFunction_ball_eq_log_max (hr n) hz (hsub n)]
    simp [discCirclePotential, greatestHarmonicMinorantBall_comm]
  have hle : ∀ n, (∫ y, C n y ∂μ) ≤ μ.real univ * C n z := by
    intro n
    have hh := htest n
    rw [← hzEq n] at hh
    have heq : (∫ y, -greenPotential (ball 0 R) (Section6.normalizedCircleMeasure x (r n)) y ∂μ) =
        -(∫ y, C n y ∂μ) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [hceq n] with y hy
      rw [hy]
    rw [heq] at hh
    linarith
  have ht := lintegral_circleAverage_greenFunction_ball_tendsto hx hμ hr hanti hrlim hsub
  have hzt := (circleAverage_greenFunction_ball_monotone_tendsto hx hz hr hanti hrlim hsub).2
  simp [hxz] at hzt
  have hbound : (∫⁻ y, if x = y then ⊤ else
      ENNReal.ofReal (greenFunction (ball 0 R) y x) ∂μ) ≤
      ENNReal.ofReal (μ.real univ) * ENNReal.ofReal (greenFunction (ball 0 R) z x) := by
    apply le_of_tendsto_of_tendsto' ht (ENNReal.Tendsto.const_mul hzt (Or.inr ENNReal.ofReal_ne_top))
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hcint n) (hn n)]
    rw [← ENNReal.ofReal_mul (measureReal_nonneg)]
    exact ENNReal.ofReal_le_ofReal (hle n)
  have hfin : (∫⁻ y, if x = y then ⊤ else
      ENNReal.ofReal (greenFunction (ball 0 R) y x) ∂μ) < ⊤ :=
    lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hae : ∀ᵐ y ∂μ, y ≠ x := ae_iff.mpr (by simpa using hatom)
  have hfin' : (∫⁻ y, ENNReal.ofReal (greenFunction (ball 0 R) x y) ∂μ) < ⊤ := by
    apply lt_of_le_of_lt _ hfin
    apply lintegral_mono_ae
    filter_upwards [hae] with y hy
    simp [Ne.symm hy, greenFunction_ball_comm]
  have hi : Integrable (greenFunction (ball 0 R) x) μ := by
    refine ⟨((measurable_greenFunction_ball_uncurry R).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun y =>
      greenFunction_nonneg isBounded_ball x y)]
    exact hfin'
  have hext : (∫⁻ y, Function.update (fun y => ENNReal.ofReal |greenFunction (ball 0 R) x y|)
      x ⊤ y ∂μ) < ⊤ := by
    apply lt_of_le_of_lt _ hfin
    apply lintegral_mono_ae
    filter_upwards [hae] with y hy
    simp [hy, Ne.symm hy, abs_of_nonneg (greenFunction_nonneg isBounded_ball x y),
      greenFunction_ball_comm]
  refine ⟨hi, hext, ?_⟩
  have heq : (∫⁻ y, if x = y then ⊤ else
      ENNReal.ofReal (greenFunction (ball 0 R) y x) ∂μ) =
      ENNReal.ofReal (greenPotential (ball 0 R) μ x) := by
    rw [← lintegral_greenKernelExtended_eq isBounded_ball hatom hi]
    apply lintegral_congr
    intro y
    simp [greenKernelExtended, eq_comm, greenFunction_ball_comm]
  rw [heq, ← ENNReal.ofReal_mul measureReal_nonneg] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg measureReal_nonneg (greenFunction_nonneg isBounded_ball z x))).mp hbound

/-- Circle-potential mean-value inequalities imply the off-center Green-potential bound. -/
theorem greenPotential_le_of_all_circle_tests
    {R : ℝ} {x z : ℂ} {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hx : x ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R) (hxz : x ≠ z)
    (hμ : μ (ball (0 : ℂ) R)ᶜ = 0) (hatom : μ {x} = 0)
    (htest : ∀ r : ℝ, 0 < r → closedBall x r ⊆ ball 0 R →
      μ.real univ * (-greenPotential (ball 0 R) (Section6.normalizedCircleMeasure x r) z) ≤
        ∫ y, -greenPotential (ball 0 R) (Section6.normalizedCircleMeasure x r) y ∂μ) :
    Integrable (greenFunction (ball 0 R) x) μ ∧
    (∫⁻ y, Function.update (fun y => ENNReal.ofReal |greenFunction (ball 0 R) x y|)
      x ⊤ y ∂μ) < ⊤ ∧
    greenPotential (ball 0 R) μ x ≤ μ.real univ * greenFunction (ball 0 R) z x := by
  let δ : ℝ := (R - ‖x‖) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith [mem_ball_zero_iff.mp hx]
  let r : ℕ → ℝ := fun n => δ / (n + 1)
  have hr : ∀ n, 0 < r n := by intro n; dsimp [r]; positivity
  have hanti : Antitone r := by
    intro i j hij
    dsimp [r]
    exact div_le_div_of_nonneg_left hδ.le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hrlim : Tendsto r atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
    simpa [r, div_eq_mul_inv, mul_comm] using h
  have hsub : ∀ n, closedBall x (r n) ⊆ ball 0 R := by
    intro n
    apply closedBall_subset_ball'
    have hle : r n ≤ δ := by
      dsimp [r]
      exact div_le_self hδ.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
    rw [dist_zero_right]
    dsimp [δ] at *
    linarith [mem_ball_zero_iff.mp hx]
  exact greenPotential_le_of_circle_tests hx hz hxz hμ hatom hr hanti hrlim hsub
    (fun n => htest (r n) (hr n) (hsub n))

/-- A finite nonatomic measure on a set compactly contained in a disc obeys the off-center
Green-potential bound when its negative circle potentials satisfy the mean-value inequalities. -/
theorem greenPotential_restrict_le_of_circle_tests
    {R : ℝ} {z : ℂ} {A : Set ℂ} {μ : Measure ℂ}
    (hz : z ∈ ball (0 : ℂ) R) (hA : closure A ⊆ ball 0 R)
    (hfin : μ A ≠ ⊤) (hatom : ∀ x, μ {x} = 0)
    (htest : ∀ x ∈ ball (0 : ℂ) R, x ≠ z → ∀ r : ℝ, 0 < r →
      closedBall x r ⊆ ball 0 R →
      μ.real A * (-greenPotential (ball 0 R) (Section6.normalizedCircleMeasure x r) z) ≤
        ∫ y in A, -greenPotential (ball 0 R) (Section6.normalizedCircleMeasure x r) y ∂μ) :
    ∀ x ∈ ball (0 : ℂ) R, x ≠ z →
      IntegrableOn (greenFunction (ball 0 R) x) A μ ∧
      (∫⁻ y in A, Function.update (fun y => ENNReal.ofReal |greenFunction (ball 0 R) x y|)
        x ⊤ y ∂μ) < ⊤ ∧
      greenPotential (ball 0 R) (μ.restrict A) x ≤ μ.real A * greenFunction (ball 0 R) z x := by
  intro x hx hxz
  have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hfin
  have hsupport : (μ.restrict A) (ball (0 : ℂ) R)ᶜ = 0 := by
    rw [Measure.restrict_apply isOpen_ball.measurableSet.compl]
    have hempty : (ball (0 : ℂ) R)ᶜ ∩ A = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hy.1 (hA (subset_closure hy.2))
    rw [hempty, measure_empty]
  have hxatom : (μ.restrict A) {x} = 0 := by
    apply le_antisymm
    · exact (Measure.restrict_le_self {x}).trans (le_of_eq (hatom x))
    · exact bot_le
  have h := greenPotential_le_of_all_circle_tests hx hz hxz hsupport hxatom (by
    intro r hr hsub
    simpa only [measureReal_restrict_apply_univ] using htest x hx hxz r hr hsub)
  exact ⟨h.1, h.2.1, by simpa only [measureReal_restrict_apply_univ] using h.2.2⟩

end HarmonicBalls
