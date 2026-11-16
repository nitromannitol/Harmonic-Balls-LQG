import HarmonicBalls.Proofs.Sec9.CircleTestObstacleInequality

/-!
# Circle tests for subharmonic balls

The sub-mean-value property supplies the circle-test inequalities and the resulting
Green-potential bound away from the center.
-/

namespace HarmonicBalls

open Metric Set MeasureTheory Filter Topology

/-- The negative potential of a circle source satisfies the sub-mean-value inequality. -/
theorem IsSubharmonicBall.circle_test {μ : Measure ℂ} {A : Set ℂ} {z c : ℂ}
    {R r : ℝ} (hA : IsSubharmonicBall μ A z)
    (hcl : closure A ⊆ ball (0 : ℂ) R) (hr : 0 < r)
    (hsub : closedBall c r ⊆ ball 0 R) :
    μ.real A * (-greenPotential (ball 0 R) (Section6.normalizedCircleMeasure c r) z) ≤
      ∫ y in A, -greenPotential (ball 0 R) (Section6.normalizedCircleMeasure c r) y ∂μ := by
  have h := (hA.2.2.2.2 _
    (neg_greenPotential_normalizedCircleMeasure_mem_testClass hr hsub hcl)).2
  rw [mul_comm] at h
  exact h

/-- Circle tests imply that the restricted source has no atom at the off-center point. -/
theorem measure_singleton_eq_zero_of_circle_tests
    {R : ℝ} {x z : ℂ} {r : ℕ → ℝ} {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hx : x ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R) (hxz : x ≠ z)
    (hμ : μ (ball (0 : ℂ) R)ᶜ = 0)
    (hr : ∀ n, 0 < r n) (hanti : Antitone r) (hrlim : Filter.Tendsto r Filter.atTop (nhds 0))
    (hsub : ∀ n, closedBall x (r n) ⊆ ball 0 R)
    (htest : ∀ n, μ.real univ * (-greenPotential (ball 0 R)
        (Section6.normalizedCircleMeasure x (r n)) z) ≤
      ∫ y, -greenPotential (ball 0 R) (Section6.normalizedCircleMeasure x (r n)) y ∂μ) :
    μ {x} = 0 := by
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
  by_contra hn
  exact (ne_of_lt hfin) (lintegral_extended_greenFunction_ball_eq_top_of_atom hn)

/-- A subharmonic ball satisfies the off-center Green-potential bound. -/
theorem IsSubharmonicBall.greenPotential_restrict_le
    {μ : Measure ℂ} {A : Set ℂ} {z : ℂ} {R : ℝ}
    (hA : IsSubharmonicBall μ A z) (hcl : closure A ⊆ ball (0 : ℂ) R) :
    ∀ x ∈ ball (0 : ℂ) R, x ≠ z →
      IntegrableOn (greenFunction (ball 0 R) x) A μ ∧
      (∫⁻ y in A, Function.update (fun y => ENNReal.ofReal |greenFunction (ball 0 R) x y|)
        x ⊤ y ∂μ) < ⊤ ∧
      greenPotential (ball 0 R) (μ.restrict A) x ≤ μ.real A * greenFunction (ball 0 R) z x := by
  intro x hx hxz
  have hz : z ∈ ball (0 : ℂ) R := hcl (subset_closure hA.2.1)
  have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr (ne_of_lt hA.2.2.2.1)
  have hsupport : (μ.restrict A) (ball (0 : ℂ) R)ᶜ = 0 := by
    rw [Measure.restrict_apply isOpen_ball.measurableSet.compl]
    have hempty : (ball (0 : ℂ) R)ᶜ ∩ A = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hy.1 (hcl (subset_closure hy.2))
    rw [hempty, measure_empty]
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
  have htests : ∀ n, (μ.restrict A).real univ * (-greenPotential (ball 0 R)
      (Section6.normalizedCircleMeasure x (r n)) z) ≤
      ∫ y, -greenPotential (ball 0 R) (Section6.normalizedCircleMeasure x (r n)) y ∂(μ.restrict A) := by
    intro n
    simpa only [measureReal_restrict_apply_univ] using hA.circle_test hcl (hr n) (hsub n)
  have hatom := measure_singleton_eq_zero_of_circle_tests hx hz hxz hsupport hr hanti hrlim hsub htests
  have h := greenPotential_le_of_all_circle_tests hx hz hxz hsupport hatom (by
    intro t ht hsubt
    simpa only [measureReal_restrict_apply_univ] using hA.circle_test hcl ht hsubt)
  exact ⟨h.1, h.2.1, by simpa only [measureReal_restrict_apply_univ] using h.2.2⟩

end HarmonicBalls
