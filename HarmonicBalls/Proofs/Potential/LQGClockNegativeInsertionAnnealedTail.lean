import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveInsertionCutoff
import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveInsertionInnerMoment

/-! # Negative insertion density increments

A dyadic increment separates into a weighted zero-insertion increment and a
correction supported inside the smoothing ball.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- A negative insertion changes its dyadic weight only inside the smoothing
ball; its correction is bounded by a positive power of the smoothing radius. -/
theorem nonpositive_insertion_dyadic_density_increment
    (h : ℝ → ℂ → ℝ) (γ α ε : ℝ) (z : ℂ)
    (hγ : 0 ≤ γ) (hα : α ≤ 0) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hz : ‖z‖ ≤ 1 / 2) :
    let q := -γ * α
    let a := (max (ε / 2) ‖z‖) ^ q
    let b := (max ε ‖z‖) ^ q
    let X := fun r : ℝ => r ^ (γ ^ 2 / 2) * Real.exp
      (γ * LatticeProb.Gauss.fieldCircleAverage 0 h r z)
    let Y := fun r : ℝ => r ^ (γ ^ 2 / 2) * Real.exp
      (γ * LatticeProb.Gauss.fieldCircleAverage α h r z)
    0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧
      0 ≤ b - a ∧ b - a ≤ ε ^ q ∧
      (ε ≤ ‖z‖ → b - a = 0) ∧
      Y (ε / 2) - Y ε = a * (X (ε / 2) - X ε) - (b - a) * X ε ∧
      0 ≤ (b - a) * X ε ∧ (b - a) * X ε ≤ ε ^ q * X ε := by
  dsimp only
  have hq : 0 ≤ -γ * α := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hγ) hα
  have he2 : 0 < ε / 2 := by positivity
  have hm1 : 0 < max (ε / 2) ‖z‖ := lt_max_of_lt_left he2
  have hm2 : 0 < max ε ‖z‖ := lt_max_of_lt_left hε
  have hmax : max (ε / 2) ‖z‖ ≤ max ε ‖z‖ := max_le_max_right _ (by linarith)
  have hmaxone : max ε ‖z‖ ≤ 1 := by apply max_le <;> linarith
  have ha : 0 ≤ (max (ε / 2) ‖z‖) ^ (-γ * α) := Real.rpow_nonneg hm1.le _
  have hab : (max (ε / 2) ‖z‖) ^ (-γ * α) ≤ (max ε ‖z‖) ^ (-γ * α) :=
    Real.rpow_le_rpow hm1.le hmax hq
  have hb : (max ε ‖z‖) ^ (-γ * α) ≤ 1 := Real.rpow_le_one hm2.le hmaxone hq
  have herr : (max ε ‖z‖) ^ (-γ * α) - (max (ε / 2) ‖z‖) ^ (-γ * α) ≤
      ε ^ (-γ * α) := by
    by_cases hzε : ε ≤ ‖z‖
    · rw [max_eq_right hzε, max_eq_right (by linarith : ε / 2 ≤ ‖z‖), sub_self]
      exact Real.rpow_nonneg hε.le _
    · rw [max_eq_left (le_of_not_ge hzε)]
      linarith
  have hzero (hzε : ε ≤ ‖z‖) :
      (max ε ‖z‖) ^ (-γ * α) - (max (ε / 2) ‖z‖) ^ (-γ * α) = 0 := by
    rw [max_eq_right hzε, max_eq_right (by linarith : ε / 2 ≤ ‖z‖), sub_self]
  have hfactor (r : ℝ) (hr : 0 < r) :
      r ^ (γ ^ 2 / 2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α h r z) =
      (max r ‖z‖) ^ (-γ * α) *
        (r ^ (γ ^ 2 / 2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 h r z)) := by
    have hlog : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z r =
        Real.log (max r ‖z‖) := by
      simpa using (LatticeProb.Gauss.circleAverage_log_norm_sub_eq z 0 hr)
    have heq : γ * LatticeProb.Gauss.fieldCircleAverage α h r z =
        (-γ * α) * Real.log (max r ‖z‖) +
          γ * LatticeProb.Gauss.fieldCircleAverage 0 h r z := by
      dsimp [LatticeProb.Gauss.fieldCircleAverage]
      rw [hlog]
      ring_nf
    rw [heq, Real.exp_add, Real.rpow_def_of_pos (lt_max_of_lt_left hr)]
    ring_nf
  have hX : 0 ≤ ε ^ (γ ^ 2 / 2) * Real.exp
      (γ * LatticeProb.Gauss.fieldCircleAverage 0 h ε z) :=
    mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le
  refine ⟨ha, hab, hb, sub_nonneg.mpr hab, herr, hzero, ?_, ?_, ?_⟩
  · rw [hfactor (ε / 2) he2, hfactor ε hε]
    ring_nf
  · exact mul_nonneg (sub_nonneg.mpr hab) hX
  · exact mul_le_mul_of_nonneg_right herr hX

/-- The smoothing-dependent insertion correction has an annealed power bound,
uniformly in the outer cutoff. -/
theorem exists_annealed_nonpositive_insertion_correction_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α : ℝ) (hγ : 0 < γ) (hγtwo : γ < 2) (hα : α ≤ 0) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C < ∞ ∧ ∀ {ε δ : ℝ},
      0 < ε → ε ≤ 1 / 2 → δ ≤ 1 / 2 →
      (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) 1,
        ENNReal.ofReal ({z : ℂ | ‖z‖ < δ}.indicator (fun z =>
          ((max ε ‖z‖) ^ (-γ * α) - (max (ε / 2) ‖z‖) ^ (-γ * α)) *
          (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) ε z))) (q.2 s.toNNReal)))
        ∂(P.prod (planarBrownianMotion x))) ≤
      ENNReal.ofReal (ε ^ (-γ * α)) * ((ENNReal.ofReal ε) ^ (1 / 2 : ℝ) * C) := by
  obtain ⟨C, hC0, hC, hbound⟩ :=
    exists_lintegral_prod_brownian_inner_nonpositive_inserted_le hh x γ 0 hγ hγtwo le_rfl
  refine ⟨C, hC0, hC, ?_⟩
  intro ε δ hε hεhalf hδ
  calc
    _ ≤ ENNReal.ofReal (ε ^ (-γ * α)) *
        (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) 1,
          ENNReal.ofReal ({z : ℂ | ‖z‖ < ε}.indicator (fun z =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) ε z)) (q.2 s.toNNReal)))
          ∂(P.prod (planarBrownianMotion x))) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono
      intro q
      dsimp only
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono
      intro s
      let z := q.2 s.toNNReal
      change ENNReal.ofReal ({z : ℂ | ‖z‖ < δ}.indicator _ z) ≤
        ENNReal.ofReal (ε ^ (-γ * α)) * ENNReal.ofReal ({z : ℂ | ‖z‖ < ε}.indicator _ z)
      by_cases hzδ : ‖z‖ < δ
      · have hzhalf : ‖z‖ ≤ 1 / 2 := le_trans (le_of_lt hzδ) hδ
        have hstep := nonpositive_insertion_dyadic_density_increment
          (hcirc q.1) γ α ε z hγ.le hα hε hεhalf hzhalf
        dsimp only at hstep
        by_cases hzε : ‖z‖ < ε
        · rw [Set.indicator_of_mem (show z ∈ {w : ℂ | ‖w‖ < δ} from hzδ), Set.indicator_of_mem (show z ∈ {w : ℂ | ‖w‖ < ε} from hzε),
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hε.le _)]
          exact ENNReal.ofReal_le_ofReal hstep.2.2.2.2.2.2.2.2
        · have hzero := hstep.2.2.2.2.2.1 (le_of_not_gt hzε)
          rw [Set.indicator_of_mem (show z ∈ {w : ℂ | ‖w‖ < δ} from hzδ), Set.indicator_of_notMem (show z ∉ {w : ℂ | ‖w‖ < ε} from hzε), hzero, zero_mul,
            ENNReal.ofReal_zero, mul_zero]
      · rw [Set.indicator_of_notMem (show z ∉ {w : ℂ | ‖w‖ < δ} from hzδ), ENNReal.ofReal_zero]
        exact zero_le
    _ ≤ _ := by
      gcongr
      exact hbound hε hεhalf hε hεhalf

end HarmonicBalls
