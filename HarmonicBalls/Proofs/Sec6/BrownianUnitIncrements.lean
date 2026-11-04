import HarmonicBalls.Proofs.Sec6.BrownianIncrementBlocks
import HarmonicBalls.Proofs.Sec6.BrownianBallCrossing
import Mathlib.Probability.BorelCantelli

/-! # Unit increments of Brownian motion -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory MarkovProcess Filter Set
open scoped ENNReal NNReal

/-- Consecutive unit increments of real Brownian motion are independent. -/
theorem iIndepFun_realBrownian_unit_increments (x : ℝ) :
    iIndepFun (fun n : ℕ => fun ω : ContinuousPath ℝ => ω (n + 1) - ω n)
      (brownianMotion x) := by
  have hi := iIndepFun_realBrownian_increment_blocks (S := fun _ : ℕ => Unit) x
    (fun n _ => (n : NNReal)) (fun n _ => (n : NNReal) + 1)
    (by intro i s; exact le_add_of_nonneg_right zero_le_one)
    (by
      intro i j hij s t
      rcases lt_or_gt_of_ne hij with h | h
      · left
        exact_mod_cast h
      · right
        exact_mod_cast h)
  have h := hi.comp (fun _ f => f ()) (fun _ => measurable_pi_apply ())
  change iIndepFun (fun n : ℕ => fun ω : ContinuousPath ℝ => ω (n + 1) - ω n)
    (brownianMotion x) at h
  exact h

/-- Every unit increment has the standard Gaussian distribution. -/
theorem realBrownian_unit_increment_hasLaw (x : ℝ) (n : ℕ) :
    HasLaw (fun ω : ContinuousPath ℝ => ω ((n : NNReal) + 1) - ω n)
      (gaussianReal 0 1) (brownianMotion x) := by
  have h := (isPreBrownianReal_brownianMotion x).hasLaw_sub ((n : NNReal) + 1) n
  change HasLaw (fun ω : ContinuousPath ℝ =>
    (ω ((n : NNReal) + 1) - x) - (ω n - x)) _ _ at h
  simpa [nndist_eq_nnnorm, sub_sub_sub_cancel_right] using h

/-- Real Brownian motion almost surely has a unit increment exceeding any
fixed level. -/
theorem ae_exists_realBrownian_unit_increment_gt (x c : ℝ) :
    ∀ᵐ ω ∂(brownianMotion x), ∃ n : ℕ, c < ω ((n : NNReal) + 1) - ω n := by
  let A : ℕ → Set (ContinuousPath ℝ) := fun n =>
    {ω | c < ω ((n : NNReal) + 1) - ω n}
  have hmeas : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_lt measurable_const
      ((ContinuousPath.measurable_coordinateProcess _).sub
        (ContinuousPath.measurable_coordinateProcess _))
  have hind : iIndepSet A (brownianMotion x) := by
    apply (iIndepSet_iff_meas_biInter hmeas).2
    intro s
    apply (iIndepFun_realBrownian_unit_increments x).meas_biInter
    intro n hn
    exact ⟨Ioi c, measurableSet_Ioi, rfl⟩
  have hmeasure : ∀ n, brownianMotion x (A n) = gaussianReal 0 1 (Ioi c) := by
    intro n
    have h := (realBrownian_unit_increment_hasLaw x n).map_eq
    have hm : Measurable (fun ω : ContinuousPath ℝ => ω ((n : NNReal) + 1) - ω n) :=
      (ContinuousPath.measurable_coordinateProcess _).sub
        (ContinuousPath.measurable_coordinateProcess _)
    rw [← h, Measure.map_apply hm measurableSet_Ioi]
    rfl
  have hpos : gaussianReal 0 1 (Ioi c) ≠ 0 := by
    intro hz
    have hv := (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : NNReal) ≠ 0)) hz
    simp at hv
  have hsum : (∑' n, brownianMotion x (A n)) = ∞ := by
    simp only [hmeasure]
    exact ENNReal.tsum_const_eq_top_of_ne_zero hpos
  have hlim := measure_limsup_eq_one hmeas hind hsum
  have hml : MeasurableSet (limsup A atTop) := by
    rw [limsup_eq_iInf_iSup_of_nat]
    exact MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun n =>
      MeasurableSet.iUnion fun _ => hmeas n
  have hae : ∀ᵐ ω ∂(brownianMotion x), ω ∈ limsup A atTop := by
    apply (ae_iff_measure_eq hml.nullMeasurableSet).2
    change brownianMotion x (limsup A atTop) = brownianMotion x Set.univ
    simpa using hlim
  filter_upwards [hae] with ω hω
  exact (mem_limsup_iff_frequently_mem.mp hω).exists

/-- Planar Brownian motion exits every ball in finite time almost surely. -/
theorem ae_planarBrownianMotion_exitTime_ball_lt_top (x : ℂ) (R : ℝ) :
    ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime (Metric.ball x R) ω < ∞ := by
  have hm : Measurable (fun ω : ContinuousPath ℂ => (reImPath ω).1) :=
    measurable_fst.comp measurable_reImPath
  have hs : MeasurableSet {p : ContinuousPath ℝ |
      ∃ n : ℕ, 2 * R < p ((n : NNReal) + 1) - p n} := by
    simp only [ofPred_exists]
    exact MeasurableSet.iUnion fun n => measurableSet_lt measurable_const
      ((ContinuousPath.measurable_coordinateProcess _).sub
        (ContinuousPath.measurable_coordinateProcess _))
  have hmap : ∀ᵐ p ∂((planarBrownianMotion x).map
      (fun ω => (reImPath ω).1)), ∃ n : ℕ, 2 * R < p ((n : NNReal) + 1) - p n := by
    rw [planarBrownianMotion_map_re]
    exact ae_exists_realBrownian_unit_increment_gt x.re (2 * R)
  have hae := (ae_map_iff hm.aemeasurable hs).mp hmap
  filter_upwards [hae] with ω hω
  obtain ⟨n, hn⟩ := hω
  apply lt_top_iff_ne_top.mpr
  intro htop
  have h₁ := ContinuousPath.mem_of_lt_exitTime (Metric.ball x R) ω (n : NNReal) (by
    rw [htop]; exact ENNReal.coe_lt_top)
  have h₂ := ContinuousPath.mem_of_lt_exitTime (Metric.ball x R) ω ((n : NNReal) + 1) (by
    rw [htop]; exact ENNReal.coe_lt_top)
  rw [Metric.mem_ball, dist_eq_norm] at h₁ h₂
  have ha := (Complex.abs_re_le_norm (ω (n : NNReal) - x)).trans_lt h₁
  have hb := (Complex.abs_re_le_norm (ω ((n : NNReal) + 1) - x)).trans_lt h₂
  simp only [Complex.sub_re] at ha hb
  simp only [reImPath_fst_apply] at hn
  have ha' := abs_lt.mp ha
  have hb' := abs_lt.mp hb
  linarith

/-- Planar Brownian motion crosses the inner circle strictly before leaving a
larger concentric ball. -/
theorem ae_planarBrownian_ball_crossing_unconditional {x : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    ∀ᵐ ω ∂(planarBrownianMotion x),
      ContinuousPath.exitTime (Metric.ball x r) ω <
        ContinuousPath.exitTime (Metric.ball x R) ω ∧
      ω ((ContinuousPath.exitTime (Metric.ball x r) ω).toNNReal) ∈ Metric.sphere x r :=
  ae_planarBrownian_ball_crossing hr hrR
    ((ae_planarBrownianMotion_exitTime_ball_lt_top x R).mono fun _ h => ne_top_of_lt h)

end HarmonicBalls.Section6
