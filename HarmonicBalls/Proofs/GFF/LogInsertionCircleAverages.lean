import HarmonicBalls.Proofs.GFF.LogInsertionReconstruction
import HarmonicBalls.Proofs.GFF.BonannoNormalizedVersion
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgKolm

/-! # Circle averages of logarithmic insertions

The distribution-valued GFF and circle mollifiers are due to Leonardo Bonanno.
The logarithmic potential identity uses his Fubini and circle-average results. -/

noncomputable section
open MeasureTheory Filter Topology
namespace HarmonicBalls

/-- The insertion pairing is minus the logarithmic potential, scaled by its coefficient. -/
theorem mollAvg_logInsertion_eq_logPot (z w : ℂ) (a r : ℝ) (n : ℕ) :
    LQGMetric.CircleAvg.mollAvg (logInsertionDistribution z a) n w r =
      -a * LQGMetric.CircleAvg.logPot (LQGMetric.CircleAvg.circBump n w r) z := by
  rw [LQGMetric.CircleAvg.mollAvg_eq, logInsertionDistribution_apply,
    LQGMetric.CircleAvg.logPot, ← integral_const_mul]
  congr 1
  funext x
  rw [norm_sub_rev z x]
  ring

/-- The actual mollified insertion converges, including circles meeting the root. -/
theorem tendsto_mollAvg_logInsertion (z w : ℂ) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => LQGMetric.CircleAvg.mollAvg (logInsertionDistribution z a) n w r)
      atTop (𝓝 (a * Real.log (max r ‖w - z‖))) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hz : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n / r) atTop (𝓝 0) := by
    simpa using hp.div_const r
  have ht : Tendsto (fun n : ℕ => ∫ t, LQGMetric.bumpTest n 0 t *
      LQGMetric.CircleAvg.circLog w r (z - t)) atTop
      (𝓝 (LQGMetric.CircleAvg.circLog w r z)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine squeeze_zero_norm (fun n => ?_) hz
    simpa only [Real.norm_eq_abs, abs_abs] using
      LQGMetric.CircleAvg.abs_integral_bump_circLog_sub_le hr n w z
  have hs := ht.const_mul a
  rw [LQGMetric.CircleAvg.circLog_eq_log_max hr] at hs
  convert hs using 1
  funext n
  rw [mollAvg_logInsertion_eq_logPot, LQGMetric.CircleAvg.logPot_circBump]
  ring

/-- The chosen circle average equals the insertion's proven mollifier limit. -/
theorem circleAvg_logInsertion (z w : ℂ) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    LQGMetric.circleAvg (logInsertionDistribution z a) r w =
      a * Real.log (max r ‖w - z‖) :=
  LQGMetric.CircleAvg.circleAvg_eq_of_tendsto (tendsto_mollAvg_logInsertion z w a hr)

/-- For each fixed circle, the reconstructed GFF plus an insertion has the
raw GFF circle average plus the explicit logarithmic correction. -/
theorem IsWholePlaneGFF.ae_circleAvg_reconstructedGFF_add_logInsertion
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (z w : ℂ) (a : ℝ)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, LQGMetric.circleAvg
      (reconstructedGFF hC ω + logInsertionDistribution z a) r w =
      hcirc ω r w + a * Real.log (max r ‖w - z‖) := by
  filter_upwards [LQGMetric.CircleAvg.ae_tendsto_mollAvg
      hh.reconstructedGFF_normalized.1 w hr,
    hh.ae_circleAvg_reconstructedGFF hr w] with ω ⟨b, hb⟩ hc
  have hsum := hb.add (tendsto_mollAvg_logInsertion z w a hr)
  have hsum' : Tendsto (fun n => LQGMetric.CircleAvg.mollAvg
      (reconstructedGFF hC ω + logInsertionDistribution z a) n w r)
      atTop (𝓝 (b + a * Real.log (max r ‖w - z‖))) := by
    convert hsum using 1
    funext n
    simp only [LQGMetric.CircleAvg.mollAvg_eq, add_apply]
  rw [LQGMetric.CircleAvg.circleAvg_eq_of_tendsto hb] at hc
  rw [LQGMetric.CircleAvg.circleAvg_eq_of_tendsto hsum', hc]

/-- The unit-circle average of the inserted normalized GFF. -/
theorem IsWholePlaneGFF.ae_circleAvg_one_zero_reconstructedGFF_add_logInsertion
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (z : ℂ) (a : ℝ) :
    ∀ᵐ ω ∂P, LQGMetric.circleAvg
      (reconstructedGFF hC ω + logInsertionDistribution z a) 1 0 =
      a * Real.log (max 1 ‖z‖) := by
  filter_upwards [hh.ae_circleAvg_reconstructedGFF_add_logInsertion z 0 a one_pos,
    hh.ae_circleAvg_reconstructedGFF one_pos 0,
    hh.ae_circleAvg_one_zero_reconstructedGFF] with ω h hraw hzero
  rw [hzero] at hraw
  simpa only [hraw, zero_add, zero_sub, norm_neg] using h

#print axioms IsWholePlaneGFF.ae_circleAvg_reconstructedGFF_add_logInsertion
#print axioms IsWholePlaneGFF.ae_circleAvg_one_zero_reconstructedGFF_add_logInsertion
#print axioms tendsto_mollAvg_logInsertion
#print axioms circleAvg_logInsertion
end HarmonicBalls
