import HarmonicBalls.Defs.LBM
import HarmonicBalls.Proofs.Sec6.CompactHittingStopping

/-! # Exit times under the Liouville clock

A finite exit from an open domain transforms by a continuous increasing clock.
The inverse-clock argument follows MatedCRT.Proofs.Sec4.ConvergenceDivisible.TimeChange
and MatedCRT.Proofs.LBM.TimeChangeContinuity.
-/

namespace HarmonicBalls

open Set Filter MarkovProcess
open scoped ENNReal NNReal

private theorem clockInverse_clockValue {f : ℝ≥0 → ℝ} (hzero : f 0 = 0)
    (hmono : StrictMono f) (r : ℝ≥0) :
    clockInverse f (Real.toNNReal (f r)) = r := by
  have hfr : 0 ≤ f r := by simpa [hzero] using hmono.monotone (show 0 ≤ r from bot_le)
  have hcoe : (Real.toNNReal (f r) : ℝ) = f r := Real.coe_toNNReal _ hfr
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro s hrs
    unfold clockInverse
    apply csInf_le'
    rw [hcoe]
    exact hmono hrs
  · unfold clockInverse
    apply le_csInf
    · refine ⟨r + 1, ?_⟩
      rw [hcoe]
      exact hmono (by simp)
    · intro s hs
      rw [hcoe] at hs
      exact (hmono.lt_iff_lt.mp hs).le

private theorem clock_surjective {f : ℝ≥0 → ℝ} (hf : IsTimeChangeClock f) :
    Function.Surjective (fun s => Real.toNNReal (f s)) := by
  intro t
  obtain ⟨s, hs⟩ := (hf.tendsto_atTop.eventually (eventually_ge_atTop (t : ℝ))).exists
  have ht : (t : ℝ) ∈ Icc (f 0) (f s) := by
    constructor
    · simpa only [hf.map_zero] using t.coe_nonneg
    · exact hs
  obtain ⟨u, _, hu⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ s from bot_le)
    hf.continuous.continuousOn ht
  refine ⟨u, ?_⟩
  change Real.toNNReal (f u) = t
  rw [hu]
  simp only [Real.toNNReal_coe]

/-- A finite Brownian exit is sent to the corresponding clock value. -/
theorem lbmExitTime_eq_clockValue {F : ContinuousPath ℂ → ℝ≥0 → ℝ}
    {b : ContinuousPath ℂ} {D : Set ℂ} (hD : IsOpen D)
    (hF : IsTimeChangeClock (F b)) (hfin : ContinuousPath.exitTime D b ≠ ⊤) :
    lbmExitTime F D b =
      (Real.toNNReal (F b (ContinuousPath.exitTime D b).toNNReal) : ℝ≥0∞) := by
  let τ := (ContinuousPath.exitTime D b).toNNReal
  have hout : b τ ∉ D := Section6.coordinate_exitTime_notMem hD b hfin
  apply le_antisymm
  · unfold lbmExitTime pathExitTime
    apply sInf_le
    refine ⟨Real.toNNReal (F b τ), rfl, ?_⟩
    change b (clockInverse (F b) (Real.toNNReal (F b τ))) ∉ D
    rw [clockInverse_clockValue hF.map_zero hF.strictMono]
    exact hout
  · unfold lbmExitTime pathExitTime
    apply le_sInf
    rintro _ ⟨t, rfl, ht⟩
    obtain ⟨r, hr⟩ := clock_surjective hF t
    have hinv : clockInverse (F b) t = r := by
      rw [← hr, clockInverse_clockValue hF.map_zero hF.strictMono]
    have hle : τ ≤ r := by
      have hexit := ContinuousPath.exitTime_le_of_notMem D b r (by
        simpa [liouvilleBrownianPath, hinv] using ht)
      exact (ENNReal.toNNReal_le_toNNReal hfin ENNReal.coe_ne_top).2 hexit
    rw [← hr]
    exact_mod_cast Real.toNNReal_le_toNNReal (hF.strictMono.monotone hle)

end HarmonicBalls
