import HarmonicBalls.FirstPass.Phase2.RootedShiftedNullTransferSteps
import HarmonicBalls.FirstPass.Phase2.ProfileDecoderDerived
import HarmonicBalls.FirstPass.Phase2.LocalDecoderCommonDerived
import HarmonicBalls.Proofs.Sec6.LQGTranslationCovariance
import HarmonicBalls.Proofs.Sec2.AffineField
import HarmonicBalls.Proofs.Sec2.LQGLimitLocality

/-! # Shifted-root null transfer: the local identification (MQ-lh-29, step L4)

Step L4 of the corrected `RootedShiftedDecoderNullTransfer` (`notes/fp-gaps/MATH-ANSWERS.md`, section MQ-lh-29).
On the ball `B_{5r/4}` around the root, the profile decoder applied to the DMS-shifted α₀-profile, recentred at `z`,
equals `exp(γ h(1,z))` times the γ-decoded profile of the affine-plus-test-function field (Duplantier-Sheffield, LQG
measure of a field with an insertion; Armitage-Gardiner, circle averages). The identity is local: it is obtained by
`IsLQGLimit.restrict_eq` from the translated α₀-limit and the `add_const` limit of the γ-field, which agree on the
dyadic scales below `r/4`.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal Topology

namespace HarmonicBalls

/-- The circle average of the DMS shift is jointly continuous in `(radius, centre)` on positive radii
(Armitage-Gardiner; Jensen's formula `circleAverage_rootShift`). -/
theorem continuousOn_circleAverage_dmsShift (γ : ℝ) (z : ℂ) :
    ContinuousOn (fun p : ℝ × ℂ => Real.circleAverage (dmsShift γ z) p.2 p.1) (Set.Ioi 0 ×ˢ Set.univ) := by
  have hds : dmsShift γ z = LocalDecoderCommon.rootShift γ z := by
    funext w
    simp only [dmsShift, LocalDecoderCommon.rootShift]
    rw [max_comm]
  have hfun : ∀ p : ℝ × ℂ, 0 < p.1 → Real.circleAverage (dmsShift γ z) p.2 p.1 =
      -γ * Real.log (max p.1 ‖p.2 - z‖) +
        γ * Real.circleAverage (fun w : ℂ => Real.log (max 1 ‖w‖)) p.2 p.1 := by
    intro p hp
    rw [hds]
    exact LocalDecoderCommon.circleAverage_rootShift γ hp z p.2
  have hm : ContinuousOn (fun p : ℝ × ℂ => max p.1 ‖p.2 - z‖) (Set.Ioi 0 ×ˢ Set.univ) :=
    (continuous_fst.max (continuous_snd.sub continuous_const).norm).continuousOn
  have h1 : ContinuousOn (fun p : ℝ × ℂ => Real.log (max p.1 ‖p.2 - z‖)) (Set.Ioi 0 ×ˢ Set.univ) :=
    hm.log fun p hp => (lt_max_of_lt_left (Set.mem_Ioi.mp hp.1)).ne'
  have h2 : Continuous (fun p : ℝ × ℂ => Real.circleAverage (fun w : ℂ => Real.log (max 1 ‖w‖)) p.2 p.1) :=
    Section6.continuous_circleAverage_radius_center LocalDecoderCommon.continuous_log_max_one
  have hcont : ContinuousOn (fun p : ℝ × ℂ => -γ * Real.log (max p.1 ‖p.2 - z‖) +
      γ * Real.circleAverage (fun w : ℂ => Real.log (max 1 ‖w‖)) p.2 p.1) (Set.Ioi 0 ×ˢ Set.univ) :=
    (continuousOn_const.mul h1).add (continuousOn_const.mul h2.continuousOn)
  exact hcont.congr fun p hp => hfun p (Set.mem_Ioi.mp hp.1)

/-- **L4a, local profile identity.** For `0 < ε < r/4` and `|y| < 5r/4`, the α₀-field of the profile `G1`
(the DMS-shifted field `hc + Av dmsShift`) at the point `y + z` equals the γ-field of the profile `G2`
(the affine profile `hc(·, · + z) - hc(1, z)` plus the smooth shift `Av gt`) at `y`, plus the constant `hc(1,z)`.
Uses `fieldCircleAverage_dmsShift_add` (L2) and `circleAverage_testShift_eq` (L3). -/
theorem fieldCircleAverage_local_identity {a0 γ r : ℝ} {z : ℂ} {hc : ℝ → ℂ → ℝ} {G1 G2 : ℝ → ℂ → ℝ}
    {gt : ℂ → ℝ} (hz : 3 * r < ‖z‖) (hzu : ‖z‖ < 1 - 3 * r)
    (hEq : Set.EqOn gt (fun y => -a0 * Real.log ‖y + z‖) (closedBall (0 : ℂ) (3 * r / 2)))
    (hG1 : ∀ s x, 0 < s → G1 s x = hc s x + Real.circleAverage (dmsShift γ z) x s)
    (hG2 : ∀ s x, 0 < s → G2 s x = hc s (x + z) - hc 1 z + Real.circleAverage gt x s)
    {ε : ℝ} {y : ℂ} (hε : 0 < ε) (hεr : ε < r / 4) (hy : ‖y‖ < 5 * r / 4) :
    fieldCircleAverage a0 G1 ε (y + z) = fieldCircleAverage γ G2 ε y + hc 1 z := by
  have hn1 : ‖y + z‖ + ε ≤ 1 := by
    have := norm_add_le y z
    linarith
  have hn2 : ε ≤ ‖y + z‖ := by
    have h3 : ‖(y + z) - y‖ ≤ ‖y + z‖ + ‖y‖ := norm_sub_le _ _
    have h4 : (y + z) - y = z := by ring
    rw [h4] at h3
    linarith
  have hA := fieldCircleAverage_dmsShift_add (α₀ := a0) (γ := γ) (z := z) (c := y + z) hc hε hn2 hn1
  have hB := circleAverage_testShift_eq hz hEq hy hε hεr
  have hC : Real.circleAverage (fun x : ℂ => Real.log ‖x‖) y ε = Real.log (max ε ‖y‖) := by
    have := circleAverage_log_norm_sub_eq y 0 hε
    simpa [sub_zero] using this
  have hG1' : fieldCircleAverage a0 G1 ε (y + z) =
      fieldCircleAverage a0 (fun s x => hc s x + Real.circleAverage (dmsShift γ z) x s) ε (y + z) := by
    simp only [fieldCircleAverage, hG1 ε (y + z) hε]
  have hG2' : fieldCircleAverage γ G2 ε y =
      hc ε (y + z) - hc 1 z + Real.circleAverage gt y ε - γ * Real.log (max ε ‖y‖) := by
    simp only [fieldCircleAverage, hG2 ε y hε, hC]
  rw [hG1', hA, hG2', hB, add_sub_cancel_right]
  ring

/-- **L4, local identification of the decoded shifted measure.** If the α₀-profile `F1` of the DMS-shifted field and
the γ-profile `F2` of the affine-plus-test field lie in the convergence locus of the test family `T`, then the
decoded α₀-measure of `F1`, recentred at `z`, agrees on `B_{5r/4}` with `exp(γ h(1,z))` times the decoded γ-measure of
`F2`. Proof: `IsLQGLimit.restrict_eq` for the translated α₀-limit and the `add_const` γ-limit. -/
theorem decoder_shifted_local_eq {a0 γ r : ℝ} {z : ℂ} {hc : ℝ → ℂ → ℝ}
    (T : ProfileDecoderDerived.TestFamily) (F1 F2 : C(CircleParameter, ℝ)) {gt : ℂ → ℝ}
    (hz : 3 * r < ‖z‖) (hzu : ‖z‖ < 1 - 3 * r) (hr : 0 < r)
    (hEq : Set.EqOn gt (fun y => -a0 * Real.log ‖y + z‖) (closedBall (0 : ℂ) (3 * r / 2)))
    (hF1 : ∀ s x, 0 < s → circleProfile F1 s x = hc s x + Real.circleAverage (dmsShift γ z) x s)
    (hF2 : ∀ s x, 0 < s → circleProfile F2 s x = hc s (x + z) - hc 1 z + Real.circleAverage gt x s)
    (h1 : F1 ∈ ProfileDecoderDerived.convSet T γ a0) (h2 : F2 ∈ ProfileDecoderDerived.convSet T γ γ) :
    ((ProfileDecoderDerived.decoder T γ a0 F1).map (fun w => w - z)).restrict (ball (0 : ℂ) (5 * r / 4)) =
      (ENNReal.ofReal (Real.exp (γ * hc 1 z)) • ProfileDecoderDerived.decoder T γ γ F2).restrict
        (ball (0 : ℂ) (5 * r / 4)) := by
  have hpos : ∀ n : ℕ, 0 < dyadicScale n := fun n => by unfold dyadicScale; positivity
  have hA := ProfileDecoderDerived.isLQGLimit_decoder T γ a0 h1
  have hB := ProfileDecoderDerived.isLQGLimit_decoder T γ γ h2
  have hT := Section6.isLQGLimit_translate hA (fun n => ProfileDecoderDerived.continuous_fca a0 F1 (hpos n)) z
  have hAdd := hB.add_const (hc 1 z)
  have hev : ∀ᶠ k : ℕ in atTop, dyadicScale k < r / 4 := by
    unfold dyadicScale
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
      (gt_mem_nhds (by linarith))
  refine hT.restrict_eq hAdd isOpen_ball ?_
  intro K _ hK
  filter_upwards [hev] with k hk
  intro y hy
  have hyU : ‖y‖ < 5 * r / 4 := mem_ball_zero_iff.mp (hK hy)
  exact fieldCircleAverage_local_identity (G1 := circleProfile F1) (G2 := circleProfile F2) hz hzu hEq
    (fun s x hs => hF1 s x hs) (fun s x hs => hF2 s x hs) (hpos k) hk hyU

end HarmonicBalls
