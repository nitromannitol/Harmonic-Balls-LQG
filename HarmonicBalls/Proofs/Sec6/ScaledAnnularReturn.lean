import HarmonicBalls.Proofs.Sec6.SpacetimeCollarReturn
import HarmonicBalls.Proofs.Sec6.UniformCollarReturn
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-! # Scale-invariant Brownian annular return estimates -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set MarkovProcess Filter
open scoped ENNReal NNReal Pointwise Topology

/-- Positive dilations map annuli to annuli. -/
theorem image_smul_annulus {k : ℝ} (hk : 0 < k) (z : ℂ) (r R : ℝ) :
    (fun x : ℂ => k • x) '' annulus z r R = annulus (k • z) (k*r) (k*R) := by
  have hinj : Function.Injective (fun x : ℂ => k • x) :=
    (Homeomorph.smulOfNeZero k hk.ne').injective
  rw [annulus, image_sdiff hinj]
  change k • ball z R \ k • closedBall z r = _
  rw [_root_.smul_ball hk.ne', _root_.smul_closedBall' hk.ne', Real.norm_eq_abs, abs_of_pos hk]
  rfl

/-- Positive dilations map closed annular cores to closed annular cores. -/
theorem image_smul_closed_annular_core {k : ℝ} (hk : 0 < k) (z : ℂ) (s S : ℝ) :
    (fun x : ℂ => k • x) '' {x | s ≤ dist x z ∧ dist x z ≤ S} =
      {x | k*s ≤ dist x (k • z) ∧ dist x (k • z) ≤ k*S} := by
  have heq (z : ℂ) (s S : ℝ) : {x | s ≤ dist x z ∧ dist x z ≤ S} =
      closedBall z S \ ball z s := by
    ext x
    simp only [mem_ofPred_eq, Set.mem_sdiff, mem_closedBall, mem_ball, not_lt]
    tauto
  have hinj : Function.Injective (fun x : ℂ => k • x) :=
    (Homeomorph.smulOfNeZero k hk.ne').injective
  rw [heq, heq, image_sdiff hinj]
  change k • closedBall z S \ k • ball z s = _
  rw [_root_.smul_closedBall' hk.ne', _root_.smul_ball hk.ne', Real.norm_eq_abs, abs_of_pos hk]

/-- Radial core-return probabilities at positive scale `k` equal those of
the corresponding unit-scale geometry. -/
theorem planarBrownian_radial_core_return_dilation
    {k : ℝ} (hk : 0 < k) (x z : ℂ) (r R b B s S : ℝ) :
    planarBrownianMotion (k • x) {ω | ∃ t : ℝ≥0,
      ContinuousPath.exitTime (annulus (k • z) (k*b) (k*B)) ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (annulus (k • z) (k*r) (k*R)) ω ∧
      k*s ≤ dist (ω t) (k • z) ∧ dist (ω t) (k • z) ≤ k*S} =
    planarBrownianMotion x {ω | ∃ t : ℝ≥0,
      ContinuousPath.exitTime (annulus z b B) ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (annulus z r R) ω ∧
      s ≤ dist (ω t) z ∧ dist (ω t) z ≤ S} := by
  simpa only [image_smul_annulus hk, image_smul_closed_annular_core hk, mem_ofPred_eq] using
    planarBrownian_core_return_dilation hk x (annulus z r R) (annulus z b B)
      {y | s ≤ dist y z ∧ dist y z ≤ S}

/-- A single relative collar width controls Brownian return probabilities on
all positive scales. The width depends only on the prescribed error; the
starting point ranges over the scaled middle circle. -/
theorem exists_scale_uniform_radial_core_return
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ k : ℝ, 0 < k → ∀ x ∈ sphere (0 : ℂ) 4,
      planarBrownianMotion (k • x) {ω | ∃ t : ℝ≥0,
        ContinuousPath.exitTime (annulus 0 (k * (3 + η)) (k * (5 - η))) ω ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < ContinuousPath.exitTime (annulus 0 (k * (3 - η)) (k * (5 + η))) ω ∧
        k * (7 / 2) ≤ dist (ω t) 0 ∧ dist (ω t) 0 ≤ k * (9 / 2)} < ε := by
  let d : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hdpos (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have hdanti : Antitone d := by
    intro n m hnm
    dsimp [d]
    apply one_div_le_one_div_of_le (by positivity)
    simpa only [add_comm] using add_le_add_right (Nat.cast_le.mpr hnm : (n : ℝ) ≤ m) 1
  have hd : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hu := eventually_uniform_circle_radial_core_return (z := (0 : ℂ))
    (r := 3) (R := 5) (s := 7 / 2) (S := 9 / 2) (ρ := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hdpos hdanti hd hε
  obtain ⟨n, hn⟩ := hu.exists
  refine ⟨d n, hdpos n, ?_⟩
  intro k hk x hx
  have h := planarBrownian_radial_core_return_dilation hk x 0
    (3 - d n) (5 + d n) (3 + d n) (5 - d n) (7 / 2) (9 / 2)
  simpa only [smul_zero] using h.trans_lt (hn x hx)

/-- The same relative width works at every centre and every positive scale. -/
theorem exists_scale_and_centre_uniform_radial_core_return
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ k : ℝ, 0 < k → ∀ z : ℂ, ∀ x ∈ sphere (0 : ℂ) 4,
      planarBrownianMotion (k • x + z) {ω | ∃ t : ℝ≥0,
        ContinuousPath.exitTime (annulus z (k * (3 + η)) (k * (5 - η))) ω ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < ContinuousPath.exitTime (annulus z (k * (3 - η)) (k * (5 + η))) ω ∧
        k * (7 / 2) ≤ dist (ω t) z ∧ dist (ω t) z ≤ k * (9 / 2)} < ε := by
  obtain ⟨η, hη, hbound⟩ := exists_scale_uniform_radial_core_return hε
  refine ⟨η, hη, ?_⟩
  intro k hk z x hx
  have hAnn (a b : ℝ) : (fun y : ℂ => y + z) '' annulus 0 a b = annulus z a b := by
    ext y
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [annulus, dist_eq_norm] using hy
    · intro hy
      refine ⟨y - z, ?_, sub_add_cancel y z⟩
      simpa [annulus, dist_eq_norm] using hy
  have hCore (a b : ℝ) : (fun y : ℂ => y + z) ''
      {y | a ≤ dist y 0 ∧ dist y 0 ≤ b} =
      {y | a ≤ dist y z ∧ dist y z ≤ b} := by
    ext y
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [dist_eq_norm] using hy
    · intro hy
      refine ⟨y - z, ?_, sub_add_cancel y z⟩
      simpa [dist_eq_norm] using hy
  have h := planarBrownian_core_return_add (k • x) z
    (annulus 0 (k * (3 - η)) (k * (5 + η)))
    (annulus 0 (k * (3 + η)) (k * (5 - η)))
    {y | k * (7 / 2) ≤ dist y 0 ∧ dist y 0 ≤ k * (9 / 2)}
  rw [hAnn, hAnn, hCore] at h
  simpa only [mem_ofPred_eq] using h.trans_lt (hbound k hk x hx)

end HarmonicBalls.Section6
