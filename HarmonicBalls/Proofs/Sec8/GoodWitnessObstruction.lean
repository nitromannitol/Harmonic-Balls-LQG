import HarmonicBalls.Proofs.Sec8.GoodEventWitnesses
import HarmonicBalls.Proofs.Sec6.BrownianAvoidance

/-! # An obstruction to universal countable bad-witness families

At zero mass threshold, countable families cannot capture all bad measures
if the Brownian survival condition persists after deleting countably many
points. The latter point-avoidance property is an explicit assumption here.
-/

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

open MarkovProcess in
/-- The empty set cannot witness failure when the annulus has positive radius. -/
theorem empty_not_goodAnnulusBadWitness {r : ℝ} (hr : 0 < r)
    (z : ℂ) (b : ℝ) (μ : Measure ℂ) :
    μ ∉ goodAnnulusBadWitness r z 0 b ∅ := by
  intro h
  obtain ⟨u, hu, hp⟩ := h.2.2.2
  have huA : u ∈ annulus z (3 * r) (5 * r) := by
    have hd : dist u z = 4 * r := mem_sphere.mp hu
    change dist u z < 5 * r ∧ ¬ dist u z ≤ 3 * r
    rw [hd]
    constructor <;> linarith
  have hzero : planarBrownianMotion u
      {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
        ContinuousPath.exitTime (∅ : Set ℂ) p} = 0 := by
    apply measure_mono_null _ (ae_iff.mp (Section6.ae_planarBrownianMotion_exitTime_pos
      (isOpen_ball.sdiff isClosed_closedBall) huA))
    intro p hp hpos
    have hempty : ContinuousPath.exitTime (∅ : Set ℂ) p = 0 := by
      apply le_antisymm
      · simpa using ContinuousPath.exitTime_le_of_notMem (∅ : Set ℂ) p 0 (by simp)
      · exact zero_le
    change ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
      ContinuousPath.exitTime (∅ : Set ℂ) p at hp
    rw [hempty] at hp
    exact (not_le_of_gt hpos) hp
  rw [hzero] at hp
  exact (not_lt_of_ge zero_le) hp

open MarkovProcess in
/-- Under countable point avoidance, no countable collection of Borel sets
captures all bad measures at zero mass threshold. -/
theorem not_countable_badWitness_family_of_countable_avoidance
    (r : ℝ) (hr : 0 < r) (z : ℂ) (b : ℝ)
    (havoid : ∀ S : Set ℂ, S.Countable →
      ∃ u ∈ sphere z (4 * r), ENNReal.ofReal b <
        planarBrownianMotion u
          {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
            ContinuousPath.exitTime (annulus z (3 * r) (5 * r) \ S) p})
    (Y : ℕ → Set ℂ) :
    ¬ (∀ μ : Measure ℂ, ¬ IsGoodAnnulus μ r z 0 b →
      ∃ n, μ ∈ goodAnnulusBadWitness r z 0 b (Y n)) := by
  classical
  let x : ℕ → ℂ := fun n => if h : (Y n).Nonempty then Classical.choose h else 0
  let μ : Measure ℂ := Measure.sum (fun n => Measure.dirac (x n))
  let S : Set ℂ := Set.range x
  have hS : S.Countable := Set.countable_range x
  have hA : MeasurableSet (annulus z (3 * r) (5 * r)) :=
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hzero : μ (annulus z (3 * r) (5 * r) \ S) = 0 := by
    rw [show μ = Measure.sum (fun n => Measure.dirac (x n)) from rfl]
    rw [Measure.sum_apply _ (hA.diff hS.measurableSet)]
    apply ENNReal.tsum_eq_zero.mpr
    intro n
    rw [Measure.dirac_apply' _ (hA.diff hS.measurableSet)]
    simp [S]
  have hbad : ¬ IsGoodAnnulus μ r z 0 b := by
    apply (not_isGoodAnnulus_iff_exists_badWitness μ r z 0 b).2
    refine ⟨annulus z (3 * r) (5 * r) \ S, ?_⟩
    refine ⟨hA.diff hS.measurableSet,
      sdiff_subset, ?_, havoid S hS⟩
    simp only [hzero, ENNReal.ofReal_zero, zero_mul, le_refl]
  intro hfamily
  obtain ⟨n, hn⟩ := hfamily μ hbad
  have hne : (Y n).Nonempty := by
    by_contra he
    have hempty : Y n = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    rw [hempty] at hn
    exact empty_not_goodAnnulusBadWitness hr z b μ hn
  have hxn : x n ∈ Y n := by
    simp only [x, dite_eq_left hne]
    exact Classical.choose_spec hne
  have hpos : 0 < μ (Y n) := by
    have hle : Measure.dirac (x n) (Y n) ≤ μ (Y n) := by
      exact (Measure.le_sum (fun n => Measure.dirac (x n)) n) (Y n)
    have : Measure.dirac (x n) (Y n) = 1 := by
      rw [Measure.dirac_apply' _ hn.1]
      simp [hxn]
    rw [this] at hle
    exact lt_of_lt_of_le zero_lt_one hle
  have hm := hn.2.2.1
  simp only [ENNReal.ofReal_zero, zero_mul, le_zero_iff] at hm
  exact (ne_of_gt hpos) hm

end HarmonicBalls
