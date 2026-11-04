import HarmonicBalls.Proofs.Sec8.ObstacleApproximation

/-! # Small-ball hitting and polar points

For a continuous path law with finite exit from a bounded domain, avoidance
of an interior point implies arbitrarily small hitting probabilities for
balls around that point. No point-polarity theorem is assumed here.
-/

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- Closed balls of reciprocal integer radii decrease to their center. -/
theorem iInter_reciprocal_closedBall (x : ℂ) :
    ⋂ n : ℕ, closedBall x (1 / ((n : ℝ) + 1)) = {x} := by
  ext y
  constructor
  · intro hy
    have hd : dist y x = 0 := by
      by_contra hne
      have hpos : 0 < dist y x := lt_of_le_of_ne dist_nonneg (Ne.symm hne)
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      have hle : dist y x ≤ 1 / ((n : ℝ) + 1) := by
        have := mem_iInter.mp hy n
        simpa only [mem_closedBall] using this
      linarith
    exact mem_singleton_iff.mpr (dist_eq_zero.mp hd)
  · intro hy
    have hyx : y = x := mem_singleton_iff.mp hy
    subst y
    apply mem_iInter.mpr
    intro n
    simp only [mem_closedBall, dist_self]
    positivity

open MarkovProcess in
/-- If a finite path law almost surely exits an open domain, starts inside it,
and avoids an interior point before exit, then it hits sufficiently small
closed balls about the point with arbitrarily small probability. -/
theorem exists_small_closedBall_hitting_of_ae_point_avoidance
    (Q : Measure (ContinuousPath ℂ)) [IsFiniteMeasure Q]
    {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U)
    (hstart : ∀ᵐ p ∂Q, p 0 ∈ U)
    (hfin : ∀ᵐ p ∂Q, ContinuousPath.exitTime U p ≠ ∞)
    (hpoint : ∀ᵐ p ∂Q, ContinuousPath.exitTime U p ≤
      ContinuousPath.exitTime ({x} : Set ℂ)ᶜ p)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ Q {p | ¬ ContinuousPath.exitTime U p ≤
      ContinuousPath.exitTime (closedBall x ρ)ᶜ p} < ε := by
  let K : ℕ → Set ℂ := fun n => closedBall x (1 / ((n : ℝ) + 1))
  have hclosed : ∀ n, IsClosed (K n) := fun _ => isClosed_closedBall
  have hanti : Antitone K := by
    intro m n hmn
    apply closedBall_subset_closedBall
    have hden : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast (Nat.add_le_add_right hmn 1)
    gcongr
  have hinter : ⋂ n, K n = {x} := iInter_reciprocal_closedBall x
  have hopen : ∀ n, IsOpen (K n)ᶜ := fun n => (hclosed n).isOpen_compl
  have hmono : Monotone fun n => (K n)ᶜ := fun _ _ h => compl_subset_compl.mpr (hanti h)
  have hunion : ⋃ n, (K n)ᶜ = ({x} : Set ℂ)ᶜ := by rw [← compl_iInter, hinter]
  let E : ℕ → Set (ContinuousPath ℂ) := fun n =>
    {p | ¬ ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (K n)ᶜ p}
  have hEanti : Antitone E := by
    intro m n hmn p hp
    change ¬ ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (K n)ᶜ p at hp
    change ¬ ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (K m)ᶜ p
    intro hm
    exact hp (hm.trans (ContinuousPath.exitTime_mono (hmono hmn) p))
  have hEmeas : ∀ n, MeasurableSet (E n) := fun n =>
    (measurableSet_le (ContinuousPath.measurable_exitTime U hU)
      (ContinuousPath.measurable_exitTime (K n)ᶜ (hopen n))).compl
  have hae : ∀ᵐ p ∂Q, p ∉ ⋂ n, E n := by
    filter_upwards [hstart, hfin, hpoint] with p hp hf ha
    intro hpall
    have hlt := exitTime_lt_obstacle_of_le hU isClosed_singleton
      (singleton_subset_iff.mpr hx) p hp hf ha
    rw [← hunion, exitTime_iUnion_eq_iSup hopen hmono, lt_iSup_iff] at hlt
    obtain ⟨n, hn⟩ := hlt
    exact (mem_iInter.mp hpall n) hn.le
  have hnull : Q (⋂ n, E n) = 0 := by
    simpa only [not_not, ofPred_mem_eq] using (ae_iff.mp hae)
  have hinf : (⨅ n, Q (E n)) = 0 := by
    rw [← hEanti.measure_iInter (fun n => (hEmeas n).nullMeasurableSet)
      ⟨0, measure_ne_top Q (E 0)⟩, hnull]
  have hl : (⨅ n, Q (E n)) < ε := by rw [hinf]; exact hε
  obtain ⟨n, hn⟩ := iInf_lt_iff.mp hl
  exact ⟨1 / ((n : ℝ) + 1), by positivity, hn⟩

open MarkovProcess in
/-- For planar Brownian motion in a bounded open domain, almost-sure
avoidance of an interior point implies the corresponding small-ball estimate. -/
theorem exists_small_ball_hitting_of_ae_point_avoidance
    {U : Set ℂ} (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    {u x : ℂ} (hu : u ∈ U) (hx : x ∈ U)
    (hpoint : ∀ᵐ p ∂(planarBrownianMotion u), ContinuousPath.exitTime U p ≤
      ContinuousPath.exitTime ({x} : Set ℂ)ᶜ p)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ planarBrownianMotion u
      {p | ¬ ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε := by
  obtain ⟨R, hR⟩ := hbounded.subset_ball u
  have hstart : ∀ᵐ p ∂(planarBrownianMotion u), p 0 ∈ U := by
    filter_upwards [ae_planarBrownianMotion_eval_zero u] with p hp
    simpa [hp] using hu
  have hfin : ∀ᵐ p ∂(planarBrownianMotion u), ContinuousPath.exitTime U p ≠ ∞ := by
    filter_upwards [Section6.ae_planarBrownianMotion_exitTime_ball_lt_top u R] with p hp
    exact ne_top_of_lt ((ContinuousPath.exitTime_mono hR p).trans_lt hp)
  obtain ⟨ρ, hρ, hsmall⟩ := exists_small_closedBall_hitting_of_ae_point_avoidance
    (planarBrownianMotion u) hU hx hstart hfin hpoint ε hε
  refine ⟨ρ, hρ, (measure_mono ?_).trans_lt hsmall⟩
  intro p hp
  change ¬ ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (ball x ρ)ᶜ p at hp
  change ¬ ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (closedBall x ρ)ᶜ p
  intro hle
  exact hp (hle.trans (ContinuousPath.exitTime_mono
    (compl_subset_compl.mpr ball_subset_closedBall) p))

open MarkovProcess in
/-- Global avoidance of a point implies avoidance before the exit from any
domain. This is the bridge from the usual definition of a polar point. -/
theorem ae_avoid_before_exit_of_ae_ne (Q : Measure (ContinuousPath ℂ))
    (U : Set ℂ) (x : ℂ) (havoid : ∀ᵐ p ∂Q, ∀ t : ℝ≥0, p t ≠ x) :
    ∀ᵐ p ∂Q, ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime ({x} : Set ℂ)ᶜ p := by
  filter_upwards [havoid] with p hp
  have ht : ContinuousPath.exitTime ({x} : Set ℂ)ᶜ p = ∞ := by
    apply (ContinuousPath.exitTime_eq_top_iff _ _).2
    intro t
    simpa using hp t
  rw [ht]
  exact le_top

open MarkovProcess in
/-- The usual global point-avoidance property supplies the interior
small-ball estimate used in the good-annulus construction. -/
theorem annulus_smallBallHitting_of_ae_point_avoidance
    (r : ℝ) (hr : 0 < r) (z : ℂ)
    (hpolar : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε := by
  intro u hu x hx hxu ε hε
  have huU : u ∈ annulus z (3 * r) (5 * r) := by
    simp only [mem_sphere] at hu
    simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le]
    constructor <;> linarith
  apply exists_small_ball_hitting_of_ae_point_avoidance
    (isOpen_ball.sdiff isClosed_closedBall) (isBounded_ball.subset sdiff_subset)
    huU hx _ ε hε
  exact ae_avoid_before_exit_of_ae_ne _ _ _ (hpolar u hu x hx hxu)

end HarmonicBalls
