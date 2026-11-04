import HarmonicBalls.Proofs.Sec8.GoodWitnessRemoval

/-! # Support points of positive-mass witnesses

A positive-mass Borel set under an atomless measure has a support point
of its restricted measure distinct from any prescribed point.
-/

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

/-- A positive-mass Borel set for an atomless measure has a support point
away from any prescribed point. Every open ball about it meets the set in
positive measure. -/
theorem exists_positive_mass_support_ne (μ : Measure ℂ) [NullSingletonClass μ]
    {Y : Set ℂ} (hY : MeasurableSet Y) (hpos : 0 < μ Y) (u : ℂ) :
    ∃ x : ℂ, x ∈ Y ∧ x ≠ u ∧ ∀ ρ : ℝ, 0 < ρ → 0 < μ (Y ∩ ball x ρ) := by
  let ν : Measure ℂ := μ.restrict Y
  have : (ae ν).NeBot := ae_restrict_neBot.mpr hpos.ne'
  have hae : ∀ᵐ x ∂ν, x ∈ ν.support ∧ x ∈ Y ∧ x ≠ u := by
    filter_upwards [Measure.support_mem_ae (μ := ν), ae_restrict_mem hY, Measure.ae_ne ν u] with x hx hxy hxu
    exact ⟨hx, hxy, hxu⟩
  obtain ⟨x, hx, hxy, hxu⟩ := hae.exists
  refine ⟨x, hxy, hxu, ?_⟩
  intro ρ hρ
  have hp := (Measure.mem_support_iff_forall x).mp hx (ball x ρ)
    (ball_mem_nhds x hρ)
  change 0 < (μ.restrict Y) (ball x ρ) at hp
  rw [Measure.restrict_apply isOpen_ball.measurableSet] at hp
  simpa only [inter_comm] using hp

open MarkovProcess in
/-- For an atomless measure and positive threshold, arbitrarily small
Brownian hitting probabilities of balls away from the starting point turn
any non-strict bad witness into a strict single-obstacle witness. -/
theorem exists_compact_obstacle_of_badWitness_of_small_ball_hitting
    (μ : Measure ℂ) [NullSingletonClass μ] {U Y : Set ℂ} (hU : IsOpen U)
    (hY : MeasurableSet Y) (hYU : Y ⊆ U) (hfinite : μ U ≠ ∞)
    (a b : ℝ≥0∞) (ha : 0 < a) (hmass : μ Y ≤ a) (u : ℂ)
    (hp : b < planarBrownianMotion u
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Y p})
    (hsmall : ∀ x : ℂ, x ∈ U → x ≠ u → ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ U ∧ μ (U \ K) < a ∧
      b < planarBrownianMotion u
        {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (U \ K) p} := by
  apply exists_compact_obstacle_of_badWitness_of_rare_removal μ hU hY hYU hfinite a b hmass u hp
  intro heq
  have hpos : 0 < μ Y := heq ▸ ha
  obtain ⟨x, hxY, hxu, hsupp⟩ := exists_positive_mass_support_ne μ hY hpos u
  have hYfinite : μ Y ≠ ∞ := ne_top_of_le_ne_top hfinite (measure_mono hYU)
  exact exists_rare_positive_compact_of_support_point μ hY hYfinite u x hsupp (hsmall x (hYU hxY) hxu)

open MarkovProcess in
/-- For a finite-mass atomless annulus and positive mass threshold, the good
condition is equivalent to testing single compact obstacles with strict mass
bound, provided small balls away from each starting point are rarely hit. -/
theorem isGoodAnnulus_iff_compact_obstacles_of_small_ball_hitting
    (μ : Measure ℂ) [NullSingletonClass μ] (r : ℝ) (z : ℂ) (a b : ℝ)
    (hfinite : μ (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hthreshold : 0 < ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)))
    (hsmall : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε) :
    IsGoodAnnulus μ r z a b ↔
      ∀ K : Set ℂ, IsCompact K → K ⊆ annulus z (3 * r) (5 * r) →
        μ (annulus z (3 * r) (5 * r) \ K) <
          ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) →
        ∀ u ∈ sphere z (4 * r), planarBrownianMotion u
          {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
            ContinuousPath.exitTime (annulus z (3 * r) (5 * r) \ K) p} ≤ ENNReal.ofReal b := by
  have hA : IsOpen (annulus z (3 * r) (5 * r)) := isOpen_ball.sdiff isClosed_closedBall
  constructor
  · intro hgood K hK hKA hmass u hu
    exact hgood _ (hA.measurableSet.diff hK.measurableSet) sdiff_subset hmass.le u hu
  · intro hcomp
    by_contra hbad
    obtain ⟨Y, hY, hYA, hmass, u, hu, hp⟩ :=
      (not_isGoodAnnulus_iff_exists_badWitness μ r z a b).1 hbad
    obtain ⟨K, hK, hKA, hKmass, hprob⟩ :=
      exists_compact_obstacle_of_badWitness_of_small_ball_hitting μ hA hY hYA hfinite
        (ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r))) (ENNReal.ofReal b)
        hthreshold hmass u hp (hsmall u hu)
    exact (not_le_of_gt hprob) (hcomp K hK hKA hKmass u hu)

end HarmonicBalls
