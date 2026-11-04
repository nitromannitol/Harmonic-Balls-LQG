import HarmonicBalls.Proofs.Sec8.PositiveMassSupport

/-! # Bad-witness removal for measures with atoms

A witness can be made strict whenever it carries positive mass away from its
Brownian starting point. The remaining case has all witness mass at that
starting point.
-/

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

/-- Positive mass away from a point supplies a support point away from it,
without requiring the measure to be atomless. -/
theorem exists_positive_mass_support_ne_of_sdiff_singleton
    (μ : Measure ℂ) {Y : Set ℂ} (hY : MeasurableSet Y) (u : ℂ)
    (hpos : 0 < μ (Y \ {u})) :
    ∃ x : ℂ, x ∈ Y ∧ x ≠ u ∧ ∀ ρ : ℝ, 0 < ρ → 0 < μ (Y ∩ ball x ρ) := by
  let ν : Measure ℂ := μ.restrict (Y \ {u})
  have : (ae ν).NeBot := ae_restrict_neBot.mpr hpos.ne'
  have hae : ∀ᵐ x ∂ν, x ∈ ν.support ∧ x ∈ Y \ {u} := by
    filter_upwards [Measure.support_mem_ae (μ := ν),
      ae_restrict_mem (hY.diff (measurableSet_singleton u))] with x hx hxy
    exact ⟨hx, hxy⟩
  obtain ⟨x, hx, hxy, hxu⟩ := hae.exists
  refine ⟨x, hxy, ?_, ?_⟩
  · simpa using hxu
  · intro ρ hρ
    have hp := (Measure.mem_support_iff_forall x).mp hx (ball x ρ) (ball_mem_nhds x hρ)
    change 0 < (μ.restrict (Y \ {u})) (ball x ρ) at hp
    rw [Measure.restrict_apply isOpen_ball.measurableSet] at hp
    exact lt_of_lt_of_le hp (measure_mono (by intro t ht; exact ⟨ht.2.1, ht.1⟩))

open MarkovProcess in
/-- A finite-mass bad witness has a strict compact-obstacle replacement
when it carries positive mass away from the Brownian starting point and small
balls away from that point are rarely hit. -/
theorem exists_compact_obstacle_of_badWitness_of_mass_away
    (μ : Measure ℂ) {U Y : Set ℂ} (hU : IsOpen U)
    (hY : MeasurableSet Y) (hYU : Y ⊆ U) (hfinite : μ U ≠ ∞)
    (a b : ℝ≥0∞) (hmass : μ Y ≤ a) (u : ℂ)
    (hp : b < planarBrownianMotion u
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Y p})
    (haway : μ Y = a → 0 < μ (Y \ {u}))
    (hsmall : ∀ x : ℂ, x ∈ U → x ≠ u → ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ U ∧ μ (U \ K) < a ∧
      b < planarBrownianMotion u
        {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (U \ K) p} := by
  apply exists_compact_obstacle_of_badWitness_of_rare_removal μ hU hY hYU hfinite a b hmass u hp
  intro heq
  obtain ⟨x, hxY, hxu, hsupp⟩ :=
    exists_positive_mass_support_ne_of_sdiff_singleton μ hY u (haway heq)
  have hYfinite : μ Y ≠ ∞ := ne_top_of_le_ne_top hfinite (measure_mono hYU)
  exact exists_rare_positive_compact_of_support_point μ hY hYfinite u x hsupp (hsmall x (hYU hxY) hxu)

/-- A set whose measure is greater than the mass of a point has positive
mass away from that point. -/
theorem measure_sdiff_singleton_pos_of_gt (μ : Measure ℂ) (Y : Set ℂ) (u : ℂ)
    (h : μ {u} < μ Y) : 0 < μ (Y \ {u}) := by
  by_contra hn
  have hz : μ (Y \ {u}) = 0 := nonpos_iff_eq_zero.mp (le_of_not_gt hn)
  have hsub : Y ⊆ (Y \ {u}) ∪ {u} := by
    intro x hx
    by_cases hxu : x = u
    · exact Or.inr (by simpa using hxu)
    · exact Or.inl ⟨hx, by simpa using hxu⟩
  have hbound : μ Y ≤ μ (Y \ {u}) + μ {u} :=
    (measure_mono hsub).trans (measure_union_le _ _)
  rw [hz, zero_add] at hbound
  exact (not_le_of_gt h) hbound

open MarkovProcess in
/-- If every atom on the starting sphere has mass below the threshold,
compact-obstacle tests characterize good annuli for arbitrary finite measures. -/
theorem isGoodAnnulus_iff_compact_obstacles_of_small_starting_atoms
    (μ : Measure ℂ) (r : ℝ) (z : ℂ) (a b : ℝ)
    (hfinite : μ (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hatoms : ∀ u ∈ sphere z (4 * r), μ {u} <
      ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)))
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
      exists_compact_obstacle_of_badWitness_of_mass_away μ hA hY hYA hfinite
        (ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r))) (ENNReal.ofReal b)
        hmass u hp (fun heq => measure_sdiff_singleton_pos_of_gt μ Y u (heq ▸ hatoms u hu))
        (hsmall u hu)
    exact (not_le_of_gt hprob) (hcomp K hK hKA hKmass u hu)

end HarmonicBalls
