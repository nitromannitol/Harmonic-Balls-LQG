import HarmonicBalls.Proofs.Sec8.AtomicWitnessRemoval

/-! # Concentration of exceptional bad witnesses

If strict compact-obstacle tests do not detect a bad witness, its mass is
concentrated at the Brownian starting point and saturates the mass threshold.
-/

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

open MarkovProcess in
/-- A bad witness missed by every strict compact-obstacle test has exactly
threshold mass, all of it at its starting point. -/
theorem exists_concentrated_badWitness_of_compact_tests
    (μ : Measure ℂ) (r : ℝ) (z : ℂ) (a b : ℝ)
    (hfinite : μ (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hsmall : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε)
    (hcomp : ∀ K : Set ℂ, IsCompact K → K ⊆ annulus z (3 * r) (5 * r) →
      μ (annulus z (3 * r) (5 * r) \ K) <
        ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) →
      ∀ u ∈ sphere z (4 * r), planarBrownianMotion u
        {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime (annulus z (3 * r) (5 * r) \ K) p} ≤ ENNReal.ofReal b)
    (hbad : ¬ IsGoodAnnulus μ r z a b) :
    ∃ Y : Set ℂ, MeasurableSet Y ∧ Y ⊆ annulus z (3 * r) (5 * r) ∧
      ∃ u ∈ sphere z (4 * r),
        μ Y = ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) ∧
        μ (Y \ {u}) = 0 ∧
        ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) ≤ μ {u} ∧
        ENNReal.ofReal b < planarBrownianMotion u
          {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
            ContinuousPath.exitTime Y p} := by
  have hA : IsOpen (annulus z (3 * r) (5 * r)) := isOpen_ball.sdiff isClosed_closedBall
  obtain ⟨Y, hY, hYA, hmass, u, hu, hp⟩ :=
    (not_isGoodAnnulus_iff_exists_badWitness μ r z a b).1 hbad
  have hnotaway : ¬ (μ Y = ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) →
      0 < μ (Y \ {u})) := by
    intro haway
    obtain ⟨K, hK, hKA, hKmass, hprob⟩ :=
      exists_compact_obstacle_of_badWitness_of_mass_away μ hA hY hYA hfinite
        (ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r))) (ENNReal.ofReal b)
        hmass u hp haway (hsmall u hu)
    exact (not_le_of_gt hprob) (hcomp K hK hKA hKmass u hu)
  have heq : μ Y = ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) := by
    by_contra hne
    exact hnotaway (fun h => (hne h).elim)
  have hzero : μ (Y \ {u}) = 0 := by
    apply nonpos_iff_eq_zero.mp
    exact le_of_not_gt (fun h => hnotaway (fun _ => h))
  have hlarge : ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) ≤ μ {u} := by
    by_contra hnot
    have hp' := measure_sdiff_singleton_pos_of_gt μ Y u (heq ▸ lt_of_not_ge hnot)
    exact (not_lt_of_ge (le_of_eq hzero)) hp'
  exact ⟨Y, hY, hYA, u, hu, heq, hzero, hlarge, hp⟩

end HarmonicBalls
