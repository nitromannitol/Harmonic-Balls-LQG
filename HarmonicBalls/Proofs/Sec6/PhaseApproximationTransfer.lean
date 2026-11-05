import HarmonicBalls.Proofs.Sec6.DyadicLatticePhaseProbability
import HarmonicBalls.Proofs.Sec8.PhaseCriterionTranslation

/-! # Deterministic transfer between nearby lattice phases

The geometric approximation alone does not establish stability of good annuli.
The count transfer below records the stability needed for each tested radius.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set

/-- A phase can be moved to a finite representative modulo the lattice by a
small displacement. -/
theorem exists_dyadic_phase_displacement {s : ℝ} (hs : 0 < s) :
    ∃ F : ℕ → Finset ℂ, (∀ n, (F n).card ≤ 2 ^ (3 * n)) ∧
      ∀ n p, ∃ q ∈ F n, ∃ t ∈ scaledLattice (dyadicScale n * s / 100),
        ∃ d : ℂ, dist 0 d < 2 * (dyadicScale (2 * n) * s / 100) ∧
          p + d = q + t := by
  obtain ⟨F, hcard, hcover⟩ := dyadic_lattice_phase_approximation hs
  refine ⟨F, hcard, ?_⟩
  intro n p
  obtain ⟨q, hq, t, ht, hd⟩ := hcover n p
  refine ⟨q, hq, t, ht, q + t - p, ?_, ?_⟩
  · simpa [dist_eq_norm, norm_sub_rev] using hd
  · abel

/-- Pointwise transfer of good annuli gives transfer of the number of tested
geometric radii. -/
theorem goodAnnulus_radius_count_le_of_transfer {μ : Measure ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (n : ℕ) (z w : ℂ) (a b a' b' : ℝ)
    (htransfer : ∀ r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ),
      IsGoodAnnulus μ r w a b → IsGoodAnnulus μ r z a' b') :
    ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
      (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
      IsGoodAnnulus μ r w a b}.ncard : ℝ) ≤
    ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
      (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
      IsGoodAnnulus μ r z a' b'}.ncard : ℝ) := by
  have hfin : {r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
      (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
      IsGoodAnnulus μ r z a' b'}.Finite := by
    apply finite_of_geometric (q := (7 : ℝ)⁻¹) (A := ρ)
      (lo := dyadicScale n * ρ) (by norm_num) (by norm_num)
      (mul_pos (dyadicScale_pos n) hρ)
    intro r hr
    obtain ⟨k, _, hk⟩ := hr.2.1
    exact ⟨hr.1.1, k, hk⟩
  have hsubset : {r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
      (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r w a b} ⊆
      {r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
      (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z a' b'} := by
    intro r hr
    exact ⟨hr.1, hr.2.1, htransfer r hr.1 hr.2.2⟩
  exact_mod_cast Set.ncard_le_ncard hsubset hfin

/-- A criterion at shifted centres and phases transfers to the original
centres and phases when each tested good annulus transfers pointwise. -/
theorem phaseVeryGoodCriterionThree_of_shifted_centres {μ : Measure ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (x : ℂ) (N : ℕ) (a b a' b' c : ℝ)
    (phase displacement : ℕ → ℂ)
    (hsource : ∀ n, N ≤ n → ∀ z ∈ annulus (x + displacement n) (ρ / 2) ρ,
      z - (phase n + displacement n) ∈ scaledLattice (dyadicScale n * ρ / 100) →
      c * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
          (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus μ r z a b}.ncard : ℝ))
    (htransfer : ∀ n, N ≤ n → ∀ z ∈ annulus x (ρ / 2) ρ,
      ∀ r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ),
        IsGoodAnnulus μ r (z + displacement n) a b → IsGoodAnnulus μ r z a' b') :
    PhaseVeryGoodCriterionThree μ ρ x N a' b' c phase := by
  intro n hn z hz hlat
  have hz' : z + displacement n ∈ annulus (x + displacement n) (ρ / 2) ρ := by
    simpa only [annulus, mem_sdiff, mem_ball, mem_closedBall, dist_eq_norm,
      add_sub_add_right_eq_sub] using hz
  have hl : z + displacement n - (phase n + displacement n) ∈
      scaledLattice (dyadicScale n * ρ / 100) := by
    simpa only [add_sub_add_right_eq_sub] using hlat
  exact (hsource n hn _ hz' hl).trans
    (goodAnnulus_radius_count_le_of_transfer hρ n z (z + displacement n) a b a' b'
      (htransfer n hn z hz))


/-- Finite phase representatives suffice if the source counts hold uniformly
at nearby centres and good annuli transfer under the corresponding small
centre displacement. These two uniformity conditions are explicit hypotheses. -/
theorem phaseVeryGoodCriterionThree_of_finite_phase_approximation
    {μ : Measure ℂ} {ρ : ℝ} (hρ : 0 < ρ) (x : ℂ) (N : ℕ)
    (a b a' b' c : ℝ) (phase : ℕ → ℂ) (F : ℕ → Finset ℂ)
    (hcover : ∀ n p, ∃ q ∈ F n, ∃ t ∈ scaledLattice (dyadicScale n * ρ / 100),
      ∃ d : ℂ, dist 0 d < 2 * (dyadicScale (2 * n) * ρ / 100) ∧ p + d = q + t)
    (hsource : ∀ n, N ≤ n → ∀ q ∈ F n,
      ∀ t ∈ scaledLattice (dyadicScale n * ρ / 100), ∀ d : ℂ,
      dist 0 d < 2 * (dyadicScale (2 * n) * ρ / 100) →
      ∀ z ∈ annulus (x + d) (ρ / 2) ρ,
      z - (q + t) ∈ scaledLattice (dyadicScale n * ρ / 100) →
      c * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
          (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus μ r z a b}.ncard : ℝ))
    (htransfer : ∀ n, N ≤ n → ∀ z ∈ annulus x (ρ / 2) ρ, ∀ d : ℂ,
      dist 0 d < 2 * (dyadicScale (2 * n) * ρ / 100) →
      ∀ r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ),
        IsGoodAnnulus μ r (z + d) a b → IsGoodAnnulus μ r z a' b') :
    PhaseVeryGoodCriterionThree μ ρ x N a' b' c phase := by
  classical
  choose q hq t ht d hd heq using fun n => hcover n (phase n)
  apply phaseVeryGoodCriterionThree_of_shifted_centres hρ x N a b a' b' c phase d
  · intro n hn z hz hlat
    apply hsource n hn (q n) (hq n) (t n) (ht n) (d n) (hd n) z hz
    simpa only [← heq n] using hlat
  · intro n hn z hz r hr hgood
    exact htransfer n hn z hz (d n) (hd n) r hr hgood

end HarmonicBalls.Section6
