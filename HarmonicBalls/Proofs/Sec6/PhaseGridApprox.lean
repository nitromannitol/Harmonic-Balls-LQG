import HarmonicBalls.Proofs.Sec6.CriterionThreeLatticeApprox

/-! # Phase-independent lattice approximation

Translation of an absolute lattice produces a lattice with a phase. These
lemmas handle arbitrary phase without identifying it with the original grid.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set

/-- Every point is within twice the mesh of a point of a lattice with an
arbitrary prescribed phase. -/
theorem exists_phase_scaledLattice_dist_lt (x phase : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ y : ℂ, y - phase ∈ scaledLattice δ ∧ dist x y < 2 * δ := by
  obtain ⟨w, hw, hd⟩ := exists_scaledLattice_dist_lt (x - phase) hδ
  refine ⟨phase + w, ?_, ?_⟩
  · simpa using hw
  · have heq : x - (phase + w) = (x - phase) - w := by abel
    simpa only [dist_eq_norm, heq] using hd

/-- A shifted annular lattice is sent into the origin-centered prevalence grid
by subtracting a nearby point of the same shifted lattice. -/
theorem phase_annulus_lattice_subset_prevalenceGrid {n : ℕ} (hn : 9 ≤ n)
    {x y phase : ℂ} (hy : y - phase ∈ scaledLattice (dyadicScale n / 100))
    (hxy : dist x y < 2 * (dyadicScale n / 100)) :
    ∀ z ∈ annulus x (1 / 2) 1,
      z - phase ∈ scaledLattice (dyadicScale n / 100) →
      z - y ∈ prevalenceGrid (dyadicScale n) := by
  intro z hz hlat
  have heq (w v : ℂ) : (w - phase) - (v - phase) = w - v := by abel
  have hxy' : dist (x - phase) (y - phase) < 2 * (dyadicScale n / 100) := by
    simpa only [dist_eq_norm, heq] using hxy
  have hz' : z - phase ∈ scaledLattice (dyadicScale n / 100) ∩
      annulus (x - phase) (1 / 2) 1 := by
    refine ⟨hlat, ?_⟩
    simpa only [annulus, mem_sdiff, Metric.mem_ball, Metric.mem_closedBall,
      dist_eq_norm, heq] using hz
  have h := shifted_annulus_lattice_subset_prevalenceGrid hn hy hxy' (z - phase) hz'
  rwa [heq] at h

/-- The translated subrange count implies the criterion-three count at every
point of an annular lattice with an arbitrary phase. -/
theorem phase_criterionThree_count_of_translated_subrange_prevalence
    {μ : Measure ℂ} {c a b : ℝ} (hc : 0 < c) {n : ℕ} (hn : 9 ≤ n)
    {x y phase : ℂ} (hy : y - phase ∈ scaledLattice (dyadicScale n / 100))
    (hxy : dist x y < 2 * (dyadicScale n / 100))
    (h : ∀ z ∈ prevalenceGrid (dyadicScale n),
      c * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
            IsGoodAnnulus (μ.map (fun w : ℂ => w + -y)) r z a b}.ncard : ℝ)) :
    ∀ z ∈ annulus x (1 / 2) 1,
      z - phase ∈ scaledLattice (dyadicScale n / 100) →
      c * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n * 1) (Real.sqrt (dyadicScale n) * 1) ∧
          (∃ k : ℕ, 1 ≤ k ∧ r = 1 * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z a b}.ncard : ℝ) := by
  intro z hz hlat
  have hε0 : 0 < dyadicScale n := by unfold dyadicScale; positivity
  have hsqrt := sqrt_dyadicScale_le_one_twentieth hn
  have hε1 : dyadicScale n ≤ 1 := by
    unfold dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hz' : z - y ∈ prevalenceGrid (dyadicScale n) :=
    phase_annulus_lattice_subset_prevalenceGrid hn hy hxy z hz hlat
  have hgood (r : ℝ) : IsGoodAnnulus (μ.map (fun w : ℂ => w + -y)) r (z - y) a b ↔
      IsGoodAnnulus μ r z a b := by
    simpa only [sub_eq_add_neg] using isGoodAnnulus_map_add_iff (-y) μ r z a b
  refine ((logb_neg_half_le (by norm_num) hc hε0 hε1).trans (h (z - y) hz')).trans ?_
  norm_cast
  refine Set.ncard_le_ncard (fun r hr => ?_) ?_
  · have hr_sqrt : r ≤ Real.sqrt (dyadicScale n) := by
      refine hr.1.2.trans ?_
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by norm_num)
    obtain ⟨k, hk⟩ := hr.2.1
    have hk1 : 1 ≤ k := by
      by_contra hk1
      have : k = 0 := by omega
      subst k
      simp only [pow_zero] at hk
      linarith
    exact ⟨by simpa using ⟨hr.1.1, hr_sqrt⟩, ⟨k, hk1, by simpa using hk⟩,
      (hgood r).mp hr.2.2⟩
  · refine finite_of_geometric (q := (7 : ℝ)⁻¹) (A := 1) (lo := dyadicScale n)
      (by norm_num) (by norm_num) hε0 fun r hr => ⟨by simpa using hr.1.1, ?_⟩
    obtain ⟨k, _, hk⟩ := hr.2.1
    exact ⟨k, hk⟩

end HarmonicBalls.Section6
