import HarmonicBalls.Proofs.Sec8.AtomicWitnessConcentration
import HarmonicBalls.Proofs.Sec6.BrownianAvoidance

/-! # Exceptional starting atoms

For a positive threshold and finite annulus mass, only finitely many starting
points have atoms large enough to obstruct strict witness removal.
-/

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

/-- A finite-mass set contains only finitely many atoms whose mass exceeds a
fixed positive threshold. -/
theorem finite_atoms_above_of_measure_ne_top
    (μ : Measure ℂ) (A : Set ℂ) (hfinite : μ A ≠ ∞)
    (c : ℝ≥0∞) (hc : 0 < c) :
    {x : ℂ | x ∈ A ∧ c ≤ μ {x}}.Finite := by
  by_contra h
  have hinf : {x : ℂ | x ∈ A ∧ c ≤ μ {x}}.Infinite := h
  have htop := hinf.meas_eq_top (μ := μ) ⟨c, hc.ne', fun x hx => hx.2⟩
  have hle : μ {x : ℂ | x ∈ A ∧ c ≤ μ {x}} ≤ μ A := measure_mono (fun _ hx => hx.1)
  exact hfinite (top_unique (htop ▸ hle))

open MarkovProcess in
/-- A Brownian bad witness with positive survival probability contains its
starting point when the domain is open and the starting point is interior. -/
theorem startingPoint_mem_of_positive_survival
    {U Y : Set ℂ} (hU : IsOpen U) {u : ℂ} (hu : u ∈ U)
    (hp : 0 < planarBrownianMotion u
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Y p}) : u ∈ Y := by
  by_contra hn
  have hzero : planarBrownianMotion u
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Y p} = 0 := by
    apply measure_mono_null _ (ae_iff.mp (show ∀ᵐ p ∂planarBrownianMotion u,
        p 0 = u ∧ 0 < ContinuousPath.exitTime U p from by
      filter_upwards [ae_planarBrownianMotion_eval_zero u,
        Section6.ae_planarBrownianMotion_exitTime_pos hU hu] with p h0 hpos
      exact ⟨h0, hpos⟩))
    intro p hp' hgood
    have hy : p 0 ∉ Y := by simpa [hgood.1] using hn
    have hyzero : ContinuousPath.exitTime Y p = 0 := by
      apply le_antisymm
      · simpa using ContinuousPath.exitTime_le_of_notMem Y p 0 hy
      · exact zero_le
    exact (not_le_of_gt hgood.2) (hyzero ▸ hp')
  exact (not_lt_of_ge (le_of_eq hzero)) hp

open MarkovProcess in
/-- A bad witness missed by strict compact tests starts at an atom of exactly
the threshold mass. -/
theorem exists_threshold_atom_badWitness_of_compact_tests
    (μ : Measure ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) (a b : ℝ)
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
      ∃ u ∈ sphere z (4 * r), u ∈ Y ∧
        μ {u} = ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) ∧
        μ (Y \ {u}) = 0 ∧
        ENNReal.ofReal b < planarBrownianMotion u
          {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
            ContinuousPath.exitTime Y p} := by
  obtain ⟨Y, hY, hYA, u, hu, heq, hzero, hlarge, hp⟩ :=
    exists_concentrated_badWitness_of_compact_tests μ r z a b hfinite hsmall hcomp hbad
  have huA : u ∈ annulus z (3 * r) (5 * r) := by
    have hd := mem_sphere.mp hu
    change dist u z < 5 * r ∧ ¬ dist u z ≤ 3 * r
    rw [hd]
    constructor <;> linarith
  have huY := startingPoint_mem_of_positive_survival
    (isOpen_ball.sdiff isClosed_closedBall) huA (lt_of_le_of_lt zero_le hp)
  have hle : μ {u} ≤ μ Y := measure_mono (singleton_subset_iff.mpr huY)
  exact ⟨Y, hY, hYA, u, hu, huY, le_antisymm (heq ▸ hle) hlarge, hzero, hp⟩

/-- The starting points whose atom mass reaches a positive threshold form a
finite set when the annulus has finite mass. -/
theorem finite_large_starting_atoms
    (μ : Measure ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) (c : ℝ≥0∞) (hc : 0 < c)
    (hfinite : μ (annulus z (3 * r) (5 * r)) ≠ ∞) :
    {u : ℂ | u ∈ sphere z (4 * r) ∧ c ≤ μ {u}}.Finite := by
  apply (finite_atoms_above_of_measure_ne_top μ (annulus z (3 * r) (5 * r))
    hfinite c hc).subset
  intro u hu
  refine ⟨?_, hu.2⟩
  have hd := mem_sphere.mp hu.1
  change dist u z < 5 * r ∧ ¬ dist u z ≤ 3 * r
  rw [hd]
  constructor <;> linarith

open MarkovProcess in
/-- Strict compact-obstacle tests imply the good-annulus inequality at every
starting point whose atom is smaller than the threshold. -/
theorem goodAnnulus_test_of_compact_tests_of_small_starting_atom
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
    (Y : Set ℂ) (hY : MeasurableSet Y) (hYA : Y ⊆ annulus z (3 * r) (5 * r))
    (hmass : μ Y ≤ ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)))
    (u : ℂ) (hu : u ∈ sphere z (4 * r))
    (hatom : μ {u} < ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r))) :
    planarBrownianMotion u
      {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
        ContinuousPath.exitTime Y p} ≤ ENNReal.ofReal b := by
  by_contra hnot
  have hp := lt_of_not_ge hnot
  have hA : IsOpen (annulus z (3 * r) (5 * r)) := isOpen_ball.sdiff isClosed_closedBall
  obtain ⟨K, hK, hKA, hKmass, hprob⟩ :=
    exists_compact_obstacle_of_badWitness_of_mass_away μ hA hY hYA hfinite
      (ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r))) (ENNReal.ofReal b)
      hmass u hp (fun heq => measure_sdiff_singleton_pos_of_gt μ Y u (heq ▸ hatom))
      (hsmall u hu)
  exact (not_le_of_gt hprob) (hcomp K hK hKA hKmass u hu)

open MarkovProcess in
/-- Compact-obstacle tests reduce the remaining good-annulus tests to the
starting points whose atom mass reaches the threshold. -/
theorem isGoodAnnulus_iff_compact_tests_and_large_atom_tests
    (μ : Measure ℂ) (r : ℝ) (z : ℂ) (a b : ℝ)
    (hfinite : μ (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hsmall : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε) :
    IsGoodAnnulus μ r z a b ↔
      (∀ K : Set ℂ, IsCompact K → K ⊆ annulus z (3 * r) (5 * r) →
        μ (annulus z (3 * r) (5 * r) \ K) <
          ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) →
        ∀ u ∈ sphere z (4 * r), planarBrownianMotion u
          {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
            ContinuousPath.exitTime (annulus z (3 * r) (5 * r) \ K) p} ≤ ENNReal.ofReal b) ∧
      (∀ Y : Set ℂ, MeasurableSet Y → Y ⊆ annulus z (3 * r) (5 * r) →
        μ Y ≤ ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) →
        ∀ u ∈ sphere z (4 * r),
          ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) ≤ μ {u} →
          planarBrownianMotion u
            {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
              ContinuousPath.exitTime Y p} ≤ ENNReal.ofReal b) := by
  have hA : IsOpen (annulus z (3 * r) (5 * r)) := isOpen_ball.sdiff isClosed_closedBall
  constructor
  · intro hgood
    constructor
    · intro K hK hKA hmass u hu
      exact hgood _ (hA.measurableSet.diff hK.measurableSet) sdiff_subset hmass.le u hu
    · intro Y hY hYA hmass u hu _
      exact hgood Y hY hYA hmass u hu
  · rintro ⟨hcomp, hlarge⟩ Y hY hYA hmass u hu
    by_cases hatom : ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) ≤ μ {u}
    · exact hlarge Y hY hYA hmass u hu hatom
    · exact goodAnnulus_test_of_compact_tests_of_small_starting_atom μ r z a b
        hfinite hsmall hcomp Y hY hYA hmass u hu (lt_of_not_ge hatom)

end HarmonicBalls
