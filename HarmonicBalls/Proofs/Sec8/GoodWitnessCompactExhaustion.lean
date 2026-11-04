import HarmonicBalls.Proofs.Sec8.GoodEventWitnesses
import HarmonicBalls.Proofs.Sec6.BrownianAvoidance

/-! # Compact obstacle exhaustion for bad annuli

For finite annulus mass, an arbitrary bad Borel witness may be enlarged to
one whose complement in the annulus is an increasing union of compact sets.
The enlargement keeps exactly the same mass, including at the non-strict
mass threshold, and can only increase the survival probability.
-/

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

/-- A Borel subset of a finite-mass Borel set can be enlarged, without
changing its mass, by removing an increasing union of compact obstacles. -/
theorem exists_compact_obstacle_exhaustion {μ : Measure ℂ} {A Y : Set ℂ}
    (hA : MeasurableSet A) (hY : MeasurableSet Y) (hYA : Y ⊆ A)
    (hfinite : μ A ≠ ∞) :
    ∃ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) ∧ Monotone K ∧
      (∀ n, K n ⊆ A \ Y) ∧ Y ⊆ A \ ⋃ n, K n ∧
      μ (A \ ⋃ n, K n) = μ Y := by
  have hfin : μ (A \ Y) ≠ ∞ := ne_top_of_le_ne_top hfinite (measure_mono sdiff_subset)
  obtain ⟨K, L, hK, hsub, hL, hmono, hLK, hmass⟩ :=
    Section6.compact_full_mass_of_summable_exceptions (hA.diff hY) hfin
      (fun _ => ∅) (fun _ => MeasurableSet.empty) (by simp)
  have hsubL : ∀ n, L n ⊆ A \ Y := by
    intro n
    exact (hLK n).trans (by simpa using hsub n)
  have hsubset : Y ⊆ A \ ⋃ n, L n := by
    intro x hx
    refine ⟨hYA hx, ?_⟩
    intro hxU
    obtain ⟨n, hn⟩ := mem_iUnion.mp hxU
    exact (hsubL n hn).2 hx
  have hnull : μ ((A \ ⋃ n, L n) \ Y) = 0 := by
    apply measure_mono_null _ hmass
    intro x hx
    exact ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩
  exact ⟨L, hL, hmono, hsubL, hsubset,
    (measure_eq_measure_of_null_sdiff hsubset hnull).symm⟩

open MarkovProcess in
/-- Avoiding obstacles before exit is the same as remaining in their
complement within the domain until exit. -/
theorem stay_sdiff_iff_avoid (U F : Set ℂ) (p : ContinuousPath ℂ) :
    ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (U \ F) p ↔
      ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Fᶜ p := by
  constructor
  · intro h
    exact h.trans (ContinuousPath.exitTime_mono (by intro x hx; exact hx.2) p)
  · intro h
    apply (ContinuousPath.le_exitTime_iff (U \ F) p _).2
    intro t ht
    by_cases hU : p t ∈ U
    · have hF : p t ∈ F := by
        by_contra hn
        exact ht ⟨hU, hn⟩
      exact h.trans (ContinuousPath.exitTime_le_of_notMem Fᶜ p t (by simpa using hF))
    · exact ContinuousPath.exitTime_le_of_notMem U p t hU

open MarkovProcess in
/-- The survival event for an increasing compact-obstacle witness is Borel. -/
theorem measurableSet_stay_sdiff_iUnion_compact {U : Set ℂ} (hU : IsOpen U)
    (K : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n)) :
    MeasurableSet {p : ContinuousPath ℂ | ContinuousPath.exitTime U p ≤
      ContinuousPath.exitTime (U \ ⋃ n, K n) p} := by
  have heq : {p : ContinuousPath ℂ | ContinuousPath.exitTime U p ≤
      ContinuousPath.exitTime (U \ ⋃ n, K n) p} =
      ⋂ n, {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (K n)ᶜ p} := by
    rw [← Section6.avoid_iUnion_before_exit]
    ext p
    exact stay_sdiff_iff_avoid U (⋃ n, K n) p
  rw [heq]
  exact MeasurableSet.iInter fun n => Section6.measurableSet_avoid_before_exit hU (hK n)

open MarkovProcess in
/-- For fixed compact obstacles, the survival probability is a measurable
function of the Brownian starting point. -/
theorem measurable_stay_sdiff_iUnion_compact {U : Set ℂ} (hU : IsOpen U)
    (K : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n)) :
    Measurable (fun u : ℂ => planarBrownianMotion u
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (U \ ⋃ n, K n) p}) := by
  exact (Measure.measurable_coe (measurableSet_stay_sdiff_iUnion_compact hU K hK)).comp
    planarBrownianMotion.measurable

/-- The mass of the witness complement is the decreasing limit of the
masses obtained by deleting one compact obstacle. -/
theorem measure_sdiff_iUnion_compact_eq_iInf (μ : Measure ℂ) {U : Set ℂ}
    (hU : MeasurableSet U) (hfinite : μ U ≠ ∞)
    (K : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n)) (hmono : Monotone K) :
    μ (U \ ⋃ n, K n) = ⨅ n, μ (U \ K n) := by
  have heq : U \ ⋃ n, K n = ⋂ n, U \ K n := by
    ext x
    simp only [mem_sdiff, mem_iUnion, mem_iInter, not_exists, forall_and, forall_const]
  rw [heq]
  apply Antitone.measure_iInter
  · intro m n hmn x hx
    exact ⟨hx.1, fun hxn => hx.2 (hmono hmn hxn)⟩
  · intro n
    exact (hU.diff (hK n).measurableSet).nullMeasurableSet
  · exact ⟨0, ne_top_of_le_ne_top hfinite (measure_mono sdiff_subset)⟩

open MarkovProcess in
/-- The Brownian survival probability against a compact exhaustion is the
infimum of the single-obstacle survival probabilities. -/
theorem stay_sdiff_iUnion_compact_probability_eq_iInf {U : Set ℂ} (hU : IsOpen U)
    (K : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n)) (hmono : Monotone K) (u : ℂ) :
    planarBrownianMotion u {p | ContinuousPath.exitTime U p ≤
      ContinuousPath.exitTime (U \ ⋃ n, K n) p} =
      ⨅ n, planarBrownianMotion u {p | ContinuousPath.exitTime U p ≤
        ContinuousPath.exitTime (K n)ᶜ p} := by
  have heq : {p : ContinuousPath ℂ | ContinuousPath.exitTime U p ≤
      ContinuousPath.exitTime (U \ ⋃ n, K n) p} =
      ⋂ n, {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (K n)ᶜ p} := by
    rw [← Section6.avoid_iUnion_before_exit]
    ext p
    exact stay_sdiff_iff_avoid U (⋃ n, K n) p
  rw [heq]
  apply Antitone.measure_iInter
  · intro m n hmn p hp
    exact hp.trans (ContinuousPath.exitTime_mono (compl_subset_compl.mpr (hmono hmn)) p)
  · intro n
    exact (Section6.measurableSet_avoid_before_exit hU (hK n)).nullMeasurableSet
  · exact ⟨0, measure_ne_top _ _⟩

open MarkovProcess in
/-- For finite annulus mass, failure of the good-annulus condition has a
witness obtained by deleting an increasing union of compact obstacles. -/
theorem not_isGoodAnnulus_iff_compact_obstacle_witness
    (μ : Measure ℂ) (r : ℝ) (z : ℂ) (a b : ℝ)
    (hfinite : μ (annulus z (3 * r) (5 * r)) ≠ ∞) :
    ¬ IsGoodAnnulus μ r z a b ↔
      ∃ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) ∧ Monotone K ∧
        (∀ n, K n ⊆ annulus z (3 * r) (5 * r)) ∧
        μ (annulus z (3 * r) (5 * r) \ ⋃ n, K n) ≤
          ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) ∧
        ∃ u ∈ sphere z (4 * r), ENNReal.ofReal b < planarBrownianMotion u
          {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
            ContinuousPath.exitTime (annulus z (3 * r) (5 * r) \ ⋃ n, K n) p} := by
  have hA : MeasurableSet (annulus z (3 * r) (5 * r)) :=
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  constructor
  · intro hbad
    obtain ⟨Y, hY, hYA, hmass, u, hu, hp⟩ :=
      (not_isGoodAnnulus_iff_exists_badWitness μ r z a b).1 hbad
    obtain ⟨K, hK, hmono, hsub, hsubset, heq⟩ :=
      exists_compact_obstacle_exhaustion hA hY hYA hfinite
    refine ⟨K, hK, hmono, fun n => (hsub n).trans sdiff_subset, ?_, u, hu, ?_⟩
    · rwa [heq]
    · refine hp.trans_le (measure_mono ?_)
      intro p hp'
      exact hp'.trans (ContinuousPath.exitTime_mono hsubset p)
  · rintro ⟨K, hK, hmono, hsub, hmass, u, hu, hp⟩
    apply (not_isGoodAnnulus_iff_exists_badWitness μ r z a b).2
    refine ⟨annulus z (3 * r) (5 * r) \ ⋃ n, K n, ?_⟩
    exact ⟨hA.diff (MeasurableSet.iUnion fun n => (hK n).measurableSet),
      sdiff_subset, hmass, u, hu, hp⟩

end HarmonicBalls
