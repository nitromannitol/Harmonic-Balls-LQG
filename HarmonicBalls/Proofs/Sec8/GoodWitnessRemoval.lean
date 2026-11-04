import HarmonicBalls.Proofs.Sec8.GoodWitnessStrict

/-! # Removing a rare compact obstacle from a witness

A bad witness at the non-strict mass threshold becomes a strict one after
removing a positive-mass compact set whose Brownian hitting probability is
smaller than the survival-probability margin.
-/

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

open MarkovProcess in
/-- Removing an obstacle from a survival set loses at most the probability
of hitting that obstacle before exiting the domain. -/
theorem survival_sdiff_probability_le (U Y Z : Set ℂ) (u : ℂ) :
    planarBrownianMotion u
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Y p} ≤
    planarBrownianMotion u
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (Y \ Z) p} +
    planarBrownianMotion u
      {p | ¬ ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Zᶜ p} := by
  calc
    _ ≤ planarBrownianMotion u
        ({p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (Y \ Z) p} ∪
         {p | ¬ ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Zᶜ p}) := by
      apply measure_mono
      intro p hp
      by_cases hz : ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Zᶜ p
      · left
        apply (ContinuousPath.le_exitTime_iff (Y \ Z) p _).2
        intro t ht
        by_cases hy : p t ∈ Y
        · have hz' : p t ∈ Z := by
            by_contra hn
            exact ht ⟨hy, hn⟩
          exact hz.trans (ContinuousPath.exitTime_le_of_notMem Zᶜ p t (by simpa using hz'))
        · exact hp.trans (ContinuousPath.exitTime_le_of_notMem Y p t hy)
      · exact Or.inr hz
    _ ≤ _ := measure_union_le _ _

open MarkovProcess in
/-- A positive-mass compact set with sufficiently small hitting probability
can be removed to make a bad witness strictly smaller than the threshold. -/
theorem exists_strict_badWitness_of_rare_compact
    (μ : Measure ℂ) {U Y Z : Set ℂ}
    (hY : MeasurableSet Y) (hYU : Y ⊆ U) (hfinite : μ U ≠ ∞)
    (hZ : IsCompact Z) (hZY : Z ⊆ Y) (hZpos : 0 < μ Z)
    (a b : ℝ≥0∞) (hmass : μ Y ≤ a) (u : ℂ)
    (hgap : b + planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Zᶜ p} <
      planarBrownianMotion u
        {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Y p}) :
    ∃ Y' : Set ℂ, MeasurableSet Y' ∧ Y' ⊆ U ∧ μ Y' < a ∧
      b < planarBrownianMotion u
        {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Y' p} := by
  have hYfin : μ Y ≠ ∞ := ne_top_of_le_ne_top hfinite (measure_mono hYU)
  have hZfin : μ Z ≠ ∞ := ne_top_of_le_ne_top hYfin (measure_mono hZY)
  have hless : μ (Y \ Z) < μ Y := by
    apply measure_sdiff_lt_of_lt_add hZ.measurableSet.nullMeasurableSet hZY hZfin
    simpa only [add_comm] using (ENNReal.lt_add_right hYfin hZpos.ne')
  refine ⟨Y \ Z, hY.diff hZ.measurableSet, sdiff_subset.trans hYU,
    hless.trans_le hmass, ?_⟩
  have hbound := survival_sdiff_probability_le U Y Z u
  by_contra hn
  have hle : planarBrownianMotion u
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (Y \ Z) p} ≤ b := le_of_not_gt hn
  have : planarBrownianMotion u
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Y p} ≤
      b + planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Zᶜ p} :=
    hbound.trans (add_le_add hle le_rfl)
  exact (not_le_of_gt hgap) this

open MarkovProcess in
/-- If arbitrarily rarely hit positive-mass compact subsets can be removed at
an exact mass threshold, every bad witness has a single compact-obstacle
replacement with a strict mass bound. -/
theorem exists_compact_obstacle_of_badWitness_of_rare_removal
    (μ : Measure ℂ) {U Y : Set ℂ} (hU : IsOpen U)
    (hY : MeasurableSet Y) (hYU : Y ⊆ U) (hfinite : μ U ≠ ∞)
    (a b : ℝ≥0∞) (hmass : μ Y ≤ a) (u : ℂ)
    (hp : b < planarBrownianMotion u
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Y p})
    (hrare : μ Y = a → ∀ ε : ℝ≥0∞, 0 < ε → ∃ Z : Set ℂ,
      IsCompact Z ∧ Z ⊆ Y ∧ 0 < μ Z ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Zᶜ p} < ε) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ U ∧ μ (U \ K) < a ∧
      b < planarBrownianMotion u
        {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (U \ K) p} := by
  by_cases hstrict : μ Y < a
  · exact exists_compact_obstacle_of_strict_badWitness μ hU hY hYU hfinite a b hstrict u hp
  · have heq : μ Y = a := le_antisymm hmass (le_of_not_gt hstrict)
    obtain ⟨δ, hδ, hgap⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hp
    obtain ⟨Z, hZ, hZY, hZpos, hsmall⟩ := hrare heq δ (by exact_mod_cast hδ)
    have hgap' : b + planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Zᶜ p} <
        planarBrownianMotion u
          {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Y p} :=
      (add_le_add le_rfl hsmall.le).trans_lt hgap
    obtain ⟨Y', hY', hY'U, hY'mass, hp'⟩ :=
      exists_strict_badWitness_of_rare_compact μ hY hYU hfinite hZ hZY hZpos a b hmass u hgap'
    exact exists_compact_obstacle_of_strict_badWitness μ hU hY' hY'U hfinite a b hY'mass u hp'

open MarkovProcess in
/-- A positive-mass support point whose small neighborhoods are hit with
arbitrarily small probability supplies the compact sets needed for removal. -/
theorem exists_rare_positive_compact_of_support_point
    (μ : Measure ℂ) {U Y : Set ℂ} (hY : MeasurableSet Y) (hfinite : μ Y ≠ ∞)
    (u x : ℂ)
    (hsupport : ∀ ρ : ℝ, 0 < ρ → 0 < μ (Y ∩ ball x ρ))
    (hsmall : ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ Z : Set ℂ, IsCompact Z ∧ Z ⊆ Y ∧ 0 < μ Z ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Zᶜ p} < ε := by
  intro ε hε
  obtain ⟨ρ, hρ, hhit⟩ := hsmall ε hε
  have hballfin : μ (Y ∩ ball x ρ) ≠ ∞ :=
    ne_top_of_le_ne_top hfinite (measure_mono inter_subset_left)
  obtain ⟨Z, hZsub, hZ, hZpos⟩ :=
    (hY.inter isOpen_ball.measurableSet).exists_lt_isCompact_of_ne_top hballfin (hsupport ρ hρ)
  refine ⟨Z, hZ, hZsub.trans inter_subset_left, hZpos, ?_⟩
  apply (measure_mono ?_).trans_lt hhit
  intro p hp havoid
  apply hp
  exact havoid.trans (ContinuousPath.exitTime_mono
    (compl_subset_compl.mpr (hZsub.trans inter_subset_right)) p)

end HarmonicBalls
