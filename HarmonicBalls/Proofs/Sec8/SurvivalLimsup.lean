import HarmonicBalls.Proofs.Sec8.ThresholdAtomMeasurability
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Limsup witnesses for survival probabilities -/

open MeasureTheory Metric Set ProbabilityTheory Filter
open scoped ENNReal

namespace HarmonicBalls

/-- A uniform lower bound for events remains a lower bound for their limsup,
under a finite measure. -/
theorem le_measure_limsup_of_forall_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (E : ℕ → Set α)
    (hE : ∀ n, MeasurableSet (E n)) (c : ℝ≥0∞) (hc : ∀ n, c ≤ μ (E n)) :
    c ≤ μ (Filter.limsup E atTop) := by
  let T : ℕ → Set α := fun m => ⋃ n ≥ m, E n
  have hanti : Antitone T := by
    intro m n hmn x hx
    simp only [T, mem_iUnion] at hx ⊢
    obtain ⟨k, hkn, hxk⟩ := hx
    exact ⟨k, le_trans hmn hkn, hxk⟩
  have hTm : ∀ n, NullMeasurableSet (T n) μ := fun n =>
    (MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => hE k).nullMeasurableSet
  have hlim : Filter.limsup E atTop = ⋂ n, T n := by
    simp only [Filter.limsup_eq_iInf_iSup_of_nat, iInf_eq_iInter, iSup_eq_iUnion, T]
  rw [hlim, hanti.measure_iInter hTm ⟨0, measure_ne_top _ _⟩]
  apply le_iInf
  intro n
  apply (hc n).trans
  apply measure_mono
  intro x hx
  simp only [T, mem_iUnion]
  exact ⟨n, le_rfl, hx⟩

open MarkovProcess in
/-- Paths that survive infinitely many sets survive their set-theoretic limsup. -/
theorem limsup_survival_subset_survival_limsup (U : Set ℂ) (Y : ℕ → Set ℂ) :
    Filter.limsup (fun n => {p : ContinuousPath ℂ |
      ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (Y n) p}) atTop ⊆
    {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (Filter.limsup Y atTop) p} := by
  intro p hp
  simp only [Filter.limsup_eq_iInf_iSup_of_nat, iInf_eq_iInter, iSup_eq_iUnion,
    mem_iInter, mem_iUnion, mem_ofPred_eq] at hp
  apply (ContinuousPath.le_exitTime_iff _ p _).2
  intro t ht
  have hnot : ∃ m, ∀ n ≥ m, p t ∉ Y n := by
    simpa only [Filter.limsup_eq_iInf_iSup_of_nat, iInf_eq_iInter, iSup_eq_iUnion,
      mem_iInter, mem_iUnion, not_forall, not_exists, not_and] using ht
  obtain ⟨m, hm⟩ := hnot
  obtain ⟨n, hmn, hn⟩ := hp m
  exact hn.trans (ContinuousPath.exitTime_le_of_notMem (Y n) p t (hm n hmn))

/-- Summably small mass away from one point disappears in the limsup. -/
theorem measure_limsup_sdiff_singleton_eq_zero (μ : Measure ℂ) (Y : ℕ → Set ℂ)
    (u : ℂ) (hsum : (∑' n, μ (Y n \ {u})) ≠ ∞) :
    μ ((Filter.limsup Y atTop) \ {u}) = 0 := by
  have hz := measure_limsup_atTop_eq_zero (μ := μ) hsum
  apply measure_mono_null _ hz
  intro x hx
  simp only [Filter.limsup_eq_iInf_iSup_of_nat, iInf_eq_iInter, iSup_eq_iUnion,
    mem_iInter, mem_iUnion, Set.mem_sdiff] at hx ⊢
  intro m
  obtain ⟨n, hmn, hn⟩ := hx.1 m
  exact ⟨n, hmn, hn, hx.2⟩

open MarkovProcess in
/-- Uniform survival along measurable witnesses with summable mass away from
`u` produces a witness whose mass is carried by `u`. -/
theorem exists_concentrated_survival_witness_of_summable
    (μ : Measure ℂ) (U : Set ℂ) (u : ℂ) (Y : ℕ → Set ℂ)
    (hY : ∀ n, MeasurableSet (Y n)) (hYU : ∀ n, Y n ⊆ U)
    (hsum : (∑' n, μ (Y n \ {u})) ≠ ∞)
    (hE : ∀ n, MeasurableSet {p : ContinuousPath ℂ |
      ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (Y n) p})
    (b c : ℝ≥0∞) (hbc : b < c)
    (hc : ∀ n, c ≤ planarBrownianMotion u {p |
      ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (Y n) p}) :
    ∃ V : Set ℂ, MeasurableSet V ∧ V ⊆ U ∧ μ V ≤ μ {u} ∧
      b < planarBrownianMotion u {p | ContinuousPath.exitTime U p ≤
        ContinuousPath.exitTime V p} := by
  let V := Filter.limsup Y atTop
  have hV : MeasurableSet V := by
    simp only [V, Filter.limsup_eq_iInf_iSup_of_nat, iInf_eq_iInter, iSup_eq_iUnion]
    exact MeasurableSet.iInter fun m => MeasurableSet.iUnion fun n =>
      MeasurableSet.iUnion fun _ => hY n
  have hVU : V ⊆ U := by
    intro x hx
    simp only [V, Filter.limsup_eq_iInf_iSup_of_nat, iInf_eq_iInter, iSup_eq_iUnion,
      mem_iInter, mem_iUnion] at hx
    obtain ⟨n, _, hn⟩ := hx 0
    exact hYU n hn
  have hmass : μ V ≤ μ {u} := by
    have hz : μ (V \ {u}) = 0 := measure_limsup_sdiff_singleton_eq_zero μ Y u hsum
    calc
      μ V ≤ μ ((V \ {u}) ∪ {u}) := measure_mono (by intro x hx; by_cases h : x = u <;> simp [hx, h])
      _ ≤ μ (V \ {u}) + μ {u} := measure_union_le _ _
      _ = μ {u} := by rw [hz, zero_add]
  have hp : c ≤ planarBrownianMotion u {p | ContinuousPath.exitTime U p ≤
      ContinuousPath.exitTime V p} := by
    apply (le_measure_limsup_of_forall_le (planarBrownianMotion u) _ hE c hc).trans
    exact measure_mono (limsup_survival_subset_survival_limsup U Y)
  exact ⟨V, hV, hVU, hmass, hbc.trans_le hp⟩

open MarkovProcess in
/-- A concentrated witness with strict survival can be approximated by a
rational compact obstacle while making the remaining off-point mass arbitrarily small. -/
theorem exists_rationalBallObstacle_of_concentrated_survival
    {D U Y : Set ℂ} (hD : Dense D) (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (μ : Measure ℂ) (hfinite : μ U ≠ ∞) (u : ℂ) (hu : u ∈ U)
    (hY : MeasurableSet Y) (hYU : Y ⊆ U) (hnull : μ (Y \ {u}) = 0)
    (c ε : ℝ≥0∞) (hε : 0 < ε)
    (hp : c < planarBrownianMotion u {p |
      ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Y p}) :
    ∃ s : Finset (D × ℚ), rationalBallObstacle D s ⊆ U ∧
      μ ((U \ rationalBallObstacle D s) \ {u}) < ε ∧
      c < planarBrownianMotion u {p | ContinuousPath.exitTime U p ≤
        ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ p} := by
  let ν := μ.restrict ({u}ᶜ)
  have hν (V : Set ℂ) (hV : MeasurableSet V) : ν V = μ (V \ {u}) := by
    simp [ν, Measure.restrict_apply hV, sdiff_eq]
  have hνfin : ν U ≠ ∞ := by
    rw [hν U hU.measurableSet]
    exact ne_top_of_le_ne_top hfinite (measure_mono sdiff_subset)
  obtain ⟨K, hK, hmono, hsub, hYsub, hmass⟩ :=
    exists_compact_obstacle_exhaustion (μ := ν) hU.measurableSet hY hYU hνfin
  have hνY : ν Y = 0 := by rw [hν Y hY, hnull]
  have hinf : (⨅ n, ν (U \ K n)) = 0 := by
    rw [← measure_sdiff_iUnion_compact_eq_iInf ν hU.measurableSet hνfin K hK hmono,
      hmass, hνY]
  have hex : ∃ n, ν (U \ K n) < ε := by
    rw [← hinf] at hε
    exact iInf_lt_iff.mp hε
  obtain ⟨n, hn⟩ := hex
  have hKU : K n ⊆ U := (hsub n).trans sdiff_subset
  have hprob : c < planarBrownianMotion u {p | ContinuousPath.exitTime U p ≤
      ContinuousPath.exitTime (K n)ᶜ p} := by
    apply hp.trans_le
    apply measure_mono
    intro p hpath
    change ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Y p at hpath
    change ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (K n)ᶜ p
    apply hpath.trans
    apply ContinuousPath.exitTime_mono
    intro x hx hmem
    exact (hsub n hmem).2 hx
  obtain ⟨s, hKs, hsU, hprob'⟩ := exists_rationalBallObstacle_of_avoid_gt
    hD hU hbounded (hK n) hKU hu c hprob
  refine ⟨s, hsU, ?_, hprob'⟩
  rw [← hν (U \ rationalBallObstacle D s)
    (hU.measurableSet.diff (isCompact_rationalBallObstacle D s).measurableSet)]
  exact (measure_mono (show U \ rationalBallObstacle D s ⊆ U \ K n from
    fun x hx => ⟨hx.1, fun hk => hx.2 (hKs hk)⟩)).trans_lt hn

open MarkovProcess in
/-- Concentrated survival witnesses are equivalent to countably many rational
obstacle tests, for any summable positive sequence of mass tolerances. -/
theorem exists_concentrated_survival_iff_rational_obstacles
    {D U : Set ℂ} (hD : Dense D) (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (μ : Measure ℂ) (hfinite : μ U ≠ ∞) (u : ℂ) (hu : u ∈ U)
    (b : ℝ≥0∞) (ε : ℕ → ℝ≥0∞) (hε : ∀ n, 0 < ε n)
    (hεsum : (∑' n, ε n) ≠ ∞) :
    (∃ Y : Set ℂ, MeasurableSet Y ∧ Y ⊆ U ∧ μ (Y \ {u}) = 0 ∧
      b < planarBrownianMotion u {p | ContinuousPath.exitTime U p ≤
        ContinuousPath.exitTime Y p}) ↔
    ∃ c : ℝ≥0∞, b < c ∧ ∀ n, ∃ s : Finset (D × ℚ),
      rationalBallObstacle D s ⊆ U ∧
      μ ((U \ rationalBallObstacle D s) \ {u}) < ε n ∧
      c ≤ planarBrownianMotion u {p | ContinuousPath.exitTime U p ≤
        ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ p} := by
  constructor
  · rintro ⟨Y, hY, hYU, hnull, hp⟩
    obtain ⟨c, hbc, hcp⟩ := exists_between hp
    refine ⟨c, hbc, fun n => ?_⟩
    obtain ⟨s, hsU, hmass, hprob⟩ := exists_rationalBallObstacle_of_concentrated_survival
      hD hU hbounded μ hfinite u hu hY hYU hnull c (ε n) (hε n) hcp
    exact ⟨s, hsU, hmass, hprob.le⟩
  · rintro ⟨c, hbc, h⟩
    choose s hsU hmass hprob using h
    let Y : ℕ → Set ℂ := fun n => U \ rationalBallObstacle D (s n)
    have hY : ∀ n, MeasurableSet (Y n) := fun n =>
      hU.measurableSet.diff (isCompact_rationalBallObstacle D (s n)).measurableSet
    have hYU : ∀ n, Y n ⊆ U := fun _ => sdiff_subset
    have hsum : (∑' n, μ (Y n \ {u})) ≠ ∞ :=
      ne_top_of_le_ne_top hεsum (ENNReal.tsum_le_tsum fun n => (hmass n).le)
    have hE : ∀ n, MeasurableSet {p : ContinuousPath ℂ |
        ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (Y n) p} := by
      intro n
      have heq : {p : ContinuousPath ℂ | ContinuousPath.exitTime U p ≤
          ContinuousPath.exitTime (Y n) p} = {p | ContinuousPath.exitTime U p ≤
            ContinuousPath.exitTime (rationalBallObstacle D (s n))ᶜ p} := by
        ext p
        exact stay_sdiff_iff_avoid U (rationalBallObstacle D (s n)) p
      rw [heq]
      exact Section6.measurableSet_avoid_before_exit hU (isCompact_rationalBallObstacle D (s n))
    have hp : ∀ n, c ≤ planarBrownianMotion u {p | ContinuousPath.exitTime U p ≤
        ContinuousPath.exitTime (Y n) p} := by
      intro n
      convert hprob n using 1
      congr 1
      ext p
      exact stay_sdiff_iff_avoid U (rationalBallObstacle D (s n)) p
    let V := Filter.limsup Y atTop
    have hV : MeasurableSet V := by
      simp only [V, Filter.limsup_eq_iInf_iSup_of_nat, iInf_eq_iInter, iSup_eq_iUnion]
      exact MeasurableSet.iInter fun m => MeasurableSet.iUnion fun n =>
        MeasurableSet.iUnion fun _ => hY n
    have hVU : V ⊆ U := by
      intro x hx
      simp only [V, Filter.limsup_eq_iInf_iSup_of_nat, iInf_eq_iInter, iSup_eq_iUnion,
        mem_iInter, mem_iUnion] at hx
      obtain ⟨n, _, hn⟩ := hx 0
      exact hYU n hn
    have hVnull : μ (V \ {u}) = 0 := measure_limsup_sdiff_singleton_eq_zero μ Y u hsum
    have hVp : b < planarBrownianMotion u {p | ContinuousPath.exitTime U p ≤
        ContinuousPath.exitTime V p} := hbc.trans_le
      ((le_measure_limsup_of_forall_le (planarBrownianMotion u) _ hE c hp).trans
        (measure_mono (limsup_survival_subset_survival_limsup U Y)))
    exact ⟨V, hV, hVU, hVnull, hVp⟩

end HarmonicBalls
