import HarmonicBalls.Proofs.Sec8.PositiveMassSupport
import HarmonicBalls.Proofs.Sec6.BrownianUnitIncrements

/-! # Continuous-path exit under an open exhaustion

An increasing open cover of a domain approximates its exit time from below.
This is the pathwise ingredient for approximating compact obstacles by a
countable family of larger obstacles.
-/

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HarmonicBalls

open MarkovProcess in
/-- A continuous path remains in one member of an increasing open cover
throughout any compact time interval strictly before exit from the union. -/
theorem exists_lt_exitTime_of_open_iUnion {V : ℕ → Set ℂ}
    (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    (p : ContinuousPath ℂ) (T : ℝ≥0)
    (hT : (T : ℝ≥0∞) < ContinuousPath.exitTime (⋃ n, V n) p) :
    ∃ N, ∀ n ≥ N, (T : ℝ≥0∞) < ContinuousPath.exitTime (V n) p := by
  have hc : IsCompact ((p : ℝ≥0 → ℂ) '' Icc 0 T) := isCompact_Icc.image p.continuous
  have hcover : (p : ℝ≥0 → ℂ) '' Icc 0 T ⊆ ⋃ n, V n := by
    rintro x ⟨t, ht, rfl⟩
    apply ContinuousPath.mem_of_lt_exitTime
    exact (show (t : ℝ≥0∞) ≤ T from by exact_mod_cast ht.2).trans_lt hT
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover V hopen hcover
  refine ⟨s.sup id, fun n hn => ?_⟩
  have hsub : (p : ℝ≥0 → ℂ) '' Icc 0 T ⊆ V n := by
    refine hs.trans (iUnion₂_subset fun i hi => hmono ?_)
    exact (Finset.le_sup (f := id) hi).trans hn
  by_contra hle
  rw [not_lt, ContinuousPath.exitTime_le_iff_mem_hitsSetBy (V n) (hopen n) T p] at hle
  obtain ⟨t, ht⟩ := hle
  exact ht (hsub ⟨t, mem_Icc.mpr ⟨zero_le, t.2⟩, rfl⟩)

open MarkovProcess in
/-- Exit from the union of increasing open sets is the supremum of their
exit times, including the case of an infinite exit time. -/
theorem exitTime_iUnion_eq_iSup {V : ℕ → Set ℂ}
    (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V) (p : ContinuousPath ℂ) :
    ContinuousPath.exitTime (⋃ n, V n) p = ⨆ n, ContinuousPath.exitTime (V n) p := by
  apply le_antisymm
  · apply le_of_forall_lt
    intro t ht
    have htfin : t ≠ ∞ := ne_top_of_lt (ht.trans_le le_top)
    have htcoe : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) = t := ENNReal.coe_toNNReal htfin
    obtain ⟨N, hN⟩ := exists_lt_exitTime_of_open_iUnion hopen hmono p t.toNNReal
      (htcoe ▸ ht)
    rw [← htcoe]
    exact (hN N le_rfl).trans_le (le_iSup (fun n => ContinuousPath.exitTime (V n) p) N)
  · exact iSup_le fun n => ContinuousPath.exitTime_mono (subset_iUnion V n) p

open MarkovProcess in
/-- Strict survival against the limit domain is the union of strict
survival events against the approximating open domains. -/
theorem strict_survival_iUnion {U : Set ℂ} {V : ℕ → Set ℂ}
    (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V) :
    {p : ContinuousPath ℂ | ContinuousPath.exitTime U p <
        ContinuousPath.exitTime (⋃ n, V n) p} =
      ⋃ n, {p | ContinuousPath.exitTime U p < ContinuousPath.exitTime (V n) p} := by
  ext p
  simp only [mem_ofPred_eq, mem_iUnion, exitTime_iUnion_eq_iSup hopen hmono, lt_iSup_iff]

open MarkovProcess in
/-- For a measure on path space, strict survival probabilities
increase to their value for the union domain. -/
theorem measure_strict_survival_iUnion (Q : Measure (ContinuousPath ℂ))
    {U : Set ℂ} {V : ℕ → Set ℂ}
    (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V) :
    Q {p | ContinuousPath.exitTime U p < ContinuousPath.exitTime (⋃ n, V n) p} =
      ⨆ n, Q {p | ContinuousPath.exitTime U p < ContinuousPath.exitTime (V n) p} := by
  rw [strict_survival_iUnion hopen hmono]
  apply Monotone.measure_iUnion
  · intro m n hmn p hp
    exact hp.trans_le (ContinuousPath.exitTime_mono (hmono hmn) p)

open MarkovProcess in
/-- Before a finite exit from an open domain, avoidance of a closed obstacle
contained in that domain is strict: the two exit times cannot coincide. -/
theorem exitTime_lt_obstacle_of_le {U K : Set ℂ} (hU : IsOpen U)
    (hK : IsClosed K) (hKU : K ⊆ U) (p : ContinuousPath ℂ)
    (hstart : p 0 ∈ U) (hfin : ContinuousPath.exitTime U p ≠ ∞)
    (havoid : ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Kᶜ p) :
    ContinuousPath.exitTime U p < ContinuousPath.exitTime Kᶜ p := by
  apply lt_of_le_of_ne havoid
  intro heq
  let t : ℝ≥0 := (ContinuousPath.exitTime U p).toNNReal
  have ht : (t : ℝ≥0∞) = ContinuousPath.exitTime U p := ENNReal.coe_toNNReal hfin
  have hfront := ContinuousPath.coordinate_exitTime_mem_frontier U hU p hstart hfin
  have hout : p t ∉ U := by
    have := hfront
    rw [hU.frontier_eq] at this
    exact this.2
  have hhit : ContinuousPath.exitTime Kᶜ p ≤ (t : ℝ≥0∞) := by rw [ht, heq]
  obtain ⟨s, hs⟩ := (ContinuousPath.exitTime_le_iff_mem_hitsSetBy Kᶜ
    hK.isOpen_compl t p).mp hhit
  have hts : t ≤ (s : ℝ≥0) := by
    have hle := ContinuousPath.exitTime_le_of_notMem Kᶜ p s hs
    rw [← heq, ← ht, ENNReal.coe_le_coe] at hle
    exact hle
  have hst : (s : ℝ≥0) = t := le_antisymm s.property hts
  apply hout
  apply hKU
  simpa only [hst, mem_compl_iff, not_not] using hs

open MarkovProcess in
/-- Avoidance probabilities for decreasing closed obstacles converge to the
avoidance probability of their intersection, provided exit is almost surely
finite and paths start in the domain. -/
theorem measure_avoid_iInter_closed (Q : Measure (ContinuousPath ℂ))
    {U K : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U)
    (Ks : ℕ → Set ℂ) (hKs : ∀ n, IsClosed (Ks n)) (hanti : Antitone Ks)
    (hinter : ⋂ n, Ks n = K)
    (hstart : ∀ᵐ p ∂Q, p 0 ∈ U)
    (hfin : ∀ᵐ p ∂Q, ContinuousPath.exitTime U p ≠ ∞) :
    Q {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Kᶜ p} =
      ⨆ n, Q {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (Ks n)ᶜ p} := by
  have hK : IsClosed K := by rw [← hinter]; exact isClosed_iInter hKs
  have hunion : ⋃ n, (Ks n)ᶜ = Kᶜ := by rw [← compl_iInter, hinter]
  have hVmono : Monotone fun n => (Ks n)ᶜ := by
    intro m n hmn
    exact compl_subset_compl.mpr (hanti hmn)
  have heq : Q {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Kᶜ p} =
      Q {p | ContinuousPath.exitTime U p < ContinuousPath.exitTime Kᶜ p} := by
    apply measure_congr
    filter_upwards [hstart, hfin] with p hp hf
    exact propext ⟨exitTime_lt_obstacle_of_le hU hK hKU p hp hf, le_of_lt⟩
  apply le_antisymm
  · rw [heq, ← hunion, measure_strict_survival_iUnion Q (fun n => (hKs n).isOpen_compl) hVmono]
    apply iSup_le
    intro n
    calc
      Q {p | ContinuousPath.exitTime U p < ContinuousPath.exitTime (Ks n)ᶜ p} ≤
          Q {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (Ks n)ᶜ p} :=
            measure_mono (by
              intro p hp
              change ContinuousPath.exitTime U p < ContinuousPath.exitTime (Ks n)ᶜ p at hp
              change ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (Ks n)ᶜ p
              exact le_of_lt hp)
      _ ≤ _ := le_iSup (fun j : ℕ => Q {p | ContinuousPath.exitTime U p ≤
        ContinuousPath.exitTime (Ks j)ᶜ p}) n
  · apply iSup_le
    intro n
    apply measure_mono
    intro p hp
    change ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (Ks n)ᶜ p at hp
    change ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Kᶜ p
    apply hp.trans
    apply ContinuousPath.exitTime_mono
    apply compl_subset_compl.mpr
    rw [← hinter]
    exact iInter_subset Ks n

open MarkovProcess in
/-- Planar Brownian avoidance probabilities converge for decreasing closed
obstacles in a bounded open domain. -/
theorem planarBrownianMotion_avoid_iInter_closed {U K : Set ℂ}
    (hU : IsOpen U) (hbounded : Bornology.IsBounded U) (hKU : K ⊆ U)
    (Ks : ℕ → Set ℂ) (hKs : ∀ n, IsClosed (Ks n)) (hanti : Antitone Ks)
    (hinter : ⋂ n, Ks n = K) {u : ℂ} (hu : u ∈ U) :
    planarBrownianMotion u {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Kᶜ p} =
      ⨆ n, planarBrownianMotion u
        {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (Ks n)ᶜ p} := by
  obtain ⟨R, hR⟩ := hbounded.subset_ball u
  apply measure_avoid_iInter_closed (planarBrownianMotion u) hU hKU Ks hKs hanti hinter
  · filter_upwards [ae_planarBrownianMotion_eval_zero u] with p hp
    simpa [hp] using hu
  · filter_upwards [Section6.ae_planarBrownianMotion_exitTime_ball_lt_top u R] with p hp
    exact ne_top_of_lt ((ContinuousPath.exitTime_mono hR p).trans_lt hp)

open MarkovProcess in
/-- A strict avoidance-probability threshold persists for one sufficiently
small closed enlargement of the obstacle. -/
theorem exists_closed_obstacle_approximation_of_avoid_gt {U K : Set ℂ}
    (hU : IsOpen U) (hbounded : Bornology.IsBounded U) (hKU : K ⊆ U)
    (Ks : ℕ → Set ℂ) (hKs : ∀ n, IsClosed (Ks n)) (hanti : Antitone Ks)
    (hinter : ⋂ n, Ks n = K) {u : ℂ} (hu : u ∈ U) (b : ℝ≥0∞)
    (hp : b < planarBrownianMotion u
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Kᶜ p}) :
    ∃ n, b < planarBrownianMotion u
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (Ks n)ᶜ p} := by
  rw [planarBrownianMotion_avoid_iInter_closed hU hbounded hKU Ks hKs hanti hinter hu,
    lt_iSup_iff] at hp
  exact hp

end HarmonicBalls
