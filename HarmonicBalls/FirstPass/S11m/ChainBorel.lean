import HarmonicBalls.FirstPass.S11m.ChainMetric

/-!
# Borel measurability of the chain formula (route Step 3.4, "its Borelness")

FIRST-PASS fp-S11m. For countable `S` and `Q`, the chain formula `chainDistance S (D ω) Q x y` is a measurable function of
`ω` as soon as every evaluation `ω ↦ D ω a b` with `a, b ∈ S ∪ Q ∪ {x, y}` is measurable (route Step 3.4, and the decoder
of Step 3.2 which factors the metric evaluations at a countable dense set). No property of `D ω` as a length metric is
used: the infimum over chains is reindexed by a countable index set (`Fin (n+1) → S ∪ {x, y}`), and each term is a
measurable function of finitely many evaluations, a countable infimum of clearances, and a comparison.
-/

namespace HarmonicBalls.S11m

open Set Metric Topology Filter MeasureTheory
open scoped ENNReal

/-- The chain `ℕ → ℂ` with vertices `w 0, …, w n`, padded by `x` beyond `n` (the padding is never used by the chain
conditions, which only look at indices `≤ n`). -/
def chainOfFin (x : ℂ) (n : ℕ) (w : Fin (n + 1) → ℂ) : ℕ → ℂ :=
  fun i => if h : i < n + 1 then w ⟨i, h⟩ else x

theorem chainOfFin_apply_of_le {x : ℂ} {n : ℕ} {w : Fin (n + 1) → ℂ} {i : ℕ} (hi : i ≤ n) :
    chainOfFin x n w i = w ⟨i, Nat.lt_succ_of_le hi⟩ := by
  simp [chainOfFin, Nat.lt_succ_of_le hi]

/-- Reindexing: the infimum over all `ℕ`-indexed admissible chains of length `n` equals the infimum over the chains
`chainOfFin` with vertices in the countable set `S ∪ {x, y}`. -/
theorem chainCost_iInf_eq_fin (S : Set ℂ) (D : ℂ → ℂ → ℝ) (Q : Set ℂ) (x y : ℂ) (n : ℕ) :
    (⨅ (v : ℕ → ℂ) (_ : AdmissibleChain S D Q x y n v),
        ∑ i ∈ Finset.range n, ENNReal.ofReal (D (v i) (v (i + 1))))
      = ⨅ (w : Fin (n + 1) → ↥(S ∪ {x, y})) (_ : AdmissibleChain S D Q x y n
            (chainOfFin x n (fun k => (w k : ℂ)))),
          ∑ i ∈ Finset.range n,
            ENNReal.ofReal (D (chainOfFin x n (fun k => (w k : ℂ)) i)
              (chainOfFin x n (fun k => (w k : ℂ)) (i + 1))) := by
  apply le_antisymm
  · refine le_iInf fun w => le_iInf fun hw => ?_
    exact iInf₂_le (chainOfFin x n fun k => (w k : ℂ)) hw
  · refine le_iInf fun v => le_iInf fun hv => ?_
    obtain ⟨h0, hn, hmem, hperm⟩ := hv
    let w : Fin (n + 1) → ↥(S ∪ {x, y}) := fun k => ⟨v k.1, hmem k.1 (Nat.le_of_lt_succ k.isLt)⟩
    have hext : ∀ i ≤ n, chainOfFin x n (fun k => (w k : ℂ)) i = v i := by
      intro i hi
      rw [chainOfFin_apply_of_le hi]
    have hadm : AdmissibleChain S D Q x y n (chainOfFin x n fun k => (w k : ℂ)) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hext 0 (Nat.zero_le _), h0]
      · rw [hext n le_rfl, hn]
      · intro i hi
        rw [hext i hi]
        exact hmem i hi
      · intro i hi
        rw [hext i hi.le, hext (i + 1) hi]
        exact hperm i hi
    have hcost : ∑ i ∈ Finset.range n,
          ENNReal.ofReal (D (chainOfFin x n (fun k => (w k : ℂ)) i)
            (chainOfFin x n (fun k => (w k : ℂ)) (i + 1)))
        = ∑ i ∈ Finset.range n, ENNReal.ofReal (D (v i) (v (i + 1))) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i < n := Finset.mem_range.mp hi
      rw [hext i hi'.le, hext (i + 1) hi']
    exact iInf_le_of_le w (iInf_le_of_le hadm (le_of_eq hcost))

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The clearance of a fixed point `a` to a countable set `Q` is measurable, once each `ω ↦ D ω a q` is. -/
theorem measurable_clearance {D : Ω → ℂ → ℂ → ℝ} {Q : Set ℂ} (hQc : Q.Countable) {a : ℂ}
    (hm : ∀ q ∈ Q, Measurable fun ω => D ω a q) :
    Measurable fun ω => clearance (D ω) Q a := by
  have : Countable Q := hQc.to_subtype
  have hfun : (fun ω => clearance (D ω) Q a) = fun ω => ⨅ q : Q, ENNReal.ofReal (D ω a q) := by
    funext ω
    unfold clearance
    rw [iInf_subtype']
  rw [hfun]
  exact Measurable.iInf fun q : Q => ENNReal.measurable_ofReal.comp (hm q q.2)

/-- The permitted-edge relation between two points of `S ∪ Q ∪ {x, y}` is a measurable event in `ω`. -/
theorem measurableSet_permittedEdge {D : Ω → ℂ → ℂ → ℝ} {Q : Set ℂ} (hQc : Q.Countable) {T : Set ℂ}
    (hDm : ∀ a ∈ T, ∀ b ∈ T, Measurable fun ω => D ω a b) (hQT : Q ⊆ T) {a b : ℂ} (ha : a ∈ T) (hb : b ∈ T) :
    MeasurableSet {ω | PermittedEdge (D ω) Q a b} := by
  have h1 : Measurable fun ω => 4 * ENNReal.ofReal (D ω a b) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp (hDm a ha b hb))
  have h2 : Measurable fun ω => min (clearance (D ω) Q a) (clearance (D ω) Q b) :=
    (measurable_clearance hQc fun q hq => hDm a ha q (hQT hq)).min
      (measurable_clearance hQc fun q hq => hDm b hb q (hQT hq))
  exact measurableSet_lt h1 h2

/-- The admissibility of a fixed `ℕ`-indexed chain whose vertices lie in `T` is a measurable event in `ω`. -/
theorem measurableSet_admissible {D : Ω → ℂ → ℂ → ℝ} {S Q : Set ℂ} {x y : ℂ} (hQc : Q.Countable)
    {T : Set ℂ} (hDm : ∀ a ∈ T, ∀ b ∈ T, Measurable fun ω => D ω a b) (hQT : Q ⊆ T)
    {n : ℕ} {v : ℕ → ℂ} (hvT : ∀ i, v i ∈ T) :
    MeasurableSet {ω | AdmissibleChain S (D ω) Q x y n v} := by
  have hperm : MeasurableSet {ω | ∀ i < n, PermittedEdge (D ω) Q (v i) (v (i + 1))} := by
    have hi_set : ∀ i : ℕ, MeasurableSet {ω | i < n → PermittedEdge (D ω) Q (v i) (v (i + 1))} := by
      intro i
      by_cases hi : i < n
      · simp only [hi, true_implies]
        exact measurableSet_permittedEdge hQc hDm hQT (hvT i) (hvT (i + 1))
      · simp only [hi, false_implies]
        exact MeasurableSet.univ
    have heq : {ω | ∀ i < n, PermittedEdge (D ω) Q (v i) (v (i + 1))}
        = ⋂ i : ℕ, {ω | i < n → PermittedEdge (D ω) Q (v i) (v (i + 1))} := by
      ext ω
      simp
    rw [heq]
    exact MeasurableSet.iInter hi_set
  have hfix : {ω | AdmissibleChain S (D ω) Q x y n v}
      = {_ω : Ω | v 0 = x} ∩ ({_ω : Ω | v n = y} ∩ ({_ω : Ω | ∀ i ≤ n, v i ∈ S ∪ {x, y}} ∩
          {ω | ∀ i < n, PermittedEdge (D ω) Q (v i) (v (i + 1))})) := by
    ext ω
    exact Iff.rfl
  rw [hfix]
  exact MeasurableSet.inter (MeasurableSet.const _)
    (MeasurableSet.inter (MeasurableSet.const _)
      (MeasurableSet.inter (MeasurableSet.const _) hperm))

/-- The infimum over the chains of length `n` with a fixed vertex sequence `v` (in `T`) is measurable in `ω`. -/
theorem measurable_chainTerm {D : Ω → ℂ → ℂ → ℝ} {S Q : Set ℂ} {x y : ℂ} (hQc : Q.Countable)
    {T : Set ℂ} (hDm : ∀ a ∈ T, ∀ b ∈ T, Measurable fun ω => D ω a b) (hQT : Q ⊆ T)
    {n : ℕ} {v : ℕ → ℂ} (hvT : ∀ i, v i ∈ T) :
    Measurable fun ω => ⨅ (_ : AdmissibleChain S (D ω) Q x y n v),
      ∑ i ∈ Finset.range n, ENNReal.ofReal (D ω (v i) (v (i + 1))) := by
  classical
  have hset := measurableSet_admissible (S := S) (x := x) (y := y) hQc hDm hQT hvT (n := n)
  have hfun : (fun ω => ⨅ (_ : AdmissibleChain S (D ω) Q x y n v),
        ∑ i ∈ Finset.range n, ENNReal.ofReal (D ω (v i) (v (i + 1))))
      = {ω | AdmissibleChain S (D ω) Q x y n v}.piecewise
          (fun ω => ∑ i ∈ Finset.range n, ENNReal.ofReal (D ω (v i) (v (i + 1)))) (fun _ => ⊤) := by
    funext ω
    by_cases h : AdmissibleChain S (D ω) Q x y n v
    · simp [Set.piecewise, h]
    · simp [Set.piecewise, h]
  rw [hfun]
  refine Measurable.piecewise hset ?_ measurable_const
  exact Finset.measurable_sum _ fun i _ =>
    ENNReal.measurable_ofReal.comp (hDm _ (hvT i) _ (hvT (i + 1)))

/-- The chain formula is a measurable function of the metric, given the countably many evaluations
`ω ↦ D ω a b` with `a, b ∈ S ∪ Q ∪ {x, y}` (route Step 3.4, "its Borelness"). No length-metric property of `D ω`
is used. -/
theorem measurable_chainDistance {D : Ω → ℂ → ℂ → ℝ} {S Q : Set ℂ} (hS : S.Countable) (hQc : Q.Countable)
    {x y : ℂ} (hDm : ∀ a ∈ S ∪ Q ∪ {x, y}, ∀ b ∈ S ∪ Q ∪ {x, y}, Measurable fun ω => D ω a b) :
    Measurable fun ω => chainDistance S (D ω) Q x y := by
  have hcount : Countable ↥(S ∪ {x, y}) :=
    ((hS.union (Set.toFinite ({x, y} : Set ℂ)).countable)).to_subtype
  have hST : S ⊆ S ∪ Q ∪ {x, y} := fun z hz => Or.inl (Or.inl hz)
  have hQT : Q ⊆ S ∪ Q ∪ {x, y} := fun z hz => Or.inl (Or.inr hz)
  have hxyT : ({x, y} : Set ℂ) ⊆ S ∪ Q ∪ {x, y} := fun z hz => Or.inr hz
  have hSxy : S ∪ {x, y} ⊆ S ∪ Q ∪ {x, y} := by
    rintro z (hz | hz)
    · exact hST hz
    · exact hxyT hz
  have hreidx : ∀ ω, chainDistance S (D ω) Q x y = ⨅ n : ℕ,
      ⨅ (w : Fin (n + 1) → ↥(S ∪ {x, y})) (_ : AdmissibleChain S (D ω) Q x y n
            (chainOfFin x n (fun k => (w k : ℂ)))),
          ∑ i ∈ Finset.range n,
            ENNReal.ofReal (D ω (chainOfFin x n (fun k => (w k : ℂ)) i)
              (chainOfFin x n (fun k => (w k : ℂ)) (i + 1))) := fun ω => by
    unfold chainDistance
    exact iInf_congr fun n => chainCost_iInf_eq_fin S (D ω) Q x y n
  have hfun : (fun ω => chainDistance S (D ω) Q x y) = fun ω => ⨅ n : ℕ,
      ⨅ (w : Fin (n + 1) → ↥(S ∪ {x, y})) (_ : AdmissibleChain S (D ω) Q x y n
            (chainOfFin x n (fun k => (w k : ℂ)))),
          ∑ i ∈ Finset.range n,
            ENNReal.ofReal (D ω (chainOfFin x n (fun k => (w k : ℂ)) i)
              (chainOfFin x n (fun k => (w k : ℂ)) (i + 1))) := funext hreidx
  rw [hfun]
  refine Measurable.iInf fun n => Measurable.iInf fun w => ?_
  refine measurable_chainTerm hQc hDm hQT (n := n) fun i => ?_
  unfold chainOfFin
  split_ifs with h
  · exact hSxy (w ⟨i, h⟩).2
  · exact hxyT (by simp)

end HarmonicBalls.S11m

#print axioms HarmonicBalls.S11m.measurable_chainDistance
