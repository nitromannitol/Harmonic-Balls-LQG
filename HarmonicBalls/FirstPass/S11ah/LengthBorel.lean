import Mathlib

/-!
# Borel measurability of pointwise inequalities on continuous functions

Generic countable-reduction lemma for the Borel σ-algebra `ContinuousMap.measurableSpace` on `C(X, ℝ)`
(Mathlib: `ContinuousMap.measurableSpace := borel _`). It is the first step of the Borel code of
`IsLengthMetricOn B (decoderOn B d)`:
a clause `∀ p, Φ d p ≤ 0`, with `Φ d` continuous, reduces to a countable dense set of points.
-/

open MeasureTheory Set Filter Topology

namespace HarmonicBalls.FirstPassS11ahLengthBorel

/-- **Countable reduction of a continuous pointwise inequality.** If `Φ d` is continuous for every `d`, and the
evaluation `d ↦ Φ d q` is measurable for each point `q` of a countable dense set `Q`, then the set of `d` with
`Φ d p ≤ 0` for all `p` is measurable. The proof: `{p | Φ d p ≤ 0}` is closed, so it contains all of `X` as soon as
it contains the dense set `Q`. -/
theorem measurableSet_forall_nonpos_of_dense {X : Type*} [TopologicalSpace X] {Q : Set X} (hQc : Q.Countable)
    (hQd : Dense Q) {Φ : C(X, ℝ) → X → ℝ} (hΦc : ∀ d, Continuous (Φ d))
    (hΦm : ∀ q ∈ Q, Measurable fun d : C(X, ℝ) => Φ d q) :
    MeasurableSet {d : C(X, ℝ) | ∀ p, Φ d p ≤ 0} := by
  have hEq : {d : C(X, ℝ) | ∀ p, Φ d p ≤ 0} = ⋂ q ∈ Q, {d : C(X, ℝ) | Φ d q ≤ 0} := by
    ext d
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro h q _
      exact h q
    · intro h p
      have hsub : Q ⊆ {p | Φ d p ≤ 0} := fun q hq => h q hq
      have hcl : closure Q ⊆ {p | Φ d p ≤ 0} :=
        closure_minimal hsub (isClosed_le (hΦc d) continuous_const)
      have hp : p ∈ closure Q := by
        rw [hQd.closure_eq]
        exact mem_univ p
      exact hcl hp
  rw [hEq]
  exact MeasurableSet.biInter hQc fun q hq => measurableSet_le (hΦm q hq) measurable_const

/-- **Evaluation is measurable** in the Borel σ-algebra of `C(X, ℝ)`. -/
theorem measurable_eval_real {X : Type*} [TopologicalSpace X] (p : X) :
    Measurable fun d : C(X, ℝ) => d p :=
  ContinuousMap.measurable_eval p

end HarmonicBalls.FirstPassS11ahLengthBorel

#print axioms HarmonicBalls.FirstPassS11ahLengthBorel.measurableSet_forall_nonpos_of_dense
