import Mathlib
import HarmonicBalls.FirstPass.S11ah.LengthBorelClauses

/-!
# The corrected countable length code (B1 of the Borel code, owner n3)

Ruling chat 236, section 3. For `B = ball c r` and a dense sequence `q : ℕ → ↥B`, a *fine chain* of a
decoder `d` from the `q`-point `q a` to the `q`-point `q b`, inside the compact level `expK c r j`, is a
finite sequence of `q`-points whose consecutive decoder distances are at most `1/(n+1)` (mesh) and whose
decoder sum is at most `D(q a, q b) + 1/(k+1)` (sum). The length code `lengthCodeSet` asks, for all levels
`i, k`, the existence of a level `j ≥ i` such that every pair of endpoints in `expK i` has such chains for
all mesh scales `n`. The quantifiers are countable and the conditions on `d` are closed, so the code is Borel.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
noncomputable section

namespace HarmonicBalls.FirstPassS11ahLengthChainCode

open HarmonicBalls.FirstPassS11ahLengthBorelClauses FirstPassS11ah HarmonicBalls

/-- A fine chain of the decoder `d` on `ball c r` from `q a` to `q b`, through `q`-points in `expK c r j`,
with decoder mesh `≤ 1/(n+1)` and decoder sum `≤ D(q a, q b) + 1/(k+1)`. A chain is a finite sequence
of indices `w 0 = a, …, w N = b` (countable data). -/
def GoodChain (c : ℂ) (r : ℝ) (q : ℕ → ↥(ball c r)) (d : C(Win (ball c r), ℝ))
    (j k n a b : ℕ) : Prop :=
  ∃ N : ℕ, ∃ w : Fin (N + 1) → ℕ,
    w 0 = a ∧ w (Fin.last N) = b ∧ (∀ t, (q (w t) : ℂ) ∈ expK c r j) ∧
    (∀ t : Fin N, decoderOn (ball c r) d (q (w t.castSucc)) (q (w t.succ)) ≤ 1 / ((n : ℝ) + 1)) ∧
    ∑ t : Fin N, decoderOn (ball c r) d (q (w t.castSucc)) (q (w t.succ)) ≤
      decoderOn (ball c r) d (q a) (q b) + 1 / ((k : ℝ) + 1)

/-- The corrected countable length code (ruling 236, section 3): for all levels `i, k` some level
`j ≥ i` carries fine chains between all `q`-endpoints in `expK i`, for all mesh scales `n`. -/
def lengthCodeSet (c : ℂ) (r : ℝ) (q : ℕ → ↥(ball c r)) : Set C(Win (ball c r), ℝ) :=
  {d | ∀ i k : ℕ, ∃ j : ℕ, i ≤ j ∧ ∀ n a b : ℕ,
      (q a : ℂ) ∈ expK c r i → (q b : ℂ) ∈ expK c r i → GoodChain c r q d j k n a b}

/-! ### Borel calculus -/

/-- Evaluation of the decoder at fixed points of `B` is continuous in `d`. -/
lemma continuous_decoderOn_apply {B : Set ℂ} {x y : ℂ} (hx : x ∈ B) (hy : y ∈ B) :
    Continuous (fun d : C(Win B, ℝ) => decoderOn B d x y) := by
  have h : (fun d : C(Win B, ℝ) => decoderOn B d x y) =
      fun d => d ⟨(x, y), mk_mem_prod hx hy⟩ :=
    funext fun d => decoderOn_apply_of_mem d hx hy
  rw [h]
  exact continuous_eval_const _

/-- A static proposition intersected with a measurable set is measurable. -/
lemma measurableSet_and_mem {α : Type*} [MeasurableSpace α] (p : Prop) {F : Set α}
    (hF : MeasurableSet F) : MeasurableSet {a : α | p ∧ a ∈ F} := by
  by_cases hp : p
  · simpa [hp] using hF
  · simp [hp]

/-- A static implication `p → a ∈ F` is measurable. -/
lemma measurableSet_imp_mem {α : Type*} [MeasurableSpace α] (p : Prop) {F : Set α}
    (hF : MeasurableSet F) : MeasurableSet {a : α | p → a ∈ F} := by
  by_cases hp : p
  · simpa [hp] using hF
  · simp [hp]

/-- The chain conditions for a fixed chain shape are closed in `d`. -/
lemma isClosed_chainConds (c : ℂ) (r : ℝ) (q : ℕ → ↥(ball c r)) (n k N : ℕ)
    (w : Fin (N + 1) → ℕ) (a b : ℕ) :
    IsClosed {d : C(Win (ball c r), ℝ) |
      (∀ t : Fin N, decoderOn (ball c r) d (q (w t.castSucc)) (q (w t.succ)) ≤ 1 / ((n : ℝ) + 1)) ∧
      ∑ t : Fin N, decoderOn (ball c r) d (q (w t.castSucc)) (q (w t.succ)) ≤
        decoderOn (ball c r) d (q a) (q b) + 1 / ((k : ℝ) + 1)} := by
  have h1 : IsClosed {d : C(Win (ball c r), ℝ) |
      ∀ t : Fin N, decoderOn (ball c r) d (q (w t.castSucc)) (q (w t.succ)) ≤ 1 / ((n : ℝ) + 1)} := by
    have hEq1 : {d : C(Win (ball c r), ℝ) |
        ∀ t : Fin N, decoderOn (ball c r) d (q (w t.castSucc)) (q (w t.succ)) ≤ 1 / ((n : ℝ) + 1)} =
        ⋂ t : Fin N, {d : C(Win (ball c r), ℝ) |
          decoderOn (ball c r) d (q (w t.castSucc)) (q (w t.succ)) ≤ 1 / ((n : ℝ) + 1)} := by
      ext d
      simp
    rw [hEq1]
    exact isClosed_iInter fun t => isClosed_le
      (continuous_decoderOn_apply (q (w t.castSucc)).2 (q (w t.succ)).2) continuous_const
  have h2 : IsClosed {d : C(Win (ball c r), ℝ) |
      ∑ t : Fin N, decoderOn (ball c r) d (q (w t.castSucc)) (q (w t.succ)) ≤
        decoderOn (ball c r) d (q a) (q b) + 1 / ((k : ℝ) + 1)} :=
    isClosed_le
      (continuous_finsetSum _ fun t _ =>
        continuous_decoderOn_apply (q (w t.castSucc)).2 (q (w t.succ)).2)
      (Continuous.add (continuous_decoderOn_apply (q a).2 (q b).2) continuous_const)
  exact h1.inter h2

/-- The set of decoders having a fine chain of given parameters is Borel. -/
lemma measurableSet_goodChain (c : ℂ) (r : ℝ) (q : ℕ → ↥(ball c r)) (j k n a b : ℕ) :
    MeasurableSet {d : C(Win (ball c r), ℝ) | GoodChain c r q d j k n a b} := by
  have hEq : {d : C(Win (ball c r), ℝ) | GoodChain c r q d j k n a b} =
      ⋃ N : ℕ, ⋃ w : Fin (N + 1) → ℕ,
        {d : C(Win (ball c r), ℝ) | (w 0 = a ∧ w (Fin.last N) = b ∧
          (∀ t, (q (w t) : ℂ) ∈ expK c r j)) ∧
          ((∀ t : Fin N, decoderOn (ball c r) d (q (w t.castSucc)) (q (w t.succ)) ≤
              1 / ((n : ℝ) + 1)) ∧
            ∑ t : Fin N, decoderOn (ball c r) d (q (w t.castSucc)) (q (w t.succ)) ≤
              decoderOn (ball c r) d (q a) (q b) + 1 / ((k : ℝ) + 1))} := by
    ext d
    constructor
    · rintro ⟨N, w, h1, h2, h3, h4, h5⟩
      exact Set.mem_iUnion.2 ⟨N, Set.mem_iUnion.2 ⟨w, ⟨⟨h1, h2, h3⟩, h4, h5⟩⟩⟩
    · intro hd
      obtain ⟨N, hN⟩ := Set.mem_iUnion.1 hd
      obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hN
      obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := hw
      exact ⟨N, w, h1, h2, h3, h4, h5⟩
  rw [hEq]
  refine MeasurableSet.iUnion fun N => MeasurableSet.iUnion fun w => ?_
  exact measurableSet_and_mem _ (isClosed_chainConds c r q n k N w a b).measurableSet

/-- The length code is Borel (ruling 236, section 3: `measurableSet_lengthCodeSet`). -/
theorem measurableSet_lengthCodeSet (c : ℂ) (r : ℝ) (q : ℕ → ↥(ball c r)) :
    MeasurableSet (lengthCodeSet c r q) := by
  have hEq : lengthCodeSet c r q =
      ⋂ i : ℕ, ⋂ k : ℕ, ⋃ j : ℕ, {d : C(Win (ball c r), ℝ) | i ≤ j ∧
        d ∈ ⋂ n : ℕ, ⋂ a : ℕ, ⋂ b : ℕ,
          {d : C(Win (ball c r), ℝ) | (q a : ℂ) ∈ expK c r i → (q b : ℂ) ∈ expK c r i →
            GoodChain c r q d j k n a b}} := by
    ext d
    simp only [lengthCodeSet, mem_ofPred_eq, mem_iInter, mem_iUnion]
  rw [hEq]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun k =>
    MeasurableSet.iUnion fun j => ?_
  refine measurableSet_and_mem _ ?_
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => ?_
  exact measurableSet_imp_mem _ (measurableSet_imp_mem _ (measurableSet_goodChain c r q j k n a b))

end HarmonicBalls.FirstPassS11ahLengthChainCode
