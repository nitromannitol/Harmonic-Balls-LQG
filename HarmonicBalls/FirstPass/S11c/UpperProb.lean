import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Proposition 11.10, an almost surely finite random bound with large probability

If a measurable random variable `X ≥ 0` is almost surely finite, then for every `η > 0`
some integer `n` has `P(X ≤ n) ≥ 1 - η`. This is the step that turns the almost-sure finiteness of the diameter of the
exterior set `K₁` (`ConnectedSquareUnionDiamFiniteFrozen`, DDDF20 Lemma 3.9) into a deterministic bound `a` holding with
probability close to one, as needed for the exterior bound of the paper's proof (corrected lines 3079-3088, `eqn-exterior-diam`).
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set
open scoped ENNReal

theorem exists_nat_bound_prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ≥0∞} (hX : Measurable X) (hfin : ∀ᵐ ω ∂P, X ω < ⊤) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ n : ℕ, 1 - η < P {ω | X ω ≤ (n : ℝ≥0∞)} := by
  set A : ℕ → Set Ω := fun n => {ω | X ω ≤ (n : ℝ≥0∞)} with hA
  have hmono : Monotone A := by
    intro n m hnm ω hω
    simp only [hA, Set.mem_ofPred_eq] at hω ⊢
    exact le_trans hω (by exact_mod_cast Nat.cast_le.2 hnm)
  have hunion : ⋃ n, A n = {ω | X ω < ⊤} := by
    ext ω
    simp only [hA, mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      exact lt_of_le_of_lt hn (ENNReal.natCast_lt_top n)
    · intro h
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h.ne
      exact ⟨n, hn.le⟩
  have hmeas : MeasurableSet {ω | X ω < ⊤} := measurableSet_lt hX measurable_const
  have hfull : P (⋃ n, A n) = 1 := by
    rw [hunion]
    exact (prob_compl_eq_zero_iff hmeas).1 (ae_iff.1 hfin)
  have htend := tendsto_measure_iUnion_atTop (μ := P) hmono
  rw [hfull] at htend
  have hlt : 1 - η < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hη.ne'
  obtain ⟨n, hn⟩ := (htend.eventually (lt_mem_nhds hlt)).exists
  exact ⟨n, hn⟩

end HarmonicBalls
