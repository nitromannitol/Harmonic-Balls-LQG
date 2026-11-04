import HarmonicBalls.Steps.Sec11.PinchBlockMeasurable
import Mathlib.MeasureTheory.Measure.Trim

/-! # Local absolute continuity for pinch-scale density

Only sufficiently small scales occur in the eventual block-density event.
This permits comparison on a local sigma algebra rather than on the full
sample-space sigma algebra.
-/

namespace HarmonicBalls

open Set Filter MeasureTheory

open Classical in
/-- A common locally measurable tail representative transfers an eventual
block-density estimate under absolute continuity on the local sigma algebra. -/
theorem ae_eventually_block_density_of_local_absolutelyContinuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P Q : Measure Ω)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (K : ℕ) (X : ℕ → Ω → ℝ) (E : ℕ → Ω → Prop) (q : ℝ)
    (hX : ∀ n, K ≤ n → Measurable[m] (X n))
    (hrepP : ∀ᵐ ω ∂P, ∀ n, K ≤ n → X n ω = if E n ω then 1 else 0)
    (hrepQ : ∀ᵐ ω ∂Q, ∀ n, K ≤ n → X n ω = if E n ω then 1 else 0)
    (hac : P.trim hm ≪ Q.trim hm)
    (hfixed : ∀ᵐ ω ∂Q, ∀ᶠ N : ℕ in atTop, q * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ E n ω}.ncard : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, q * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ E n ω}.ncard : ℝ) := by
  let A : Set Ω := {ω | ∀ᶠ N : ℕ in atTop, q * N ≤
    ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ (K ≤ n ∧ X n ω = 1)}.ncard : ℝ)}
  have hA : MeasurableSet[m] A := by
    let : MeasurableSpace Ω := m
    apply measurableSet_eventually_blockEvent_ncard
    intro n
    by_cases hn : K ≤ n
    · simp only [hn, true_and]
      change MeasurableSet (X n ⁻¹' ({1} : Set ℝ))
      exact (measurableSet_singleton (1 : ℝ)).preimage (hX n hn)
    · simpa only [hn, false_and, ofPred_false] using (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))
  have hequiv (ω : Ω) (hω : ∀ n, K ≤ n → X n ω = if E n ω then 1 else 0) :
      (ω ∈ A ↔ ∀ᶠ N : ℕ in atTop, q * N ≤
        ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ E n ω}.ncard : ℝ)) := by
    have hx (n : ℕ) (hn : K ≤ n) : X n ω = 1 ↔ E n ω := by
      rw [hω n hn]
      split_ifs <;> simp_all
    have hsets (N : ℕ) (hN : K ≤ N) :
        {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ (K ≤ n ∧ X n ω = 1)} =
        {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ E n ω} := by
      ext n
      simp only [mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2, hk, h3⟩
        exact ⟨h1, h2, (hx n hk).1 h3⟩
      · rintro ⟨h1, h2, h3⟩
        have hk : K ≤ n := le_trans hN (le_trans (Nat.le_succ N) h1)
        exact ⟨h1, h2, hk, (hx n hk).2 h3⟩
    change (∀ᶠ N : ℕ in atTop, q * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ (K ≤ n ∧ X n ω = 1)}.ncard : ℝ)) ↔ _
    apply Filter.eventually_congr
    filter_upwards [eventually_ge_atTop K] with N hN
    rw [hsets N hN]
  have hQA : ∀ᵐ ω ∂Q, ω ∈ A := by
    filter_upwards [hrepQ, hfixed] with ω hrep hω
    exact (hequiv ω hrep).2 hω
  have hQtrim : ∀ᵐ ω ∂(Q.trim hm), ω ∈ A := by
    rw [ae_iff] at hQA ⊢
    change Q Aᶜ = 0 at hQA
    change (Q.trim hm) Aᶜ = 0
    rwa [trim_measurableSet_eq hm hA.compl]
  have hPA : ∀ᵐ ω ∂P, ω ∈ A := MeasureTheory.ae_of_ae_trim hm (hac.ae_le hQtrim)
  filter_upwards [hrepP, hPA] with ω hrep hω
  exact (hequiv ω hrep).1 hω

#print axioms ae_eventually_block_density_of_local_absolutelyContinuous

end HarmonicBalls
