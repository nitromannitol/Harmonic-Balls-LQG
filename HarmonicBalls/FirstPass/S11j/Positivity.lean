import Mathlib

/-!
# First pass, Section 11: deterministic thresholds of positive probability (fp-S11j, owner n4)

Pure measure theory used by the faithful Lemma 11.15 (corrected paper, local event `E₁`, lines 3659-3696: "Choose
deterministic `c₁,…,c₄ > 0` so that `F = {L ≥ c₁, A ≤ c₂, D(0,∂B_{δ/2}) ≥ c₃, d₀ ≤ c₄}` has positive probability.
This is possible since the variables are positive and finite"). The paper's sentence is made precise here: for
`[0,∞]`-valued measurable random variables `X₁, X₃` with `0 < X` almost surely and `X₂, X₄` with `X < ∞` almost
surely, there are natural-number thresholds `n, k, m, l` (the Lean forms of `1/n`, `1/k`, `m`, `l`) with
`P[1/n ≤ X₁, X₂ ≤ m, 1/k ≤ X₃, X₄ ≤ l] > 0`.

Terminology: Armitage-Gardiner style "positive probability of a sublevel/superlevel set"; the proof is continuity of
measure along monotone sequences of events (Billingsley, *Probability and Measure*, Theorem 2.1).
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Lower threshold. If `X > 0` almost surely, then for every `ε > 0` some `n ≥ 1` satisfies
`P[X < 1/n] < ε`. -/
theorem measure_lt_inv_nat_lt_of_pos {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞}
    (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 < X ω) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ P {ω | X ω < (n : ℝ≥0∞)⁻¹} < ε := by
  set s : ℕ → Set Ω := fun n => {ω | X ω < (n : ℝ≥0∞)⁻¹} with hs_def
  have hs_meas : ∀ n, NullMeasurableSet (s n) P := fun n =>
    (measurableSet_lt hX measurable_const).nullMeasurableSet
  have hs_anti : Antitone s := by
    intro m n hmn ω hω
    have h1 : X ω < (n : ℝ≥0∞)⁻¹ := hω
    show X ω < (m : ℝ≥0∞)⁻¹
    exact lt_of_lt_of_le h1 (ENNReal.inv_le_inv.2 (Nat.cast_le.2 hmn))
  have hsub : (⋂ n, s n) ⊆ {ω | ¬ 0 < X ω} := by
    intro ω hω hpos0
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hpos0.ne'
    have h1 : X ω < (n : ℝ≥0∞)⁻¹ := mem_iInter.1 hω n
    exact lt_asymm h1 hn
  have hnull : P (⋂ n, s n) = 0 := measure_mono_null hsub (ae_iff.1 hpos)
  have hT : Tendsto (P ∘ s) atTop (𝓝 (P (⋂ n, s n))) :=
    tendsto_measure_iInter_atTop hs_meas hs_anti ⟨0, measure_ne_top P _⟩
  rw [hnull] at hT
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hT).2 ε hε)
  exact ⟨N + 1, Nat.succ_pos N, hN (N + 1) (Nat.le_succ N)⟩

/-- Upper threshold. If `X < ∞` almost surely, then for every `ε > 0` some `m : ℕ` satisfies `P[m < X] < ε`. -/
theorem measure_nat_lt_lt_of_lt_top {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ≥0∞}
    (hX : Measurable X) (hfin : ∀ᵐ ω ∂P, X ω < ∞) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ m : ℕ, P {ω | (m : ℝ≥0∞) < X ω} < ε := by
  set s : ℕ → Set Ω := fun m => {ω | (m : ℝ≥0∞) < X ω} with hs_def
  have hs_meas : ∀ m, NullMeasurableSet (s m) P := fun m =>
    (measurableSet_lt measurable_const hX).nullMeasurableSet
  have hs_anti : Antitone s := by
    intro m n hmn ω hω
    have h1 : (n : ℝ≥0∞) < X ω := hω
    show (m : ℝ≥0∞) < X ω
    exact lt_of_le_of_lt (Nat.cast_le.2 hmn) h1
  have hsub : (⋂ m, s m) ⊆ {ω | ¬ X ω < ∞} := by
    intro ω hω hfin0
    obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hfin0.ne
    have h1 : (m : ℝ≥0∞) < X ω := mem_iInter.1 hω m
    exact lt_asymm h1 hm
  have hnull : P (⋂ m, s m) = 0 := measure_mono_null hsub (ae_iff.1 hfin)
  have hT : Tendsto (P ∘ s) atTop (𝓝 (P (⋂ m, s m))) :=
    tendsto_measure_iInter_atTop hs_meas hs_anti ⟨0, measure_ne_top P _⟩
  rw [hnull] at hT
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hT).2 ε hε)
  exact ⟨N, hN N le_rfl⟩

/-- Positive probability of the four-fold threshold event. Let `X₁, X₃` be almost surely positive and `X₂, X₄`
almost surely finite. Then there are natural numbers `n, k, m, l` with `n, k ≥ 1` such that
`P[1/n ≤ X₁, X₂ ≤ m, 1/k ≤ X₃, X₄ ≤ l] > 0`. -/
theorem exists_thresholds_measure_pos {P : Measure Ω} [IsProbabilityMeasure P] {X₁ X₂ X₃ X₄ : Ω → ℝ≥0∞}
    (h₁ : Measurable X₁) (h₂ : Measurable X₂) (h₃ : Measurable X₃) (h₄ : Measurable X₄)
    (p₁ : ∀ᵐ ω ∂P, 0 < X₁ ω) (p₂ : ∀ᵐ ω ∂P, X₂ ω < ∞)
    (p₃ : ∀ᵐ ω ∂P, 0 < X₃ ω) (p₄ : ∀ᵐ ω ∂P, X₄ ω < ∞) :
    ∃ n k m l : ℕ, 0 < n ∧ 0 < k ∧
      0 < P {ω | (n : ℝ≥0∞)⁻¹ ≤ X₁ ω ∧ X₂ ω ≤ (m : ℝ≥0∞) ∧
        (k : ℝ≥0∞)⁻¹ ≤ X₃ ω ∧ X₄ ω ≤ (l : ℝ≥0∞)} := by
  have hε : (0 : ℝ≥0∞) < 4⁻¹ := ENNReal.inv_pos.2 (by simp)
  obtain ⟨n, hn, hB1⟩ := measure_lt_inv_nat_lt_of_pos h₁ p₁ hε
  obtain ⟨m, hB2⟩ := measure_nat_lt_lt_of_lt_top h₂ p₂ hε
  obtain ⟨k, hk, hB3⟩ := measure_lt_inv_nat_lt_of_pos h₃ p₃ hε
  obtain ⟨l, hB4⟩ := measure_nat_lt_lt_of_lt_top h₄ p₄ hε
  refine ⟨n, k, m, l, hn, hk, ?_⟩
  set F : Set Ω := {ω | (n : ℝ≥0∞)⁻¹ ≤ X₁ ω ∧ X₂ ω ≤ (m : ℝ≥0∞) ∧
        (k : ℝ≥0∞)⁻¹ ≤ X₃ ω ∧ X₄ ω ≤ (l : ℝ≥0∞)} with hF_def
  set B1 : Set Ω := {ω | X₁ ω < (n : ℝ≥0∞)⁻¹} with hB1_def
  set B2 : Set Ω := {ω | (m : ℝ≥0∞) < X₂ ω} with hB2_def
  set B3 : Set Ω := {ω | X₃ ω < (k : ℝ≥0∞)⁻¹} with hB3_def
  set B4 : Set Ω := {ω | (l : ℝ≥0∞) < X₄ ω} with hB4_def
  have hcov : (univ : Set Ω) ⊆ F ∪ B1 ∪ B2 ∪ B3 ∪ B4 := by
    intro ω _
    simp only [mem_union, mem_ofPred_eq, hF_def, hB1_def, hB2_def, hB3_def, hB4_def]
    rcases le_or_gt ((n : ℝ≥0∞)⁻¹) (X₁ ω) with h1 | h1
    · rcases le_or_gt (X₂ ω) (m : ℝ≥0∞) with h2 | h2
      · rcases le_or_gt ((k : ℝ≥0∞)⁻¹) (X₃ ω) with h3 | h3
        · rcases le_or_gt (X₄ ω) (l : ℝ≥0∞) with h4 | h4
          · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨h1, h2, h3, h4⟩)))
          · exact Or.inr h4
        · exact Or.inl (Or.inr h3)
      · exact Or.inl (Or.inl (Or.inr h2))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h1)))
  by_contra hF
  have hF0 : P F = 0 := nonpos_iff_eq_zero.1 (not_lt.1 hF)
  have e1 := measure_union_le (μ := P) (F ∪ B1 ∪ B2 ∪ B3) B4
  have e2 := measure_union_le (μ := P) (F ∪ B1 ∪ B2) B3
  have e3 := measure_union_le (μ := P) (F ∪ B1) B2
  have e4 := measure_union_le (μ := P) F B1
  have htot : P (univ : Set Ω) ≤ P (F ∪ B1 ∪ B2 ∪ B3 ∪ B4) := measure_mono hcov
  have hlt : P F + P B1 + P B2 + P B3 + P B4 < 1 := by
    rw [hF0, zero_add]
    calc P B1 + P B2 + P B3 + P B4 < 4⁻¹ + 4⁻¹ + 4⁻¹ + 4⁻¹ := by
          exact ENNReal.add_lt_add (ENNReal.add_lt_add (ENNReal.add_lt_add hB1 hB2) hB3) hB4
      _ = 4 * 4⁻¹ := by ring
      _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have : (1 : ℝ≥0∞) ≤ P F + P B1 + P B2 + P B3 + P B4 := by
    rw [measure_univ] at htot
    calc (1 : ℝ≥0∞) ≤ P (F ∪ B1 ∪ B2 ∪ B3 ∪ B4) := htot
      _ ≤ P (F ∪ B1 ∪ B2 ∪ B3) + P B4 := e1
      _ ≤ (P (F ∪ B1 ∪ B2) + P B3) + P B4 := add_le_add e2 le_rfl
      _ ≤ ((P (F ∪ B1) + P B2) + P B3) + P B4 := add_le_add (add_le_add e3 le_rfl) le_rfl
      _ ≤ (((P F + P B1) + P B2) + P B3) + P B4 :=
          add_le_add (add_le_add (add_le_add e4 le_rfl) le_rfl) le_rfl
      _ = P F + P B1 + P B2 + P B3 + P B4 := by ring
  exact absurd hlt (not_lt.2 this)

#print axioms measure_lt_inv_nat_lt_of_pos
#print axioms measure_nat_lt_lt_of_lt_top
#print axioms exists_thresholds_measure_pos

end HarmonicBalls
