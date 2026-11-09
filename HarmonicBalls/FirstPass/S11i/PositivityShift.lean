import Mathlib

/-!
# Positivity by scaled shifts (Lemma 11.12 replacement, Theorem 2, unconditional positivity)

Generic measure step of `notes/fp-gaps/G-11-12.md`, section 3, "Proof of unconditional positivity": "Its shift law is
equivalent to the original law. Since the events `{e^{γk} μ(S₀) > 8c}`, `k ∈ ℕ`, exhaust a full-measure event,
equivalence proves `p = P{μ(S₀) > 8c} > 0`."

Abstractly: let `X` be a measurable real functional that is almost surely positive, and let `T k` be maps with
`P.map (T k) ≪ P` (shift laws absolutely continuous to the original law) under which `X` is scaled by `exp (γ k)` almost
surely. Then `P {t < X} > 0` for every `t`. The shift and scaling inputs are EXTERNAL and enter as hypotheses here.
-/

open MeasureTheory Filter Topology Set

namespace FirstPassS11i

theorem exists_pos_of_scaled_shift {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Measurable X) (hpos : ∀ᵐ ω ∂P, 0 < X ω) {γ : ℝ} (hγ : 0 < γ)
    (T : ℕ → Ω → Ω) (hT : ∀ k, Measurable (T k)) (hac : ∀ k, P.map (T k) ≪ P)
    (hscale : ∀ k : ℕ, ∀ᵐ ω ∂P, X (T k ω) = X ω * Real.exp (γ * (k : ℝ))) (t : ℝ) :
    0 < P {ω | t < X ω} := by
  set E : ℕ → Set Ω := fun k => {ω | t < X ω * Real.exp (γ * (k : ℝ))} with hEdef
  -- the scaled events exhaust a set of full measure
  have hfull : ∀ᵐ ω ∂P, ω ∈ ⋃ k, E k := by
    filter_upwards [hpos] with ω hω
    have hexp : Tendsto (fun k : ℕ => Real.exp (γ * (k : ℝ))) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hγ)
    have hlim : Tendsto (fun k : ℕ => X ω * Real.exp (γ * (k : ℝ))) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hω hexp
    obtain ⟨k, hk⟩ := (hlim.eventually_gt_atTop t).exists
    exact mem_iUnion.2 ⟨k, hk⟩
  -- some scaled event has positive probability
  have hk : ∃ k, 0 < P (E k) := by
    by_contra hcon
    simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
    have hU : P (⋃ k, E k) = 0 := measure_iUnion_null fun k => hcon k
    have hae : ∀ᵐ ω ∂P, ω ∉ ⋃ k, E k := by
      refine ae_iff.2 ?_
      have hset : {ω | ¬ ω ∉ ⋃ k, E k} = ⋃ k, E k := by
        ext ω
        simp
      rw [hset]
      exact hU
    obtain ⟨ω, h1, h2⟩ := (hfull.and hae).exists
    exact h2 h1
  obtain ⟨k, hkpos⟩ := hk
  -- transfer the positivity through the shift
  have hS : MeasurableSet {ω | t < X ω} := measurableSet_lt measurable_const hX
  by_contra hcon
  have hS0 : P {ω | t < X ω} = 0 := nonpos_iff_eq_zero.1 (not_lt.1 hcon)
  have hmap : P.map (T k) {ω | t < X ω} = 0 := hac k hS0
  rw [Measure.map_apply (hT k) hS] at hmap
  have hnull : P {ω | ¬ X (T k ω) = X ω * Real.exp (γ * (k : ℝ))} = 0 := ae_iff.1 (hscale k)
  have hsub : E k ⊆ T k ⁻¹' {ω | t < X ω} ∪ {ω | ¬ X (T k ω) = X ω * Real.exp (γ * (k : ℝ))} := by
    intro ω hω
    by_cases h : X (T k ω) = X ω * Real.exp (γ * (k : ℝ))
    · left
      show t < X (T k ω)
      rw [h]
      exact hω
    · right
      exact h
  have hle : P (E k) ≤ 0 := by
    calc P (E k)
        ≤ P (T k ⁻¹' {ω | t < X ω} ∪ {ω | ¬ X (T k ω) = X ω * Real.exp (γ * (k : ℝ))}) := measure_mono hsub
      _ ≤ P (T k ⁻¹' {ω | t < X ω}) + P {ω | ¬ X (T k ω) = X ω * Real.exp (γ * (k : ℝ))} := measure_union_le _ _
      _ = 0 := by rw [hmap, hnull, add_zero]
  exact absurd hkpos (not_lt.2 hle)

end FirstPassS11i
