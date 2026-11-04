import HarmonicBalls.Draft.Section6
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6

/-!
# Annulus iteration for a distribution-valued GFF

Leonardo Bonanno proved Gwynne–Miller's annulus iteration lemma in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. This file converts its indexing to the
zero-based convention used in Section 6. The law transfer from the pairing-valued GFF remains
separate.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HarmonicBalls.Section6


/-- A deterministic logarithmic shift leaves the local field modulo constants unchanged. -/
theorem fieldSigmaAlgebraModConst_eq {Ω : Type*} (α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) :
    fieldSigmaAlgebraModConst α₀ hC U = fieldSigmaAlgebraModConst 0 hC U := by
  unfold fieldSigmaAlgebraModConst
  congr 1; ext1 φ; congr 1; ext1 _
  have h1 : (fun ω => fieldPairing α₀ (hC ω) φ) =
      (fun t : ℝ => t - α₀ * ∫ x, φ x * Real.log ‖x‖) ∘
        fun ω => fieldPairing 0 (hC ω) φ := by
    funext ω
    simp only [Function.comp_apply, fieldPairing, zero_mul, sub_zero]
  rw [h1, ← MeasurableSpace.comap_comp]
  congr 1
  exact (MeasurableEquiv.subRight (α₀ * ∫ x, φ x * Real.log ‖x‖)).measurableEmbedding.comap_eq

open Classical in
/-- A finite count of measurable events is measurable. -/
theorem measurable_count_range {Ξ : Type*} [MeasurableSpace Ξ] (A : ℕ → Set Ξ)
    (hA : ∀ k, MeasurableSet (A k)) (K : ℕ) :
    Measurable (fun x => (((Finset.range K).filter fun k => x ∈ A k).card : ℝ)) := by
  have heq : (fun x => (((Finset.range K).filter fun k => x ∈ A k).card : ℝ)) =
      fun x => ∑ k ∈ Finset.range K, if x ∈ A k then (1 : ℝ) else 0 := by
    funext x
    exact Finset.natCast_card_filter _ _
  rw [heq]
  exact Finset.measurable_sum _ fun k _ => Measurable.ite (hA k) measurable_const measurable_const

open Classical in
/-- Equal laws give equal probabilities for every bound on a finite count of events on the
common state space. This is the measure-theoretic part of the law transfer. -/
theorem measure_count_range_eq_of_map_eq {Ω Ω' Ξ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace Ξ] (P : Measure Ω) (Q : Measure Ω')
    (f : Ω → Ξ) (g : Ω' → Ξ) (hf : Measurable f) (hg : Measurable g)
    (hlaw : P.map f = Q.map g) (A : ℕ → Set Ξ) (hA : ∀ k, MeasurableSet (A k))
    (K : ℕ) (b : ℝ) :
    P {ω | (((Finset.range K).filter fun k => f ω ∈ A k).card : ℝ) < b} =
      Q {ω | (((Finset.range K).filter fun k => g ω ∈ A k).card : ℝ) < b} := by
  let S : Set Ξ := {x | (((Finset.range K).filter fun k => x ∈ A k).card : ℝ) < b}
  have hS : MeasurableSet S := measurableSet_lt (measurable_count_range A hA K) measurable_const
  change P (f ⁻¹' S) = Q (g ⁻¹' S)
  rw [← Measure.map_apply hf hS, ← Measure.map_apply hg hS, hlaw]

open Classical in
/-- Bonanno's annulus iteration bound, with the first `K` events indexed by `Finset.range K`.
The auxiliary event at index zero is the whole sample space; its radius is `r 0 / s₁`. -/
theorem annulus_iteration_range_of_distribution
    (s₁ s₂ α β : ℝ) (hs₁ : 0 < s₁) (hs₁₂ : s₁ < s₂) (hs₂ : s₂ < 1)
    (hα : 0 < α) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ p ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsNormalizedWPGFF h P →
    ∀ r : ℕ → ℝ, (∀ k, 0 < r k) → (∀ k, r (k + 1) ≤ s₁ * r k) →
    ∀ E : ℕ → Set Ω,
      (∀ k, MeasurableSet[LQGMetric.Blueprint.fieldSigma
        (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (r k) 0))
        (LQGMetric.Blueprint.annulus 0 (s₁ * r k) (s₂ * r k))] (E k)) →
      (∀ k, ENNReal.ofReal p ≤ P (E k)) →
      ∀ K : ℕ, P {ω | (((Finset.range K).filter fun k => ω ∈ E k).card : ℝ) < β * K} ≤
        ENNReal.ofReal (C * Real.exp (-α * K)) := by
  obtain ⟨p, C, hp, hp1, hC, hiter⟩ :=
    LQGMetric.LM.lmLem3_1a s₁ s₂ hs₁ hs₁₂ hs₂ α hα β hβ.1 hβ.2
  refine ⟨p, ⟨hp, hp1⟩, C, hC, ?_⟩
  intro Ω _ P _ h hh r hr hratio E hE hprob K
  let r' : ℕ → ℝ := fun k => match k with | 0 => r 0 / s₁ | k + 1 => r k
  let E' : ℕ → Set Ω := fun k => match k with | 0 => univ | k + 1 => E k
  have hs₁1 : s₁ < 1 := lt_trans hs₁₂ hs₂
  have hr' : ∀ k, 0 < r' k := by
    intro k
    cases k with
    | zero => exact div_pos (hr 0) hs₁
    | succ k => exact hr k
  have hratio' : ∀ k, r' (k + 1) / r' k ≤ s₁ := by
    intro k
    cases k with
    | zero =>
      change r 0 / (r 0 / s₁) ≤ s₁
      rw [div_le_iff₀ (div_pos (hr 0) hs₁)]
      field_simp
      exact le_rfl
    | succ k =>
      change r (k + 1) / r k ≤ s₁
      exact (div_le_iff₀ (hr k)).2 (hratio k)
  have hanti : Antitone r' := antitone_nat_of_succ_le fun k => by
    have := (div_le_iff₀ (hr' k)).1 (hratio' k)
    nlinarith [hr' k]
  have hlocal : ∀ k, MeasurableSet[LQGMetric.Blueprint.fieldSigma
      (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (r' k) 0))
      (LQGMetric.Blueprint.annulus 0 (s₁ * r' k) (s₂ * r' k))] (E' k) := by
    intro k
    cases k with
    | zero => exact MeasurableSet.univ
    | succ k => exact hE k
  have hprob' : ∀ k, ENNReal.ofReal p ≤ P (E' k) := by
    intro k
    cases k with
    | zero => simpa only [E', measure_univ] using ENNReal.ofReal_le_one.mpr hp1.le
    | succ k => exact hprob k
  have hcount (ω : Ω) : LQGMetric.Blueprint.countOcc E' K ω =
      ((Finset.range K).filter fun k => ω ∈ E k).card := by
    classical
    unfold LQGMetric.Blueprint.countOcc
    apply Finset.card_bij (fun k _ => k - 1)
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · omega
      · cases k with
        | zero => omega
        | succ k => simpa only [E', Nat.add_sub_cancel] using hk.2
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_Icc] at ha hb
      omega
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_range] at hb
      refine ⟨b + 1, ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, by simpa only [E'] using hb.2⟩
  have hbound := hiter P h hh r' E' ⟨hr', hanti, hratio', hlocal⟩ hprob' K
  simpa only [hcount] using hbound


open Classical in
/-- The same estimate for events equal almost surely to field-measurable events. -/
theorem annulus_iteration_range_of_distribution_ae
    (s₁ s₂ α β : ℝ) (hs₁ : 0 < s₁) (hs₁₂ : s₁ < s₂) (hs₂ : s₂ < 1)
    (hα : 0 < α) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ p ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistC), LQGMetric.IsNormalizedWPGFF h P →
    ∀ r : ℕ → ℝ, (∀ k, 0 < r k) → (∀ k, r (k + 1) ≤ s₁ * r k) →
    ∀ E : ℕ → Set Ω,
      (∀ k, ∃ E' : Set Ω, MeasurableSet[LQGMetric.Blueprint.fieldSigma
        (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (r k) 0))
        (LQGMetric.Blueprint.annulus 0 (s₁ * r k) (s₂ * r k))] E' ∧ E k =ᵐ[P] E') →
      (∀ k, ENNReal.ofReal p ≤ P (E k)) →
      ∀ K : ℕ, P {ω | (((Finset.range K).filter fun k => ω ∈ E k).card : ℝ) < β * K} ≤
        ENNReal.ofReal (C * Real.exp (-α * K)) := by
  obtain ⟨p, hp, C, hC, hiter⟩ :=
    annulus_iteration_range_of_distribution s₁ s₂ α β hs₁ hs₁₂ hs₂ hα hβ
  refine ⟨p, hp, C, hC, ?_⟩
  intro Ω _ P _ h hh r hr hratio E hlocal hprob K
  choose E' hE' hEq using hlocal
  have hprob' : ∀ k, ENNReal.ofReal p ≤ P (E' k) := fun k => by
    rw [← measure_congr (hEq k)]
    exact hprob k
  have hcounts : {ω | (((Finset.range K).filter fun k => ω ∈ E k).card : ℝ) < β * K} =ᵐ[P]
      {ω | (((Finset.range K).filter fun k => ω ∈ E' k).card : ℝ) < β * K} := by
    filter_upwards [ae_all_iff.2 hEq] with ω hω
    have heq : (Finset.range K).filter (fun k => ω ∈ E k) =
        (Finset.range K).filter (fun k => ω ∈ E' k) :=
      Finset.filter_congr fun k _ => Iff.of_eq (hω k)
    simp only [heq]
  rw [measure_congr hcounts]
  exact hiter P h hh r hr hratio E' hE' hprob' K

end HarmonicBalls.Section6
