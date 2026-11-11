import HarmonicBalls.FirstPass.S11c.ShiftMass
import HarmonicBalls.FirstPass.S11c.ProbGlue

/-!
# Proposition 11.10, the shifted event has positive probability

In the proof of Proposition 11.10 (paper lines 3091-3112) the shifted event
`{sup_{S₂} D_{h̃} ≤ ε, C ≤ μ_{h̃}(S₁)}` is shown to have positive probability by intersecting four good events. This file
contains the two elementary steps: (i) the shifted mass of a set on which the shift vanishes is at least the unshifted mass
of that set, since the density `exp(γ f)` is one there; (ii) the four-fold intersection lemma of `ProbGlue` gives positive
probability of any event containing the intersection.
-/

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicBalls

/-- The shifted mass of `S` is at least the unshifted mass of a measurable subset `T ⊆ S` on which the shift vanishes
(the density `exp(γ f)` equals one on `T`). This is the class-cell mass in the printed proof of `lemma:mass-diam`. -/
lemma mass_le_shifted_mass_of_zero_on {γ ξ : ℝ} {f : ℂ → ℝ} {S T : Set ℂ} (hT : MeasurableSet T)
    (hTS : T ⊆ S) (hf : ∀ z ∈ T, f z = 0) (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) :
    μ T ≤ (weylShiftPair γ ξ f (μ, D)).1 S := by
  have h1 := weylShiftPair_fst_apply_of_const (γ := γ) (ξ := ξ) (a := 0) hT hf μ D
  simp only [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul] at h1
  calc μ T = (weylShiftPair γ ξ f (μ, D)).1 T := h1.symm
    _ ≤ (weylShiftPair γ ξ f (μ, D)).1 S := measure_mono hTS

/-- The four-fold intersection of the good events lies in the event where both properties hold, provided the first
property holds on `A ∩ B` and the second on `X ∩ G`. -/
lemma inter_four_subset_of_good {Ω : Type*} {X G A B : Set Ω} {P₁ P₂ : Ω → Prop}
    (h₁ : ∀ ω ∈ A ∩ B, P₁ ω) (h₂ : ∀ ω ∈ X ∩ G, P₂ ω) :
    X ∩ G ∩ A ∩ B ⊆ {ω | P₁ ω ∧ P₂ ω} := by
  intro ω hω
  exact ⟨h₁ ω ⟨hω.1.2, hω.2⟩, h₂ ω hω.1.1⟩

/-- Positive probability of an event containing the good intersection `X ∩ G ∩ A ∩ B`, when the complements of
`G`, `A`, `B` have total measure less than that of `X`. -/
lemma pos_of_superset_good_inter {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {X G A B E : Set Ω}
    (hsum : P Gᶜ + P Aᶜ + P Bᶜ < P X) (hsub : X ∩ G ∩ A ∩ B ⊆ E) :
    0 < P E :=
  lt_of_lt_of_le (measure_pos_inter_three_of_compl_sum_lt P hsum) (measure_mono hsub)

end HarmonicBalls
