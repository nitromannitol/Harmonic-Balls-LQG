import HarmonicBalls.FirstPass.Phase2.DomainMarkovGramSchmidt
import HarmonicBalls.Proofs.Sec11.ModConstPairingLaw
import LatticeProb.Prob.CondExpPositive
import LatticeProb.Prob.CountableCoordinates

/-!
# Reduction of the conditional positivity of inner events to countably many coordinates

Let `h` be a whole-plane GFF (pairings `hC`), `O, V ⊆ ℂ`. We reduce the statement

  *every event `A ∈ σ(h|_O)` with `P A > 0` has almost surely positive conditional probability given the field on `V`
  modulo constants (`localModConstPairings`)*

to the following *core* statement about countably many coordinates: for test functions `ψ n` on `O`, pairwise
`G`-orthogonal mean-zero test functions `ρ k` on `V` and measurable sets `S`, `T` of sequences, if the intersection of
`{((h^ℂ, ψ n))_n ∈ S}` and `{((h^ℂ, ρ k))_k ∈ T}` is null, then one of the two events is null.

The steps are:
* an event of `σ(h|_O)` is `{((h, ψ n))_n ∈ S}` for countably many test functions `ψ n` on `O`, and an event of the
  outer sigma-algebra is `{((h, ρ n))_n ∈ S}` for countably many mean-zero test functions `ρ n` on `V`
  (countably many coordinates suffice for an event of a generated sigma-algebra);
* the deterministic logarithmic shift `-α₀ log |·|` is a coordinatewise translation and can be dropped
  (`exists_setOf_fieldPairing_seq_eq`);
* the outer coordinates can be replaced, up to a null set, by pairwise orthogonal ones
  (`IsWholePlaneGFF.exists_orthogonal_pairing_coordinates`);
* positivity of a conditional probability follows from: every event `B` of the conditioning sigma-algebra with
  `P (A ∩ B) = 0` is null (`LatticeProb.ae_condExp_indicator_pos_of_forall_measure_inter_eq_zero`).

## Main results

* `IsWholePlaneGFF.measurable_localModConstPairings`: the outer sigma-algebra modulo constants is a sub-sigma-algebra
  of the ambient one (for `σ(h|_O)` this is `IsWholePlaneGFF.fieldSigmaAlgebra_le`).
* `exists_seq_of_measurableSet_fieldSigmaAlgebra`, `exists_seq_of_measurableSet_comap_localModConstPairings`: events
  in terms of countably many pairings of `h^ℂ`.
* `IsWholePlaneGFF.ae_condExp_indicator_pos_of_orthogonal_core`: the reduction.
-/

namespace HarmonicBalls

open MeasureTheory Set ProbabilityTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The joint process of the outer pairings modulo constants is measurable. -/
theorem IsWholePlaneGFF.measurable_localModConstPairings (hh : IsWholePlaneGFF P hC hcirc) (α₀ : ℝ) (U : Set ℂ) :
    Measurable (localModConstPairings α₀ hC U) :=
  measurable_pi_iff.mpr fun φ =>
    (hh.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ U))).sub_const _

omit [MeasurableSpace Ω] in
/-- An event of `σ(h|_U)` is the event `{((h^ℂ, ψ n))_n ∈ S}` for countably many test functions `ψ n` on `U` and a
measurable set `S` of sequences. -/
theorem exists_seq_of_measurableSet_fieldSigmaAlgebra {α₀ : ℝ} {U : Set ℂ} {A : Set Ω}
    (hA : MeasurableSet[fieldSigmaAlgebra α₀ hC U] A) :
    ∃ (ψ : ℕ → ℂ → ℝ) (S : Set (ℕ → ℝ)), (∀ n, IsTestFunction U (ψ n)) ∧ MeasurableSet S ∧
      A = {ω | (fun n => hC ω (ψ n)) ∈ S} := by
  obtain ⟨ψ, S, hψ, hS, rfl⟩ :=
    LatticeProb.exists_seq_measurableSet_of_measurableSet_iSup_comap_of_forall (p := IsTestFunction U)
      ⟨_, isTestFunction_fun_zero U⟩ (X := fun φ ω => fieldPairing α₀ (hC ω) φ) hA
  obtain ⟨S₁, hS₁, he⟩ := exists_setOf_fieldPairing_seq_eq α₀ hC ψ hS
  exact ⟨ψ, S₁, hψ, hS₁, he⟩

omit [MeasurableSpace Ω] in
/-- An event of the sigma-algebra of the pairings modulo constants on `U` is the event `{((h^ℂ, ρ n))_n ∈ S}` for
countably many mean-zero test functions `ρ n` on `U` and a measurable set `S` of sequences. -/
theorem exists_seq_of_measurableSet_comap_localModConstPairings {α₀ : ℝ} {U : Set ℂ} {B : Set Ω}
    (hB : MeasurableSet[MeasurableSpace.comap (localModConstPairings α₀ hC U) inferInstance] B) :
    ∃ (ρ : ℕ → ℂ → ℝ) (S : Set (ℕ → ℝ)), (∀ n, IsTestFunction U (ρ n) ∧ ∫ x, ρ n x = 0) ∧
      MeasurableSet S ∧ B = {ω | (fun n => hC ω (ρ n)) ∈ S} := by
  have : Nonempty (LocalZeroMeanTest U) := ⟨⟨fun _ => 0, isTestFunction_fun_zero U, by simp⟩⟩
  obtain ⟨x, S, hS, rfl⟩ := LatticeProb.exists_seq_measurableSet_of_measurableSet_comap_pi hB
  obtain ⟨S₁, hS₁, he⟩ := exists_setOf_fieldPairing_seq_eq α₀ hC (fun n => (x n).1) hS
  exact ⟨fun n => (x n).1, S₁, fun n => (x n).2, hS₁, he⟩

/-- **Reduction to orthogonal coordinates.** Suppose that for test functions `ψ n` on `O`, pairwise `G`-orthogonal
mean-zero test functions `ρ k` on `V` and measurable sets `S`, `T` of sequences, a null intersection of
`{((h^ℂ, ψ n))_n ∈ S}` and `{((h^ℂ, ρ k))_k ∈ T}` forces one of the two events to be null. Then every event
`A ∈ σ(h|_O)` with `P A > 0` has almost surely positive conditional probability given the pairings modulo constants
on `V`. -/
theorem IsWholePlaneGFF.ae_condExp_indicator_pos_of_orthogonal_core [IsProbabilityMeasure P]
    (hh : IsWholePlaneGFF P hC hcirc) (α₀ : ℝ) {O V : Set ℂ}
    (hcore : ∀ (ψ ρ : ℕ → ℂ → ℝ) (S T : Set (ℕ → ℝ)), (∀ n, IsTestFunction O (ψ n)) →
      (∀ k, IsTestFunction V (ρ k) ∧ ∫ x, ρ k x = 0) →
      (∀ k l, k ≠ l → wholePlaneGFFCov (.pairing (ρ k)) (.pairing (ρ l)) = 0) →
      MeasurableSet S → MeasurableSet T →
      P ({ω | (fun n => hC ω (ψ n)) ∈ S} ∩ {ω | (fun k => hC ω (ρ k)) ∈ T}) = 0 →
      P {ω | (fun n => hC ω (ψ n)) ∈ S} = 0 ∨ P {ω | (fun k => hC ω (ρ k)) ∈ T} = 0)
    {A : Set Ω} (hA : MeasurableSet[fieldSigmaAlgebra α₀ hC O] A) (hPA : 0 < P A) :
    ∀ᵐ ω ∂P, 0 < (P[A.indicator (1 : Ω → ℝ) |
      MeasurableSpace.comap (localModConstPairings α₀ hC V) inferInstance]) ω := by
  have hAm : MeasurableSet A := hh.fieldSigmaAlgebra_le α₀ O A hA
  obtain ⟨ψ, S, hψ, hS, rfl⟩ := exists_seq_of_measurableSet_fieldSigmaAlgebra hA
  refine LatticeProb.ae_condExp_indicator_pos_of_forall_measure_inter_eq_zero
    (hh.measurable_localModConstPairings α₀ V).comap_le hAm fun B hB h0 => ?_
  obtain ⟨ρ, S', hρ, hS', rfl⟩ := exists_seq_of_measurableSet_comap_localModConstPairings hB
  obtain ⟨ρ', T, hρ', horth, hT, hae⟩ := hh.exists_orthogonal_pairing_coordinates hρ hS'
  have h0' : P ({ω | (fun n => hC ω (ψ n)) ∈ S} ∩ {ω | (fun k => hC ω (ρ' k)) ∈ T}) = 0 := by
    rw [← h0]
    exact measure_congr (ae_eq_set_inter (ae_eq_refl _) hae).symm
  rcases hcore ψ ρ' S T hψ hρ' horth hS hT h0' with h1 | h1
  · exact absurd h1 hPA.ne'
  · rw [measure_congr hae]
    exact h1

end HarmonicBalls
