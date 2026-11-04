import HarmonicBalls.Proofs.Sec11.RandomConstantPairingLaw
import HarmonicBalls.Proofs.Sec11.PairingLawRealizations

/-! # Modulo-constant pairing laws across realizations

The Section 8 germ proof uses Leonardo Bonanno's LatticeProb formalization.
The comparison below concerns the full joint process of local pairings;
absolute continuity of individual coordinates does not suffice.
-/

namespace HarmonicBalls

open MeasureTheory

/-- Restricting the full joint field observation to zero-integral tests
preserves absolute continuity, also for different underlying sample spaces. -/
theorem localModConstPairings_ac_of_localFieldPairings_ac_realizations
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) (α β : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hD : Ξ → (ℂ → ℝ) → ℝ) (U : Set ℂ)
    (hP : Measurable (localFieldPairings α hC U))
    (hQ : Measurable (localFieldPairings β hD U))
    (hAC : P.map (localFieldPairings α hC U) ≪
      Q.map (localFieldPairings β hD U)) :
    P.map (localModConstPairings α hC U) ≪ Q.map (localModConstPairings β hD U) := by
  let R : (LocalFieldTest U → ℝ) → LocalZeroMeanTest U → ℝ :=
    fun v φ => v ⟨φ.1, φ.2.1⟩
  have hR : Measurable R := by
    apply measurable_pi_iff.mpr
    intro φ
    exact measurable_pi_apply (⟨φ.1, φ.2.1⟩ : LocalFieldTest U)
  have hp : localModConstPairings α hC U = R ∘ localFieldPairings α hC U := rfl
  have hq : localModConstPairings β hD U = R ∘ localFieldPairings β hD U := rfl
  rw [hp, hq, ← Measure.map_map hR hP, ← Measure.map_map hR hQ]
  exact hAC.map hR

/-- A comparison on an open region restricts to any smaller test region.
The conclusion concerns the full joint law, not merely its marginals. -/
theorem localModConstPairings_ac_mono
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) (α β : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hD : Ξ → (ℂ → ℝ) → ℝ)
    {U V : Set ℂ} (hVU : V ⊆ U)
    (hP : Measurable (localModConstPairings α hC U))
    (hQ : Measurable (localModConstPairings β hD U))
    (hAC : P.map (localModConstPairings α hC U) ≪
      Q.map (localModConstPairings β hD U)) :
    P.map (localModConstPairings α hC V) ≪ Q.map (localModConstPairings β hD V) := by
  let R : (LocalZeroMeanTest U → ℝ) → LocalZeroMeanTest V → ℝ :=
    fun v φ => v ⟨φ.1, φ.2.1.mono_set hVU, φ.2.2⟩
  have hR : Measurable R := by
    apply measurable_pi_iff.mpr
    intro φ
    exact measurable_pi_apply (⟨φ.1, φ.2.1.mono_set hVU, φ.2.2⟩ : LocalZeroMeanTest U)
  have hp : localModConstPairings α hC V = R ∘ localModConstPairings α hC U := rfl
  have hq : localModConstPairings β hD V = R ∘ localModConstPairings β hD U := rfl
  rw [hp, hq, ← Measure.map_map hR hP, ← Measure.map_map hR hQ]
  exact hAC.map hR

/-- If one sample law is dominated by a whole-plane GFF law, its local
zero-integral pairing law is dominated by that of any other whole-plane GFF
realization, after a common deterministic shift and arbitrary independent
random recenterings. The global domination is an explicit hypothesis and is
not a rooted or Palm comparison. -/
theorem localModConstPairings_shifted_ac_of_dominated_gff
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P S : Measure Ω) (Q : Measure Ξ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {hD : Ξ → (ℂ → ℝ) → ℝ} {hcircD : Ξ → ℝ → ℂ → ℝ}
    (hS : IsWholePlaneGFF S hC hcirc) (hQ : IsWholePlaneGFF Q hD hcircD)
    (hPS : P ≪ S) (α β : ℝ) (d : (ℂ → ℝ) → ℝ)
    (c : Ω → ℝ) (e : Ξ → ℝ) (U : Set ℂ) :
    P.map (localModConstPairings β (fun ω =>
      addFunPairing (fun φ => hC ω φ + d φ) (fun _ => c ω)) U) ≪
    Q.map (localModConstPairings β (fun ω =>
      addFunPairing (fun φ => hD ω φ + d φ) (fun _ => e ω)) U) := by
  rw [localModConstPairings_add_random_constant, localModConstPairings_add_random_constant]
  have hp : Measurable (localFieldPairings β (fun ω φ => hC ω φ + d φ) U) := by
    apply Measurable.of_eval
    intro φ
    change Measurable (fun ω => (hC ω φ.1 + d φ.1) - β * ∫ x, φ.1 x * Real.log ‖x‖)
    exact ((hS.measurable_pairing φ.1 (φ.2.mono_set (Set.subset_univ _))).add_const _).sub_const _
  have hq : Measurable (localFieldPairings β (fun ω φ => hD ω φ + d φ) U) := by
    apply Measurable.of_eval
    intro φ
    change Measurable (fun ω => (hD ω φ.1 + d φ.1) - β * ∫ x, φ.1 x * Real.log ‖x‖)
    exact ((hQ.measurable_pairing φ.1 (φ.2.mono_set (Set.subset_univ _))).add_const _).sub_const _
  apply localModConstPairings_ac_of_localFieldPairings_ac_realizations P Q β β _ _ U hp hq
  exact localFieldPairings_shifted_ac_of_dominated_gff P S Q hS hQ hPS α β d U

#print axioms localModConstPairings_ac_of_localFieldPairings_ac_realizations
#print axioms localModConstPairings_ac_mono
#print axioms localModConstPairings_shifted_ac_of_dominated_gff

end HarmonicBalls
