import HarmonicBalls.Proofs.Sec11.ShiftedPairingGerm

/-! # Absolute continuity of deterministically shifted pairing laws

The Section 8 germ proof uses Leonardo Bonanno's LatticeProb formalization.
The comparison remains a hypothesis on the full joint pairing law.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- Changing the logarithmic charge and adding deterministic values to all
pairings preserves absolute continuity between the two full local pairing
laws. The compared measures live on the same sample space, and measurability
of the original local pairing process is explicit. -/
theorem localFieldPairings_map_absolutelyContinuous_iff_of_deterministic_shift
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    (α β : ℝ) (hC hC' : Ω → (ℂ → ℝ) → ℝ)
    (d : (ℂ → ℝ) → ℝ) (hd : ∀ ω φ, hC' ω φ = hC ω φ + d φ)
    (U : Set ℂ) (hf : Measurable (localFieldPairings α hC U)) :
    P.map (localFieldPairings β hC' U) ≪ Q.map (localFieldPairings β hC' U) ↔
      P.map (localFieldPairings α hC U) ≪ Q.map (localFieldPairings α hC U) := by
  have heq : fieldSigmaAlgebra β hC' U = fieldSigmaAlgebra α hC U := by
    rw [fieldSigmaAlgebra_eq_of_deterministic_pairing_shift β hC hC' d hd,
      fieldSigmaAlgebra_eq β, fieldSigmaAlgebra_eq α]
  have hcomap : MeasurableSpace.comap (localFieldPairings β hC' U) inferInstance =
      MeasurableSpace.comap (localFieldPairings α hC U) inferInstance := by
    rw [← fieldSigmaAlgebra_eq_comap_localFieldPairings,
      ← fieldSigmaAlgebra_eq_comap_localFieldPairings]
    exact heq
  have hg : Measurable (localFieldPairings β hC' U) :=
    measurable_iff_comap_le.mpr (hcomap ▸ hf.comap_le)
  rw [← trim_comap_absolutelyContinuous_iff P Q _ hg,
    ← trim_comap_absolutelyContinuous_iff P Q _ hf]
  constructor
  · intro hac
    apply Measure.AbsolutelyContinuous.mk
    intro s hs hz
    have hs' : MeasurableSet[MeasurableSpace.comap (localFieldPairings β hC' U)
        inferInstance] s := by rw [hcomap]; exact hs
    have hz' : Q.trim hg.comap_le s = 0 := by
      rw [trim_measurableSet_eq hg.comap_le hs']
      simpa only [trim_measurableSet_eq hf.comap_le hs] using hz
    have hp := hac hz'
    rw [trim_measurableSet_eq hg.comap_le hs'] at hp
    simpa only [trim_measurableSet_eq hf.comap_le hs] using hp
  · intro hac
    apply Measure.AbsolutelyContinuous.mk
    intro s hs hz
    have hs' : MeasurableSet[MeasurableSpace.comap (localFieldPairings α hC U)
        inferInstance] s := by rw [← hcomap]; exact hs
    have hz' : Q.trim hf.comap_le s = 0 := by
      rw [trim_measurableSet_eq hf.comap_le hs']
      simpa only [trim_measurableSet_eq hg.comap_le hs] using hz
    have hp := hac hz'
    rw [trim_measurableSet_eq hf.comap_le hs'] at hp
    simpa only [trim_measurableSet_eq hg.comap_le hs] using hp

/-- A full local pairing-law comparison for the original field transfers to
the shifted field's modulo-constant origin germ. -/
theorem origin_shifted_modConst_germ_trivial_of_unshifted_pairing_law
    {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    {hC hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hQ : IsWholePlaneGFF Q hC hcirc) (α β : ℝ)
    (d : (ℂ → ℝ) → ℝ) (hd : ∀ ω φ, hC' ω φ = hC ω φ + d φ)
    {r : ℝ} (hr : 0 < r)
    (hAC : P.map (localFieldPairings α hC (ball 0 r)) ≪
      Q.map (localFieldPairings α hC (ball 0 r))) :
    ∀ A : Set Ω, (∀ ε : ℝ, 0 < ε →
      MeasurableSet[Section6.fieldSigmaAlgebraModConst β hC' (ball 0 ε)] A) →
      P A = 0 ∨ P A = 1 := by
  have hf : Measurable (localFieldPairings α hC (ball 0 r)) := by
    apply measurable_iff_comap_le.mpr
    rw [← fieldSigmaAlgebra_eq_comap_localFieldPairings]
    exact hQ.fieldSigmaAlgebra_le α _
  have hAC' := (localFieldPairings_map_absolutelyContinuous_iff_of_deterministic_shift
    P Q α β hC hC' d hd (ball 0 r) hf).mpr hAC
  exact origin_shifted_modConst_germ_trivial_of_pairing_law P Q hQ β d hd hr hAC'


end HarmonicBalls
