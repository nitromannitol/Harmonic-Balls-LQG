import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.FirstPass.Frozen.S11aj
import HarmonicBalls.Steps.Sec11.GaussianProcessLaw

/-! # Mutual absolute continuity of the shifted whole-plane GFF

Derives `CameronMartinGFFMutualAbsCont` (FirstPass/Frozen/S11d.lean:74) from the frozen Cameron-Martin reweighting
`CameronMartinGFFReweighting` (FirstPass/Frozen/S11aj.lean:33; Miller-Sheffield, Imaginary Geometry, Proposition 2.9,
for the Cameron-Martin shift `h ↦ h + g` of a smooth compactly supported `g` with zero unit-circle average).

Argument. Let `P' ~ P` be the measure of `CameronMartinGFFReweighting` for `g`, so that `(hC + g, hcirc + g_r)` is a
whole-plane GFF under `P'`. Both `hC` under `P` and `hC + g` under `P'` are centred Gaussian families of pairings with the
same covariance `wholePlaneGFFCov`, so they have the same law for the pairings with test functions
(`wholePlaneGFF_localFieldPairings_map_eq`, with `α₀ = 0` and `U = univ`). The distribution σ-algebra is the one pulled
back by the evaluation on test functions, so `P'(hC + g ∈ B) = P(hC ∈ B)` for every `B` in `distributionMeasurableSpace`.
Mutual absolute continuity of `P` and `P'` then gives the equivalence of the two null conditions. -/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

universe u

/-- The evaluation of a distribution on the test functions of `univ`, as a function on the index type
`LocalFieldTest univ`. -/
noncomputable def cmDerivedEval : ((ℂ → ℝ) → ℝ) → (LocalFieldTest Set.univ → ℝ) :=
  fun T φ => T φ.1

theorem cmDerivedEval_comap_le :
    MeasurableSpace.comap cmDerivedEval MeasurableSpace.pi ≤ distributionMeasurableSpace := by
  unfold distributionMeasurableSpace
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  refine iSup_le fun φ => ?_
  rw [MeasurableSpace.comap_comp]
  exact le_iSup₂_of_le φ.1 φ.2 le_rfl

theorem cmDerivedEval_measurable : Measurable[distributionMeasurableSpace] cmDerivedEval :=
  measurable_iff_comap_le.2 cmDerivedEval_comap_le

/-- The distribution σ-algebra is the σ-algebra pulled back by `cmDerivedEval` from the product σ-algebra. -/
theorem distributionMeasurableSpace_eq_comap_cmDerivedEval :
    distributionMeasurableSpace = MeasurableSpace.comap cmDerivedEval MeasurableSpace.pi := by
  apply le_antisymm
  · unfold distributionMeasurableSpace
    refine iSup₂_le fun φ hφ => ?_
    have hΨ : Measurable[MeasurableSpace.comap cmDerivedEval MeasurableSpace.pi] cmDerivedEval :=
      comap_measurable cmDerivedEval
    have hev : Measurable[MeasurableSpace.comap cmDerivedEval MeasurableSpace.pi]
        (fun T : (ℂ → ℝ) → ℝ => T φ) :=
      (measurable_pi_apply (⟨φ, hφ⟩ : {φ : ℂ → ℝ // IsTestFunction Set.univ φ})).comp hΨ
    exact hev.comap_le
  · exact cmDerivedEval_comap_le

/-- Cameron-Martin mutual absolute continuity, derived from the reweighting input. -/
theorem cameronMartinGFFMutualAbsCont_derived
    (hRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u}) :
    CameronMartinGFFMutualAbsCont.{u} := by
  intro Ω _ P _ hC hcirc g hW hgC hgS hgc B hB
  obtain ⟨P', hP'P, hPP', hW'⟩ := hRew Ω P hC hcirc hW g hgC hgS hgc
  rw [distributionMeasurableSpace_eq_comap_cmDerivedEval] at hB
  obtain ⟨B', hB', rfl⟩ := MeasurableSpace.measurableSet_comap.1 hB
  -- the law of the pairings with test functions, under `P` and under `P'`
  have hmap := wholePlaneGFF_localFieldPairings_map_eq hW hW' 0 Set.univ
  have e1 : localFieldPairings 0 hC Set.univ = fun ω => cmDerivedEval (hC ω) := by
    funext ω φ
    simp [localFieldPairings, fieldPairing, cmDerivedEval]
  have e2 : localFieldPairings 0 (fun ω => addFunPairing (hC ω) g) Set.univ =
      fun ω => cmDerivedEval (addFunPairing (hC ω) g) := by
    funext ω φ
    simp [localFieldPairings, fieldPairing, cmDerivedEval]
  rw [e1, e2] at hmap
  have hF : Measurable fun ω => cmDerivedEval (hC ω) :=
    measurable_pi_iff.2 fun φ => hW.measurable_pairing φ.1 φ.2
  have hF' : Measurable fun ω => cmDerivedEval (addFunPairing (hC ω) g) :=
    measurable_pi_iff.2 fun φ => hW'.measurable_pairing φ.1 φ.2
  have hLHS : P (hC ⁻¹' (cmDerivedEval ⁻¹' B')) = (P.map fun ω => cmDerivedEval (hC ω)) B' :=
    (Measure.map_apply hF hB').symm
  have hRHS : P' ((fun ω => addFunPairing (hC ω) g) ⁻¹' (cmDerivedEval ⁻¹' B')) =
      (P'.map fun ω => cmDerivedEval (addFunPairing (hC ω) g)) B' :=
    (Measure.map_apply hF' hB').symm
  have hEq : P (hC ⁻¹' (cmDerivedEval ⁻¹' B')) =
      P' ((fun ω => addFunPairing (hC ω) g) ⁻¹' (cmDerivedEval ⁻¹' B')) := by
    rw [hLHS, hRHS, hmap]
  constructor
  · intro h0
    have h1 : P' ((fun ω => addFunPairing (hC ω) g) ⁻¹' (cmDerivedEval ⁻¹' B')) = 0 := by
      rw [← hEq]
      exact h0
    exact hPP' h1
  · intro h0
    have h1 : P' ((fun ω => addFunPairing (hC ω) g) ⁻¹' (cmDerivedEval ⁻¹' B')) = 0 := hP'P h0
    rw [← hEq] at h1
    exact h1

end HarmonicBalls
