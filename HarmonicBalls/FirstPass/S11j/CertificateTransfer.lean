import HarmonicBalls.FirstPass.Frozen.S11d

/-!
# Cameron-Martin transfer through one common field event

Proved, not frozen.
Two events `E0`, `Ef` on the carrier `Ω` of a whole-plane GFF `hC` are certified by one common measurable event `B` of
fields: `ω ∈ E0 ↔ hC ω ∈ B` and `ω ∈ Ef ↔ addFunPairing (hC ω) f ∈ B` almost surely. The Cameron-Martin mutual absolute
continuity of `hC` and `hC + f` (`CameronMartinGFFMutualAbsCont`, Miller-Sheffield arXiv:1302.4738v2 Proposition 2.9,
frozen in `FirstPass/Frozen/S11d.lean`) then transfers null sets and positivity. The inner-measure conclusion uses a
measurable null superset of the exceptional set, so completeness of `(Ω, P)` is not needed.
-/

universe u

namespace HarmonicBalls

open MeasureTheory

/-- A map into the distribution σ-algebra is measurable as soon as each test pairing is a random variable. -/
theorem measurable_into_distributionMeasurableSpace {Ω : Type*} [MeasurableSpace Ω]
    {F : Ω → (ℂ → ℝ) → ℝ} (h : ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ → Measurable fun ω => F ω φ) :
    @Measurable Ω ((ℂ → ℝ) → ℝ) _ distributionMeasurableSpace F := by
  apply Measurable.of_comap_le
  unfold distributionMeasurableSpace
  simp only [MeasurableSpace.comap_iSup]
  refine iSup_le fun φ => iSup_le fun hφ => ?_
  rw [MeasurableSpace.comap_comp]
  exact (h φ hφ).comap_le

/-- Cameron-Martin transfer through one common measurable field event (proved from the frozen
`CameronMartinGFFMutualAbsCont`). For a whole-plane GFF `hC` and a smooth compactly supported `f` with zero unit-circle
average, if `E0` and `Ef` are both certified by one measurable field event `B`, then both are null-measurable, `P Ef = 0 ↔
P E0 = 0`, and positive probability of `Ef` gives a measurable subset of `E0` of positive probability. -/
theorem cameronMartinFieldCertificateTransfer (hCM : CameronMartinGFFMutualAbsCont.{u}) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (f : ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      Real.circleAverage f 0 1 = 0 →
      ∀ E0 Ef : Set Ω,
        (∃ B : Set ((ℂ → ℝ) → ℝ), MeasurableSet[distributionMeasurableSpace] B ∧
          (∀ᵐ ω ∂P, ω ∈ E0 ↔ hC ω ∈ B) ∧
          (∀ᵐ ω ∂P, ω ∈ Ef ↔ addFunPairing (hC ω) f ∈ B)) →
        NullMeasurableSet E0 P ∧ NullMeasurableSet Ef P ∧ (P Ef = 0 ↔ P E0 = 0) ∧
        (0 < P Ef → ∃ A ⊆ E0, MeasurableSet A ∧ 0 < P A) := by
  intro Ω _ P _ hC hcirc f hGFF hsm hcomp hcirc0 E0 Ef ⟨B, hB, hE0, hEf⟩
  have hmC : @Measurable Ω ((ℂ → ℝ) → ℝ) _ distributionMeasurableSpace hC :=
    measurable_into_distributionMeasurableSpace fun φ hφ => hGFF.measurable_pairing φ hφ
  have hmS : @Measurable Ω ((ℂ → ℝ) → ℝ) _ distributionMeasurableSpace (fun ω => addFunPairing (hC ω) f) :=
    measurable_into_distributionMeasurableSpace fun φ hφ => by
      simp only [addFunPairing]
      exact ((hGFF.measurable_pairing φ hφ).add_const _)
  have hA0m : MeasurableSet (hC ⁻¹' B) := hmC hB
  have hAfm : MeasurableSet ((fun ω => addFunPairing (hC ω) f) ⁻¹' B) := hmS hB
  have hcm := hCM Ω P hC hcirc f hGFF hsm hcomp hcirc0 B hB
  -- the two events agree almost surely with their field representatives
  have hE0eq : E0 =ᵐ[P] hC ⁻¹' B := Filter.eventuallyEqSet_iff.2 hE0
  have hEfeq : Ef =ᵐ[P] (fun ω => addFunPairing (hC ω) f) ⁻¹' B := Filter.eventuallyEqSet_iff.2 hEf
  have hNE0 : NullMeasurableSet E0 P := hA0m.nullMeasurableSet.congr hE0eq.symm
  have hNEf : NullMeasurableSet Ef P := hAfm.nullMeasurableSet.congr hEfeq.symm
  have hPE0 : P E0 = P (hC ⁻¹' B) := measure_congr hE0eq
  have hPEf : P Ef = P ((fun ω => addFunPairing (hC ω) f) ⁻¹' B) := measure_congr hEfeq
  refine ⟨hNE0, hNEf, ?_, ?_⟩
  · rw [hPEf, hPE0]
    exact hcm.symm
  · intro hpos
    have hposf : 0 < P ((fun ω => addFunPairing (hC ω) f) ⁻¹' B) := by rw [← hPEf]; exact hpos
    have hA0pos : 0 < P (hC ⁻¹' B) :=
      pos_iff_ne_zero.2 fun h0 => (pos_iff_ne_zero.1 hposf) (hcm.1 h0)
    -- the exceptional set is null; take a measurable null superset and remove it from `hC ⁻¹' B`
    have hN : P {ω | ¬ (ω ∈ E0 ↔ hC ω ∈ B)} = 0 := ae_iff.1 hE0
    obtain ⟨N, hNN, hNm, hN0⟩ := exists_measurable_superset_of_null hN
    refine ⟨hC ⁻¹' B \ N, ?_, hA0m.diff hNm, ?_⟩
    · intro ω hω
      by_contra hE
      exact hω.2 (hNN (show ¬(ω ∈ E0 ↔ hC ω ∈ B) from fun h => hE (h.2 hω.1)))
    · rw [measure_sdiff_null hN0]
      exact hA0pos

end HarmonicBalls
