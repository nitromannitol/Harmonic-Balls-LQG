import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Steps.Sec11.GaussianProcessLaw

/-!
# Laws of whole-plane GFF pairings on `distributionMeasurableSpace`

For a whole-plane GFF `(P, hC, hcirc)` the random pairing functional `ω ↦ hC ω` is measurable for
`distributionMeasurableSpace` (`measurable_wholePlaneGFF_distribution`), and two whole-plane GFFs on one
probability space give the same probability to every event of the form `hC ⁻¹' A`, `A` measurable for
`distributionMeasurableSpace` (`wholePlaneGFF_distribution_preimage_eq`).

The second statement is reduced to the equality of the laws of the test-function pairings, which is
`wholePlaneGFF_localFieldPairings_map_eq` (Steps/Sec11/GaussianProcessLaw.lean). That lemma uses only the
Gaussian and covariance clauses of `IsWholePlaneGFF`; no external input is used here.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set

/-- `distributionMeasurableSpace` is the pullback of the product σ-algebra on the test functions. -/
theorem distributionMeasurableSpace_eq_comap :
    distributionMeasurableSpace =
      MeasurableSpace.comap (fun (T : (ℂ → ℝ) → ℝ) (φ : LocalFieldTest (univ : Set ℂ)) => T φ.1)
        MeasurableSpace.pi := by
  let Φ0 : ((ℂ → ℝ) → ℝ) → (LocalFieldTest (univ : Set ℂ) → ℝ) := fun T ψ => T ψ.1
  apply le_antisymm
  · refine iSup₂_le fun φ hφ => ?_
    have hΦ0 : Measurable[MeasurableSpace.comap Φ0 MeasurableSpace.pi] Φ0 := comap_measurable Φ0
    have hev : Measurable[MeasurableSpace.comap Φ0 MeasurableSpace.pi]
        (fun T : (ℂ → ℝ) → ℝ => T φ) :=
      (measurable_pi_apply (⟨φ, hφ⟩ : LocalFieldTest (univ : Set ℂ))).comp hΦ0
    exact hev.comap_le
  · have hpi : (MeasurableSpace.pi : MeasurableSpace (LocalFieldTest (univ : Set ℂ) → ℝ)) =
        ⨆ (ψ : LocalFieldTest (univ : Set ℂ)),
          MeasurableSpace.comap (fun f : LocalFieldTest (univ : Set ℂ) → ℝ => f ψ) inferInstance :=
      rfl
    rw [hpi, MeasurableSpace.comap_iSup]
    refine iSup_le fun ψ => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_iSup₂ (f := fun (χ : ℂ → ℝ) (_ : IsTestFunction univ χ) =>
      MeasurableSpace.comap (fun T : (ℂ → ℝ) → ℝ => T χ) inferInstance) ψ.1 ψ.2

/-- A whole-plane GFF is a measurable random pairing functional for `distributionMeasurableSpace`. -/
theorem measurable_wholePlaneGFF_distribution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) :
    @Measurable Ω ((ℂ → ℝ) → ℝ) _ distributionMeasurableSpace hC := by
  refine measurable_iff_comap_le.2 ?_
  unfold distributionMeasurableSpace
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun φ => ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun hφ => ?_
  rw [MeasurableSpace.comap_comp]
  exact (h.measurable_pairing φ hφ).comap_le

/-- Two whole-plane GFFs on one probability space give the same probability to the events `hC ⁻¹' A`,
`A` measurable for `distributionMeasurableSpace`: the laws of the pairing functionals agree. -/
theorem wholePlaneGFF_distribution_preimage_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P hC' hcirc')
    {A : Set ((ℂ → ℝ) → ℝ)} (hA : MeasurableSet[distributionMeasurableSpace] A) :
    P (hC ⁻¹' A) = P (hC' ⁻¹' A) := by
  have hmap := wholePlaneGFF_localFieldPairings_map_eq (Q := P) h h' 0 (univ : Set ℂ)
  rw [distributionMeasurableSpace_eq_comap] at hA
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  let Φ : ((ℂ → ℝ) → ℝ) → (LocalFieldTest (univ : Set ℂ) → ℝ) := fun T φ => T φ.1
  have hΦ : @Measurable ((ℂ → ℝ) → ℝ) _ distributionMeasurableSpace _ Φ := by
    rw [distributionMeasurableSpace_eq_comap]
    exact comap_measurable _
  have key : ∀ (G : Ω → (ℂ → ℝ) → ℝ) (g : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P G g →
      P (G ⁻¹' (Φ ⁻¹' B)) = P.map (localFieldPairings 0 G univ) B := by
    intro G g hG
    have he : localFieldPairings 0 G univ = fun ω => Φ (G ω) := by
      funext ω φ
      simp [Φ, localFieldPairings, fieldPairing]
    have hmG : Measurable (fun ω => Φ (G ω)) :=
      hΦ.comp (measurable_wholePlaneGFF_distribution hG)
    rw [he, Measure.map_apply hmG hB]
    rfl
  rw [key hC _ h, key hC' _ h', hmap]
