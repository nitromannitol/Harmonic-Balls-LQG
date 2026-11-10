import HarmonicBalls.FirstPass.S11p.ModConstComposition
import HarmonicBalls.FirstPass.Frozen.S11p
import HarmonicBalls.FirstPass.S11k.ExteriorVersions
import HarmonicBalls.FirstPass.S11k.ExitLocality
import HarmonicBalls.Proofs.Sec6.AnnulusIteration
import HarmonicBalls.Proofs.Sec1.Locality
import HarmonicBalls.Steps.Sec11.LocalPairingLaw
import HarmonicBalls.Steps.Sec11.LocalExtremaRepresentatives
import HarmonicBalls.FirstPass.S11u

/-!
# First pass, Section 11: exterior versions of the field observables (fp-S11k, owner z3)

Let `E` be an open set containing the unit circle. The zero-mean exterior sigma-algebra
`comap (localModConstPairings α₀ hC E)` carries an almost-sure version of every
`fieldSigmaAlgebra α₀ hC U`-measurable real or `ℝ≥0∞` observable with `U ⊆ E`, and of every
exit distance `ENNReal.ofReal (setDist D A (frontier U))` with `closure U ⊆ V ⊆ E` for an open `V`.
These are the building blocks (N1) of `PinchSecondExteriorVersionsStep`, following ChatGPT
`notes/fp-gaps/CHATGPT-n4-B2-z3-N1N2.md` sections 3-5.

Inputs (explicit hypotheses): `WholePlaneCircleAverageLimitFrozen.{u}` (FIRST-PASS FROZEN, n4), the GFF
hypothesis `IsWholePlaneGFF`, and, for the metric, item II (locality) of `LQGMetricFieldAxioms` in the form
of a hypothesis `hII` on the open set `V`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

universe u

namespace ExteriorPairings

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

omit mΩ in
/-- The mean-zero composition at exponent `0` also holds at exponent `α₀`: the zero-mean pairing
sigma-algebra does not depend on the exponent (`Section6.fieldSigmaAlgebraModConst_eq`). -/
theorem comap_localModConst_eq_zero (α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (E : Set ℂ) :
    MeasurableSpace.comap (localModConstPairings 0 hC E) inferInstance =
      MeasurableSpace.comap (localModConstPairings α₀ hC E) inferInstance := by
  rw [← fieldSigmaAlgebraModConst_eq_comap_localModConstPairings 0 hC E,
    ← fieldSigmaAlgebraModConst_eq_comap_localModConstPairings α₀ hC E]
  exact (Section6.fieldSigmaAlgebraModConst_eq α₀ hC E).symm

/-- A test-function pairing supported in an open `E` containing the unit circle has an almost-sure version
measurable for the zero-mean exterior sigma-algebra of `E`. Proof: the exponent-`0` composition
`ae_pairing_exists_meanZero_measurable` (n4) applied to the unit-mass mollifiers of the frozen circle-average
limit on `E`, then the deterministic shift `- α₀ ∫ φ log‖·‖` of `fieldPairing`. -/
theorem exists_exterior_fieldPairing_version
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (α₀ : ℝ) {E : Set ℂ} (hE : IsOpen E) (hsph : sphere (0 : ℂ) 1 ⊆ E)
    {φ : ℂ → ℝ} (hφ : IsTestFunction E φ) :
    ∃ g : Ω → ℝ, Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC E) inferInstance] g ∧
      ∀ᵐ ω ∂P, fieldPairing α₀ (hC ω) φ = g ω := by
  have hb : WholePlaneCircleAverageLimitFrozen.{u} := wholePlaneCircleAverageLimit_derived.{u}
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨ψ, hψ, hlim⟩ := hb Ω P hC hcirc hGFF E 1 0 hE one_pos hsph
  obtain ⟨g0, hg0m, hg0⟩ := ae_pairing_exists_meanZero_measurable hGFF (fun j => (hψ j).1)
    (fun j => (hψ j).2) hlim hφ
  refine ⟨fun ω => g0 ω - α₀ * ∫ x, φ x * Real.log ‖x‖, ?_, ?_⟩
  · rw [comap_localModConst_eq_zero α₀ hC E] at hg0m
    exact hg0m.sub_const _
  · filter_upwards [hg0] with ω hω
    simp only [fieldPairing]
    rw [hω]

/-- Exterior version of a `fieldSigmaAlgebra α₀ hC U`-measurable observable with `U ⊆ E`: an almost-sure version
measurable for the zero-mean exterior sigma-algebra of `E`. Proof: the Doob-Dynkin version lemma
`exists_measurable_version_of_coordinate_versions` over the coordinates `localFieldPairings α₀ hC E`. -/
theorem exists_exterior_version_of_fieldSigmaAlgebra
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (α₀ : ℝ) {E : Set ℂ} (hE : IsOpen E) (hsph : sphere (0 : ℂ) 1 ⊆ E)
    {U : Set ℂ} (hUE : U ⊆ E) {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace.CountablySeparated X]
    (G : Ω → X) (hG : Measurable[fieldSigmaAlgebra α₀ hC U] G) :
    ∃ G' : Ω → X, Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC E) inferInstance] G' ∧
      ∀ᵐ ω ∂P, G' ω = G ω := by
  have hG' : Measurable[fieldSigmaAlgebra α₀ hC E] G := hG.mono (fieldSigmaAlgebra_mono α₀ hC hUE) le_rfl
  rw [fieldSigmaAlgebra_eq_comap_localFieldPairings] at hG'
  refine exists_measurable_version_of_coordinate_versions (localFieldPairings α₀ hC E) ?_ G hG'
  intro i
  obtain ⟨g, hgm, hga⟩ := exists_exterior_fieldPairing_version hGFF α₀ hE hsph i.2
  exact ⟨g, hgm, hga⟩

/-- Exterior version of an infimum of internal metric values on an open set `V ⊆ E`, where the metric
satisfies item II of `LQGMetricFieldAxioms` on `V` (hypothesis `hII`). The infimum over `A × B ⊆ V × V` is
measurable for `fieldSigmaAlgebra V` (`exists_local_iInf_internalMetric_representative`, countable reduction by
continuity), hence for the zero-mean exterior sigma-algebra of `E` (`fieldSigmaAlgebra_mono`). -/
theorem exists_exterior_iInf_internalMetric_version
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (α₀ : ℝ) {E : Set ℂ} (hE : IsOpen E) (hsph : sphere (0 : ℂ) 1 ⊆ E)
    {D : Ω → ℂ → ℂ → ℝ} (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {V : Set ℂ} (hV : IsOpen V) (hVE : V ⊆ E)
    (hII : ∃ G : Ω → ℂ → ℂ → ℝ≥0∞, (∀ z w, Measurable[fieldSigmaAlgebra α₀ hC V] fun ω => G ω z w) ∧
      ∀ᵐ ω ∂P, ∀ z ∈ V, ∀ w ∈ V, internalMetric (D ω) V z w = G ω z w)
    {A B : Set ℂ} (hA : A ⊆ V) (hB : B ⊆ V) :
    ∃ Y : Ω → ℝ≥0∞, Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC E) inferInstance] Y ∧
      ∀ᵐ ω ∂P, (⨅ x ∈ A, ⨅ y ∈ B, internalMetric (D ω) V x y) = Y ω := by
  obtain ⟨G, hGm, hGa⟩ := hII
  obtain ⟨Y, hY, hYa⟩ := exists_local_iInf_internalMetric_representative (m := fieldSigmaAlgebra α₀ hC V)
    hV hA hB hmetric (fun x _ y _ => hGm x y)
    (hGa.mono fun ω h x hx y hy => h x (hA hx) y (hB hy))
  obtain ⟨Y', hY'm, hY'a⟩ := exists_exterior_version_of_fieldSigmaAlgebra hGFF α₀ hE hsph hVE
    Y hY
  exact ⟨Y', hY'm, by filter_upwards [hYa, hY'a] with ω h1 h2; rw [h1, h2]⟩

/-- Exterior version of an exit distance `ENNReal.ofReal (setDist D A (frontier U))`, for an open `U` and an open
`V ⊆ E` with `closure U ⊆ V`, under item II of the metric on `V`. Proof: `exists_outside_ofReal_setDist_of_internalMetric`
(first-exit truncation, ChatGPT section 5.1) gives a `fieldSigmaAlgebra V`-measurable version, and
`exists_exterior_version_of_fieldSigmaAlgebra` moves it to the zero-mean exterior sigma-algebra. -/
theorem exists_exterior_ofReal_setDist_version
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (α₀ : ℝ) {E : Set ℂ} (hE : IsOpen E) (hsph : sphere (0 : ℂ) 1 ⊆ E)
    {D : Ω → ℂ → ℂ → ℝ} (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {U V A : Set ℂ} (hU : IsOpen U) (hV : IsOpen V) (hVE : V ⊆ E) (hAU : A ⊆ U) (hUV : closure U ⊆ V)
    (hA : A.Nonempty) (hfront : (frontier U).Nonempty)
    (hII : ∃ G : Ω → ℂ → ℂ → ℝ≥0∞, (∀ z w, Measurable[fieldSigmaAlgebra α₀ hC V] fun ω => G ω z w) ∧
      ∀ᵐ ω ∂P, ∀ z ∈ V, ∀ w ∈ V, internalMetric (D ω) V z w = G ω z w) :
    ∃ a : Ω → ℝ≥0∞, Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC E) inferInstance] a ∧
      ∀ᵐ ω ∂P, a ω = ENNReal.ofReal (setDist (D ω) A (frontier U)) := by
  obtain ⟨G, hGm, hGa⟩ := hII
  have hEq : ∀ᵐ ω ∂P, ∀ x ∈ A, ∀ y ∈ frontier U, internalMetric (D ω) V x y = G ω x y :=
    hGa.mono fun ω h x hx y hy => h x (hUV (subset_closure (hAU hx))) y (hUV (frontier_subset_closure hy))
  obtain ⟨a, ham, haa⟩ := exists_outside_ofReal_setDist_of_internalMetric (m := fieldSigmaAlgebra α₀ hC V)
    hV hU hAU hUV hA hfront hmetric (fun x _ y _ => hGm x y) hEq
  obtain ⟨a', ham', ha'a⟩ := exists_exterior_version_of_fieldSigmaAlgebra hGFF α₀ hE hsph hVE a ham
  exact ⟨a', ham', by filter_upwards [haa, ha'a] with ω h1 h2; rw [h2, h1]⟩

end ExteriorPairings

end HarmonicBalls
