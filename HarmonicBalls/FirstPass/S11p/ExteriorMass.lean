import HarmonicBalls.FirstPass.S11p
import HarmonicBalls.FirstPass.S11p.NullSigma
import HarmonicBalls.FirstPass.S11p.ModConstComposition
import HarmonicBalls.FirstPass.S11p.FiniteWeighted
import HarmonicBalls.FirstPass.S11p.BaseFinite
import HarmonicBalls.FirstPass.S11p.BufferedGeometry
import HarmonicBalls.FirstPass.Frozen.S11p
import HarmonicBalls.FirstPass.Frozen.S11k
import HarmonicBalls.FirstPass.S11u

/-!
# Exterior measurability of the LQG mass in the annulus

Discharges the hypothesis `hExt` of `exists_exterior_annulusGreenPotentialSup` (`FirstPass/S11p.lean`) from the
external inputs `LQGMassInnerMeasurableFrozen` (Frozen/S11k, locality and measurability of the LQG mass, BRG Fact 2.1 II)
and `WholePlaneCircleAverageLimitFrozen` (Frozen/S11p, input (b)), together with the geometric hypotheses that the unit
circle and the sets `closure U` (`U` open, `U ⊆ 𝔸_{3,6}`) avoid `closure W`. The normalisation (a) is the theorem
`IsWholePlaneGFF.ae_circleAverage_one_zero`.

Chain: (1) exponent `0` to exponent `α₀` transfer of the mean-zero σ-algebra; (2) generator-wise a.s. measurability at
exponent `α₀` (`ae_pairing_exists_meanZero_measurable`); (3) the full field σ-algebra lies in the null modification of the
exterior mean-zero σ-algebra; (4) the mass is measurable for it; (5) the null-modification completion
(`exists_measurable_of_measurable_nullSigma`).
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

universe u

/-- (1) The mean-zero σ-algebra at exponent `0` is contained in the one at exponent `α₀` (deterministic shift). -/
theorem comap_localModConst_zero_le {Ω : Type*} [MeasurableSpace Ω] (α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (O : Set ℂ) :
    MeasurableSpace.comap (localModConstPairings 0 hC O) inferInstance ≤
      MeasurableSpace.comap (localModConstPairings α₀ hC O) inferInstance := by
  have hT : Measurable (fun (v : LocalZeroMeanTest O → ℝ) (t : LocalZeroMeanTest O) =>
      v t + α₀ * ∫ x, t.1 x * Real.log ‖x‖) :=
    Measurable.of_eval (fun t => (measurable_pi_apply t).add_const _)
  have hf : localModConstPairings 0 hC O = (fun (v : LocalZeroMeanTest O → ℝ) (t : LocalZeroMeanTest O) =>
      v t + α₀ * ∫ x, t.1 x * Real.log ‖x‖) ∘ localModConstPairings α₀ hC O := by
    funext ω t
    simp only [localModConstPairings, fieldPairing, Function.comp_apply]
    ring
  rw [hf]
  exact Measurable.comap_le (hT.comp (comap_measurable (localModConstPairings α₀ hC O)))

/-- (2) At exponent `α₀`, a pairing with a test function in `O` is a.s. equal to a variable measurable for the exterior
mean-zero σ-algebra at exponent `α₀`. -/
theorem ae_fieldPairing_exists_measurable_exterior {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (α₀ : ℝ) {O : Set ℂ} {ψ : ℕ → ℂ → ℝ}
    (hψt : ∀ j, IsTestFunction O (ψ j)) (hψint : ∀ j, ∫ x, ψ j x = 1)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun j => hC ω (ψ j)) atTop (𝓝 (hcirc ω 1 0)))
    {φ : ℂ → ℝ} (hφ : IsTestFunction O φ) :
    ∃ g : Ω → ℝ, Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC O) inferInstance] g ∧
      ∀ᵐ ω ∂P, fieldPairing α₀ (hC ω) φ = g ω := by
  obtain ⟨g0, hg0m, hg0a⟩ := ae_pairing_exists_meanZero_measurable hGFF hψt hψint hlim hφ
  refine ⟨fun ω => g0 ω - α₀ * ∫ x, φ x * Real.log ‖x‖, ?_, ?_⟩
  · exact (hg0m.mono (comap_localModConst_zero_le α₀ hC O) le_rfl).sub_const _
  · filter_upwards [hg0a] with ω hω
    simp only [fieldPairing]
    rw [hω]

/-- (3) The full field σ-algebra on `O` (with constant) lies in the `P`-null modification of the exterior mean-zero
σ-algebra at exponent `α₀`. -/
theorem fieldSigmaAlgebra_le_nullSigma_exterior {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (α₀ : ℝ) {O : Set ℂ}
    (hψ : ∃ ψ : ℕ → ℂ → ℝ, (∀ j, IsTestFunction O (ψ j) ∧ ∫ x, ψ j x = 1) ∧
      ∀ᵐ ω ∂P, Tendsto (fun j => hC ω (ψ j)) atTop (𝓝 (hcirc ω 1 0))) :
    fieldSigmaAlgebra α₀ hC O ≤
      nullSigma (NullIdeal.ofMeasure P)
        (MeasurableSpace.comap (localModConstPairings α₀ hC O) inferInstance) := by
  obtain ⟨ψ, hψ1, hlim⟩ := hψ
  refine iSup₂_le fun φ hφ => ?_
  obtain ⟨g, hgm, hga⟩ :=
    ae_fieldPairing_exists_measurable_exterior hGFF α₀ (fun j => (hψ1 j).1) (fun j => (hψ1 j).2) hlim hφ
  have hN : (NullIdeal.ofMeasure P).Null {ω | ¬ fieldPairing α₀ (hC ω) φ = g ω} := ae_iff.1 hga
  have hm : Measurable[nullSigma (NullIdeal.ofMeasure P)
      (MeasurableSpace.comap (localModConstPairings α₀ hC O) inferInstance)]
      (fun ω => fieldPairing α₀ (hC ω) φ) :=
    measurable_nullSigma_of_ae_eq hgm hN (fun ω hω => not_not.1 hω)
  exact hm.comap_le

/-- (4)+(5) The LQG mass of an open subset of the exterior, a.s. equal to a variable measurable for the exterior
mean-zero σ-algebra at exponent `α₀`. -/
theorem exists_exterior_mass_version {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (γ α₀ : ℝ) (μ : Ω → Measure ℂ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hLQG : IsLQGMeasureOfField P γ α₀ hcirc μ) (hFr : LQGMassInnerMeasurableFrozen.{u})
    {O : Set ℂ} (hO : IsOpen O)
    (hψ : ∃ ψ : ℕ → ℂ → ℝ, (∀ j, IsTestFunction O (ψ j) ∧ ∫ x, ψ j x = 1) ∧
      ∀ᵐ ω ∂P, Tendsto (fun j => hC ω (ψ j)) atTop (𝓝 (hcirc ω 1 0)))
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (hUO : closure U ⊆ O) :
    ∃ g : Ω → ℝ≥0∞,
      Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC O) inferInstance] g ∧
        ∀ᵐ ω ∂P, μ ω U = g ω := by
  obtain ⟨g, hgm, hga⟩ := hFr γ α₀ Ω P hC hcirc μ hGFF hγ0 hγ2 hα hLQG O U hO hU hUb hUO
  have hgN : Measurable[nullSigma (NullIdeal.ofMeasure P)
      (MeasurableSpace.comap (localModConstPairings α₀ hC O) inferInstance)] g :=
    hgm.mono (fieldSigmaAlgebra_le_nullSigma_exterior hGFF α₀ hψ) le_rfl
  obtain ⟨g', hg'm, N, hN, hNe⟩ := exists_measurable_of_measurable_nullSigma hgN
  refine ⟨g', hg'm, ?_⟩
  have hN' : P N = 0 := hN
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := ae_iff.2 (by simpa using hN')
  filter_upwards [hga, hNae] with ω h1 h2
  rw [h1, hNe ω h2]

/-- The exterior annular Green potential, with the mass input and the circle-average input (b) supplied as the
Frozen Props, and the geometric hypotheses that the unit circle and the closures of the open subsets of `𝔸_{3,6}`
avoid `closure W`. Reduces to `exists_exterior_annulusGreenPotentialSup` (N2) with `hExt` discharged. -/
theorem exists_exterior_annulusGreenPotentialSup_of_frozen {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (γ α₀ : ℝ) (μ : Ω → Measure ℂ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hLQG : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hFr : LQGMassInnerMeasurableFrozen.{u})
    (W : Set ℂ) (hsph : sphere (0 : ℂ) 1 ⊆ (closure W)ᶜ)
    (hWA : ∀ U : Set ℂ, IsOpen U → U ⊆ annulus (0 : ℂ) 3 6 → closure U ⊆ (closure W)ᶜ)
    (hFin : ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ⊤) :
    ∃ G : Ω → ℝ≥0∞,
      Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] G ∧
        (∀ᵐ ω ∂P, G ω = annulusGreenPotentialSup (μ ω) 0 3 6) ∧ ∀ᵐ ω ∂P, G ω ≠ ⊤ := by
  have hBr : WholePlaneCircleAverageLimitFrozen.{u} := wholePlaneCircleAverageLimit_derived.{u}
  have hO : IsOpen (closure W)ᶜ := isClosed_closure.isOpen_compl
  have hψ := hBr Ω P hC hcirc hGFF (closure W)ᶜ 1 0 hO one_pos hsph
  have hExt : ∀ U : Set ℂ, IsOpen U → U ⊆ annulus (0 : ℂ) 3 6 →
      ∃ g : Ω → ℝ≥0∞,
        Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] g ∧
          ∀ᵐ ω ∂P, μ ω U = g ω := by
    intro U hU hUA
    have hUb : Bornology.IsBounded U :=
      Metric.isBounded_ball.subset fun z hz => (hUA hz).1
    exact exists_exterior_mass_version hGFF γ α₀ μ hγ0 hγ2 hα hLQG hFr hO hψ hU hUb (hWA U hU hUA)
  exact exists_exterior_annulusGreenPotentialSup P α₀ hC W μ hExt hFin

/-- Route (ii) form of N2: `hFin` is derived from the base finiteness `hBase` (the Green-potential clause of HB Prop. 2.5,
for the exponent-`0` measure `μ₀`, a named hypothesis) and the singular identity `hSing` (`singular_measure_identity`,
`FirstPass/S11q.lean`, a named hypothesis here). -/
theorem exists_exterior_annulusGreenPotentialSup_of_frozen_base {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (γ α₀ : ℝ) (μ μ₀ : Ω → Measure ℂ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hLQG : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hFr : LQGMassInnerMeasurableFrozen.{u})
    (W : Set ℂ) (hsph : sphere (0 : ℂ) 1 ⊆ (closure W)ᶜ)
    (hWA : ∀ U : Set ℂ, IsOpen U → U ⊆ annulus (0 : ℂ) 3 6 → closure U ⊆ (closure W)ᶜ)
    (hBase : ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ₀ ω) 0 3 6 ≠ ⊤)
    (hSing : ∀ᵐ ω ∂P, μ ω = (μ₀ ω).withDensity (fun z => ENNReal.ofReal (LQGSingularWeight γ α₀ z))) :
    ∃ G : Ω → ℝ≥0∞,
      Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] G ∧
        (∀ᵐ ω ∂P, G ω = annulusGreenPotentialSup (μ ω) 0 3 6) ∧ ∀ᵐ ω ∂P, G ω ≠ ⊤ :=
  exists_exterior_annulusGreenPotentialSup_of_frozen hGFF γ α₀ μ hγ0 hγ2 hα hLQG hFr W hsph hWA
    (ae_annulusGreenPotentialSup_ne_top_of_withDensity P γ α₀ μ₀ μ hBase hSing)

/-- Route (ii) with the base finiteness discharged: `hBase` is derived from HB Prop. 2.5 (`GreenPotentialHolderStmt`,
cited, Draft/Section2.lean) for the exponent-`0` base measure `μ₀` (`h₀`), with the Proposed non-atomicity `hNa0`
(`FirstPass/S11p/BaseFinite.lean`). `hSing` stays a named hypothesis (`singular_measure_identity`, `FirstPass/S11q.lean`). -/
theorem exists_exterior_annulusGreenPotentialSup_of_frozen_holder {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (γ α₀ : ℝ) (μ μ₀ : Ω → Measure ℂ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hLQG : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hFr : LQGMassInnerMeasurableFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u}) (h₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (hNa0 : LQGMeasureNonatomic P γ 0 hC hcirc)
    (W : Set ℂ) (hsph : sphere (0 : ℂ) 1 ⊆ (closure W)ᶜ)
    (hWA : ∀ U : Set ℂ, IsOpen U → U ⊆ annulus (0 : ℂ) 3 6 → closure U ⊆ (closure W)ᶜ)
    (hSing : ∀ᵐ ω ∂P, μ ω = (μ₀ ω).withDensity (fun z => ENNReal.ofReal (LQGSingularWeight γ α₀ z))) :
    ∃ G : Ω → ℝ≥0∞,
      Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] G ∧
        (∀ᵐ ω ∂P, G ω = annulusGreenPotentialSup (μ ω) 0 3 6) ∧ ∀ᵐ ω ∂P, G ω ≠ ⊤ :=
  exists_exterior_annulusGreenPotentialSup_of_frozen_base hGFF γ α₀ μ μ₀ hγ0 hγ2 hα hLQG hFr W hsph hWA
    (ae_annulusGreenPotentialSup_ne_top_base hGFF hγ0 hγ2 h₀ hNa0 hholder) hSing

/-- N2 with the geometric preconditions taken from the buffered pinch geometry `IsBufferedPinchGeometry`: `hsph` and
`hWA` are derived in `FirstPass/S11p/BufferedGeometry.lean` (`closure W ⊆ T ⊆ 𝔸_{1,5}`, `W ⊆ 𝔸_{1,2}`). This is the form
for the pinch second exterior event. -/
theorem exists_exterior_annulusGreenPotentialSup_of_buffered {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (γ α₀ : ℝ) (μ μ₀ : Ω → Measure ℂ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hLQG : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hFr : LQGMassInnerMeasurableFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u}) (h₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (hNa0 : LQGMeasureNonatomic P γ 0 hC hcirc)
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hSing : ∀ᵐ ω ∂P, μ ω = (μ₀ ω).withDensity (fun z => ENNReal.ofReal (LQGSingularWeight γ α₀ z))) :
    ∃ G : Ω → ℝ≥0∞,
      Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] G ∧
        (∀ᵐ ω ∂P, G ω = annulusGreenPotentialSup (μ ω) 0 3 6) ∧ ∀ᵐ ω ∂P, G ω ≠ ⊤ :=
  exists_exterior_annulusGreenPotentialSup_of_frozen_holder hGFF γ α₀ μ μ₀ hγ0 hγ2 hα hLQG hFr hholder h₀ hNa0 W
    (sphere_one_subset_compl_closure_W_of_buffered hgeo)
    (closure_annulus_compl_closure_W_of_buffered hgeo) hSing

/-- N2 with the singular identity discharged: `hSing` is `singular_measure_identity` (`FirstPass/S11q.lean`) for the
exponent-`α₀` LQG measure `μ` and the exponent-`0` base `μ₀`. Named inputs: the Proposed `hWeyl`, `hNa0`, `hNa`
(`LQGMeasureWeylScaling`, `LQGMeasureNonatomic`, pending operator source-check), the cited HB Prop. 2.5 `hholder`, and the
frozen `hFr` (the circle-average limit is derived, `wholePlaneCircleAverageLimit_derived`); the geometry is `IsBufferedPinchGeometry`. -/
theorem exists_exterior_annulusGreenPotentialSup_of_buffered_singular {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (γ α₀ : ℝ) (μ μ₀ : Ω → Measure ℂ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hLQG : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hFr : LQGMassInnerMeasurableFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u}) (h₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (hWeyl : LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hNa0 : LQGMeasureNonatomic P γ 0 hC hcirc) (hNa : LQGMeasureNonatomic P γ α₀ hC hcirc)
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ∃ G : Ω → ℝ≥0∞,
      Measurable[MeasurableSpace.comap (localModConstPairings α₀ hC (closure W)ᶜ) inferInstance] G ∧
        (∀ᵐ ω ∂P, G ω = annulusGreenPotentialSup (μ ω) 0 3 6) ∧ ∀ᵐ ω ∂P, G ω ≠ ⊤ :=
  exists_exterior_annulusGreenPotentialSup_of_buffered hGFF γ α₀ μ μ₀ hγ0 hγ2 hα hLQG hFr hholder h₀ hNa0 hgeo
    (singular_measure_identity P hGFF hγ0 hγ2 hα hWeyl hNa0 hNa h₀ hLQG)

end HarmonicBalls

#print axioms HarmonicBalls.exists_exterior_annulusGreenPotentialSup_of_buffered
#print axioms HarmonicBalls.exists_exterior_annulusGreenPotentialSup_of_buffered_singular

#print axioms HarmonicBalls.exists_exterior_annulusGreenPotentialSup_of_frozen
