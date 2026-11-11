import HarmonicBalls.FirstPass.S11ai.RootedInstance
import HarmonicBalls.FirstPass.Frozen.S11aj
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.FirstPass.S11c.TranslateField11_7
import HarmonicBalls.FirstPass.S11i.AlphaCanonical
import HarmonicBalls.FirstPass.S11i.MixingCanonical

/-!
# Transfer of the unit-scale coding clause to the rooted field: `hG` of `RootedInstance.lean`

Proves the hypothesis `hG` of `ae_termwise_of_identification` from the following named inputs:
* `ScaleOneAll`: the unit-scale coding clause (`scale_one_eq` of `FirstPassS11i.CertificateIdentification`,
  `S11i/Identification.lean:52`), read for every whole-plane GFF realization on `Ω`;
* `AffineInvarianceAll`: the universal closure of `WholePlaneGFFAffineInvariance` (`Proposed/LQG.lean:53`);
* `HarmonicBalls.S11aj.CameronMartinGFFReweighting` (frozen, `FirstPass/Frozen/S11aj.lean:31`);
* `PairingScalarLinear (hC ω)`, almost surely: scalar homogeneity of the GFF pairing (not recorded by `IsWholePlaneGFF`).

Chain for a fixed root `z`, admissible `(b, u)` and `n`: translation (affine, `a = 1`, `b = z`), Cameron-Martin shift by `u`
(`P' ∼ P`), dilation by `2^{-n}` under `P'` (affine), identification of the dilated pairing with `dilOp^[n]` of the
insertion-`γ` canonical field (`canonFieldOf_affineDilate`), `ScaleOneAll` under `P'`, and transfer back to `P`.
-/

universe u

namespace FirstPassS11ai

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls
open HarmonicBalls.S11c

/-- Universal closure of `WholePlaneGFFAffineInvariance` (`Proposed/LQG.lean:53`) over all measures and fields on `Ω`. -/
def AffineInvarianceAll (Ω : Type u) [MeasurableSpace Ω] : Prop :=
  ∀ (Q : Measure Ω) (C : Ω → (ℂ → ℝ) → ℝ) (K : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance Q C K

/-- Scalar homogeneity of a pairing functional. The GFF is a random linear functional; `IsWholePlaneGFF` does not record it. -/
def PairingScalarLinear (T : (ℂ → ℝ) → ℝ) : Prop :=
  ∀ (c : ℝ) (ψ : ℂ → ℝ), T (fun y => c * ψ y) = c * T ψ

/-- The unit-scale coding clause for every whole-plane GFF realization `(Q, C, K)` on `Ω`: almost surely the coding event `F`
holds at the insertion-`γ` canonical field exactly when the physical certificate at scale one (radius `1`, centre `0`) holds.
This is `scale_one_eq` of `FirstPassS11i.CertificateIdentification` read for all realizations. -/
def ScaleOneAll (γ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (F : Set (ModConstTestPairings (ball (0 : ℂ) 7)))
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ) : Prop :=
  ∀ (Qm : Measure Ω) (C : Ω → (ℂ → ℝ) → ℝ) (K : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF Qm C K →
    (∀ᵐ ω ∂Qm, PairingScalarLinear (C ω)) →
    ∀ᵐ ω ∂Qm, (ballRestrictPairing 7 (canonFieldOf γ (C ω)) ∈ F ↔
      FirstPassS11i.CertificateEvent (Dμ (canonFieldOf γ (C ω))) (Dd (canonFieldOf γ (C ω)))
        Ostar U V W T Q' Q η M 1 0)

theorem pairingScalarLinear_translatedPairing {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (z : ℂ) (ω : Ω) (h : PairingScalarLinear (hC ω)) :
    PairingScalarLinear (translatedPairing hC hcirc z ω) := by
  intro c ψ
  have h1 := h c (fun y => ψ (y - z))
  have h2 : ∫ x, c * ψ x = c * ∫ x, ψ x := integral_const_mul c ψ
  simp only [translatedPairing] at h1 ⊢
  rw [h2, h1]
  ring

theorem pairingScalarLinear_addFunPairing (T : (ℂ → ℝ) → ℝ) (f : ℂ → ℝ) (h : PairingScalarLinear T) :
    PairingScalarLinear (addFunPairing T f) := by
  intro c ψ
  have h2 : ∫ x, f x * (c * ψ x) = c * ∫ x, f x * ψ x := by
    rw [← integral_const_mul]
    congr 1
    ext x
    ring
  simp only [addFunPairing]
  rw [h c ψ, h2]
  ring

theorem pairingScalarLinear_affineDilate (n : ℕ) (T : (ℂ → ℝ) → ℝ) (hT : PairingScalarLinear T) (K : ℝ) :
    PairingScalarLinear (fun φ => (‖((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ)‖ ^ 2)⁻¹ *
        T (fun y => φ ((y - 0) / ((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ))) - K * ∫ x, φ x) := by
  intro c ψ
  have h1 := hT c (fun y => ψ ((y - 0) / ((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ)))
  have h2 : ∫ x, c * ψ x = c * ∫ x, ψ x := integral_const_mul c ψ
  simp only at h1 ⊢
  rw [h2, h1]
  ring

theorem isWholePlaneGFF_translatedPairing {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hAff : AffineInvarianceAll Ω)
    (hh : IsWholePlaneGFF P hC hcirc) (z : ℂ) :
    IsWholePlaneGFF P (translatedPairing hC hcirc z) (translatedCircle hcirc z) := by
  have h := hAff P hC hcirc hh 1 one_ne_zero z
  have h' : IsWholePlaneGFF P (fun ω φ => hC ω (fun y => φ (y - z)) - hcirc ω 1 z * ∫ x, φ x)
      (fun ω r w => hcirc ω r (w + z) - hcirc ω 1 z) := by
    simpa using h
  exact h'

/-- The iterated dilation preserves `∫ · log|·|` on mean-zero test functions. -/
theorem integral_dilateTest_iter_mul_log (n : ℕ) :
    ∀ {k : ℂ → ℝ}, IsTestFunction univ k → ∫ z, k z = 0 →
      ∫ y, dilateTest n k y * Real.log ‖y‖ = ∫ z, k z * Real.log ‖z‖ := by
  induction n with
  | zero =>
    intro k _ _
    simp [dilateTest]
  | succ n ih =>
    intro k hk hmean
    rw [← dilateTest_one_comp n k,
      ih (isTestFunction_dilateTest hk 1) ((integral_dilateTest 1 k).trans hmean)]
    exact integral_dilateTest_one_mul_log hk hmean

theorem norm_dilScale (n : ℕ) : ‖((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ)‖ = ((2 : ℝ) ^ n)⁻¹ := by
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]

theorem sq_inv_dilScale (n : ℕ) : ((((2 : ℝ) ^ n)⁻¹) ^ 2)⁻¹ = (4 : ℝ) ^ n := by
  rw [inv_pow, inv_inv, ← pow_mul, mul_comm, pow_mul]
  norm_num

/-- The affine dilation of a scalar-homogeneous pairing has insertion-`γ` canonical field `dilOp^[n]` of the original. -/
theorem canonFieldOf_affineDilate (γ : ℝ) (n : ℕ) (T : (ℂ → ℝ) → ℝ) (hT : PairingScalarLinear T) (K : ℝ) :
    canonFieldOf γ (fun φ => (‖((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ)‖ ^ 2)⁻¹ *
        T (fun y => φ ((y - 0) / ((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ))) - K * ∫ x, φ x) =
      dilOp^[n] (canonFieldOf γ T) := by
  funext i
  rw [iterate_dilOp]
  have hy : ∀ y : ℂ, (y - 0) / ((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) = ((2 : ℝ) ^ n) • y := by
    intro y
    rw [sub_zero, Complex.real_smul]
    push_cast
    field_simp
  have hT' : T (dilateTest n i.1) = (4 : ℝ) ^ n * T (fun y => i.1 (((2 : ℝ) ^ n) • y)) :=
    hT ((4 : ℝ) ^ n) (fun y => i.1 (((2 : ℝ) ^ n) • y))
  have hlog := integral_dilateTest_iter_mul_log n i.2.1 i.2.2
  have hK : ∫ x, i.1 x = 0 := i.2.2
  simp only [canonFieldOf, fieldPairing, hy, norm_dilScale, sq_inv_dilScale]
  rw [hT', hlog, hK]
  ring

/-- **`hG` for a fixed root `z` and admissible shift `u`** (`RootedInstance.lean`, `hG`): almost surely, for every `n`, the
unit-scale certificate of the dilated, translated, `u`-shifted canonical field agrees with the coding event `F`. -/
theorem ae_coding_rooted_of_scaleOne
    {γ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))}
    {Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ}
    {Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ}
    {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ}
    (hAff : AffineInvarianceAll Ω) (hCMRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u})
    (hScale : ScaleOneAll γ Ω F Dμ Dd Ostar U V W T Q' Q η M)
    (hh : IsWholePlaneGFF P hC hcirc) (hhom : ∀ᵐ ω ∂P, PairingScalarLinear (hC ω))
    (z : ℂ) (u : ℂ → ℝ) (hu_sm : ContDiff ℝ (⊤ : ℕ∞) u) (hu_cs : HasCompactSupport u)
    (hu_avg : Real.circleAverage u 0 1 = 0) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      (FirstPassS11i.CertificateEvent
          (Dμ (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
          (Dd (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
          Ostar U V W T Q' Q η M 1 0 ↔
        ballRestrictPairing 7 (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))) ∈ F) := by
  have hH := isWholePlaneGFF_translatedPairing hAff hh z
  obtain ⟨P', hP'a, hP'b, hG⟩ :=
    hCMRew Ω P (translatedPairing hC hcirc z) (translatedCircle hcirc z) hH u hu_sm hu_cs hu_avg
  have hhomP : ∀ᵐ ω ∂P, PairingScalarLinear (addFunPairing (translatedPairing hC hcirc z ω) u) :=
    hhom.mono fun ω h => pairingScalarLinear_addFunPairing _ u
      (pairingScalarLinear_translatedPairing hC hcirc z ω h)
  have hhomP' : ∀ᵐ ω ∂P', PairingScalarLinear (addFunPairing (translatedPairing hC hcirc z ω) u) :=
    hP'a.ae_le hhomP
  have hstep : ∀ n : ℕ, ∀ᵐ ω ∂P,
      (FirstPassS11i.CertificateEvent
          (Dμ (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
          (Dd (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
          Ostar U V W T Q' Q η M 1 0 ↔
        ballRestrictPairing 7 (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))) ∈ F) := by
    intro n
    have ha : ((((2 : ℝ) ^ n)⁻¹ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (by positivity)
    have hG' := hAff P' _ _ hG _ ha 0
    have hS := hScale P' _ _ hG'
      (hhomP'.mono fun ω hω => pairingScalarLinear_affineDilate n _ hω _)
    have hboth := hS.and hhomP'
    refine hP'b.ae_le ?_
    filter_upwards [hboth] with ω hω
    obtain ⟨h1, h2⟩ := hω
    rw [canonFieldOf_affineDilate γ n _ h2 _] at h1
    exact h1.symm
  exact ae_all_iff.2 hstep

/-- **`hG` of `ae_termwise_of_identification`**, from the unit-scale coding clause, the affine invariance, and the
Cameron-Martin reweighting, for every root (`ae_of_all`). -/
theorem hG_of_scaleOne
    {γ α₀ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))}
    {Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ}
    {Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ}
    {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ} (μ : Measure ℂ) (A : Set ℂ)
    (hAff : AffineInvarianceAll Ω) (hCMRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u})
    (hScale : ScaleOneAll γ Ω F Dμ Dd Ostar U V W T Q' Q η M)
    (hh : IsWholePlaneGFF P hC hcirc) (hhom : ∀ᵐ ω ∂P, PairingScalarLinear (hC ω)) :
    ∀ᵐ z ∂μ, z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P, ∀ n : ℕ,
      (FirstPassS11i.CertificateEvent
          (Dμ (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
          (Dd (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
          Ostar U V W T Q' Q η M 1 0 ↔
        ballRestrictPairing 7 (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))) ∈ F) :=
  ae_of_all μ fun z _ b u hadm => by
    obtain ⟨-, -, -, h4, h5, h6, -⟩ := hadm
    exact ae_coding_rooted_of_scaleOne hAff hCMRew hScale hh hhom z u h4 h5 h6

end FirstPassS11ai
