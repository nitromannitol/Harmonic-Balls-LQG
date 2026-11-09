import HarmonicBalls.FirstPass.S11i.AlphaCanonical
import HarmonicBalls.FirstPass.S11c.TranslateField11_7

/-!
# Translation invariance of the canonical law (fp-S11i-11-13, write-up Step 11)

Mirrors `MixingCanonical.map_dilate_eq`. For a whole-plane GFF `hC` and `z : ℂ` the translated carrier
`translatedPairing hC hcirc z` (S11c: `φ ↦ hC (φ(· - z)) - hcirc 1 z · ∫φ`) has the same canonical law on mean-zero
test functions as `hC`:
* the covariances agree, since the whole-plane covariance changes by one-variable terms `shiftDiff`, which integrate to
  zero against mean-zero test functions (`wholePlaneGFFCov_shift_shift`, S11c);
* the Gaussian laws agree on cylinders (`map_eq_of_gaussian_cov`), hence on the σ-algebra.
Consequence (Step 11, first reduction): Step 9 applied to the translated carrier gives the window frequency of the field
rooted at `z`, with the same limit `P{alphaCanon α hC ∈ E}`.
Source: `notes/fp-gaps/CHATGPT-11-13-proof.md` Step 11 (l.464-487), corrected paper translation invariance modulo constants.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ProbabilityTheory

namespace HarmonicBalls

open HarmonicBalls.S11c

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The whole-plane covariance of two translated pairings of mean-zero test functions equals the untranslated one. -/
theorem wholePlaneGFFCov_pairing_translate {φ ψ : ℂ → ℝ} (hφ : IsTestFunction univ φ)
    (hψ : IsTestFunction univ ψ) (hφ0 : ∫ x, φ x = 0) (hψ0 : ∫ x, ψ x = 0) (z : ℂ) :
    wholePlaneGFFCov (GFFObservable.pairing (fun y => φ (y - z)))
        (GFFObservable.pairing (fun y => ψ (y - z))) =
      wholePlaneGFFCov (GFFObservable.pairing φ) (GFFObservable.pairing ψ) := by
  have h := wholePlaneGFFCov_shift_shift z (o := GFFObservable.pairing φ) (o' := GFFObservable.pairing ψ)
    hφ hψ
  have hmφ : mass (GFFObservable.pairing φ) = 0 := by simpa [mass, GFFObservable.smear] using hφ0
  have hmψ : mass (GFFObservable.pairing ψ) = 0 := by simpa [mass, GFFObservable.smear] using hψ0
  change wholePlaneGFFCov (GFFObservable.pairing (fun y => φ (y - z)))
      (GFFObservable.pairing (fun y => ψ (y - z))) = _ at h
  rw [h, hmφ, hmψ]
  ring

/-- Covariance invariance under translation (mean-zero test functions). -/
theorem cov_pairing_translate (hh : IsWholePlaneGFF P hC hcirc) {φ ψ : ℂ → ℝ} (hφ : IsTestFunction univ φ)
    (hψ : IsTestFunction univ ψ) (hφ0 : ∫ x, φ x = 0) (hψ0 : ∫ x, ψ x = 0) (z : ℂ) :
    cov[fun ω => hC ω (fun y => φ (y - z)), fun ω => hC ω (fun y => ψ (y - z)); P] =
      cov[fun ω => hC ω φ, fun ω => hC ω ψ; P] := by
  rw [cov_pairing_eq hh (isTestFunction_shift hφ z) (isTestFunction_shift hψ z),
    wholePlaneGFFCov_pairing_translate hφ hψ hφ0 hψ0 z, cov_pairing_eq hh hφ hψ]

/-- The finite-dimensional laws of the translated canonical field agree with those of the field. -/
theorem map_translate_eq [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc) (z : ℂ) :
    P.map (fun ω (i : CanonIdx) => hC ω (fun y => i.1 (y - z))) =
      P.map (fun ω (i : CanonIdx) => hC ω i.1) := by
  refine MeasureTheory.ext_of_generate_finite (measurableCylinders fun _ : CanonIdx => ℝ)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
  · intro s hs
    simp only [measurableCylinders, mem_iUnion, mem_singleton_iff, exists_prop] at hs
    obtain ⟨J, B, hB, rfl⟩ := hs
    have hY : Measurable (fun ω (j : J) => hC ω (fun y => j.1.1 (y - z))) :=
      measurable_pi_iff.2 fun j => hh.measurable_pairing _ (isTestFunction_shift j.1.2.1 z)
    have hY0 : Measurable (fun ω (j : J) => hC ω j.1.1) :=
      measurable_pi_iff.2 fun j => hh.measurable_pairing _ j.1.2.1
    have hJ := map_eq_of_gaussian_cov (ι := J) (Y := fun j ω => hC ω j.1.1)
      (Y' := fun j ω => hC ω (fun y => j.1.1 (y - z)))
      (fun j => hh.measurable_pairing _ j.1.2.1)
      (fun j => hh.measurable_pairing _ (isTestFunction_shift j.1.2.1 z))
      (hasGaussianLaw_pairing_family hh (fun j : J => j.1.1) (fun j => j.1.2.1))
      (hasGaussianLaw_pairing_family hh (fun j : J => fun y => j.1.1 (y - z))
        (fun j => isTestFunction_shift j.1.2.1 z))
      (fun j => integral_pairing_eq_zero hh j.1.2.1)
      (fun j => integral_pairing_eq_zero hh (isTestFunction_shift j.1.2.1 z))
      (fun j l => (cov_pairing_translate hh j.1.2.1 l.1.2.1 j.1.2.2 l.1.2.2 z).symm)
    have hm1 : Measurable (fun ω (i : CanonIdx) => hC ω (fun y => i.1 (y - z))) :=
      measurable_pi_iff.2 fun i => hh.measurable_pairing _ (isTestFunction_shift i.2.1 z)
    have hg : Measurable (fun (f : CanonIdx → ℝ) (i : J) => f i.1) :=
      measurable_pi_iff.2 fun i => measurable_pi_apply i.1
    have hcyl : MeasurableSet (cylinder J B) := hg hB
    rw [Measure.map_apply hm1 hcyl, Measure.map_apply (measurable_canonical hh) hcyl]
    show P ((fun ω (j : J) => hC ω (fun y => j.1.1 (y - z))) ⁻¹' B) =
      P ((fun ω (j : J) => hC ω j.1.1) ⁻¹' B)
    rw [← Measure.map_apply hY hB, ← Measure.map_apply hY0 hB, hJ]
  · simp

/-- The canonical law of the translated carrier is the canonical law of the carrier. -/
theorem canonicalLaw_translatedPairing [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc) (z : ℂ) :
    canonicalLaw (translatedPairing hC hcirc z) P = canonicalLaw hC P := by
  have hfun : (fun ω (i : CanonIdx) => translatedPairing hC hcirc z ω i.1) =
      (fun ω (i : CanonIdx) => hC ω (fun y => i.1 (y - z))) := by
    funext ω i
    simp only [translatedPairing, i.2.2, mul_zero, sub_zero]
  unfold canonicalLaw
  rw [hfun]
  exact map_translate_eq hh z

/-- Step 9 transfers along translation: the probability of the canonical event of the translated carrier equals that
of the carrier. -/
theorem prob_alphaCanon_translatedPairing [IsProbabilityMeasure P] (hh : IsWholePlaneGFF P hC hcirc) (α : ℝ)
    (z : ℂ) {E : Set (ModConstTestPairings (Set.univ : Set ℂ))} (hE : MeasurableSet E) :
    P {ω | alphaCanon α (translatedPairing hC hcirc z) ω ∈ E} = P {ω | alphaCanon α hC ω ∈ E} := by
  set E' : Set (ModConstTestPairings (Set.univ : Set ℂ)) := transl (logDrift α) ⁻¹' E with hE'_def
  have hE' : MeasurableSet E' := measurable_transl (logDrift α) hE
  have hX : Measurable (fun ω (i : CanonIdx) => hC ω i.1) := measurable_canonical hh
  have hXz : Measurable (fun ω (i : CanonIdx) => translatedPairing hC hcirc z ω i.1) :=
    measurable_canonical (isWholePlaneGFF_translate hh z)
  have hsetz : (fun ω (i : CanonIdx) => translatedPairing hC hcirc z ω i.1) ⁻¹' E' =
      {ω | alphaCanon α (translatedPairing hC hcirc z) ω ∈ E} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, alphaCanon_eq, hE'_def]
  have hset : (fun ω (i : CanonIdx) => hC ω i.1) ⁻¹' E' = {ω | alphaCanon α hC ω ∈ E} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, alphaCanon_eq, hE'_def]
  have hlaw := canonicalLaw_translatedPairing hh z
  unfold canonicalLaw at hlaw
  rw [← hsetz, ← hset, ← Measure.map_apply hXz hE', ← Measure.map_apply hX hE', hlaw]

end HarmonicBalls
