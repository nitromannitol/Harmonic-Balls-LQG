import HarmonicBalls.FirstPass.Phase2.CampbellObsTransfer
import HarmonicBalls.FirstPass.Phase2.CameronMartinLipschitzShiftHolds
import HarmonicBalls.FirstPass.S11c.ShiftCM11_7
import HarmonicBalls.FirstPass.S11i.DilationMixing

/-!
# Cameron-Martin step of the rooted (Campbell) identity on a translated disc

The rooted identity on `B_1(a)` (`CampbellObsTransfer.lintegral_translate_campbell`) produces at the root `z` the field
`h - α₀ log|·| + f_{z-a}(· - a)`, `f_w = dmsShift γ w`, read on the mean-zero test functions supported in a bounded set
`D`. Since `f_{z-a}(y - a) = -γ log|y - z| + γ log max(|y - a|, 1)`, this differs from the Campbell reference field
`h - α₀ log|·| - γ log|· - z| + γ log max(1, |·|)` (`campbellReferenceObs`) by the function
`γ (log max(1, |· - a|) - log max(1, |·|))`, which on `D` agrees with a locally Lipschitz compactly supported function.
The Cameron-Martin theorem for such shifts (`cameronMartinLocallyLipschitzShiftAbsCont_holds`) then shows: an event of
marked restrictions that is null for the reference field at `z` is null for the shifted field at `z`.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

namespace CampbellShiftCM

open CampbellObsTransfer

/-- The probability of a measurable event of a measurable observation, as a lintegral of its indicator. -/
theorem lintegral_indicator_comp {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (P : Measure Ω)
    {f : Ω → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    ∫⁻ ω, s.indicator (fun _ => (1 : ℝ≥0∞)) (f ω) ∂P = P {ω | f ω ∈ s} := by
  rw [show {ω | f ω ∈ s} = f ⁻¹' s from rfl, ← lintegral_indicator_one (hf hs)]
  exact lintegral_congr fun ω => rfl

/-- The correction `y ↦ γ (log max(1, |y - a|) - log max(1, |y|)) χ(y)` with a cut-off `χ`. -/
noncomputable def dmsCorrection (γ : ℝ) (a : ℂ) (χ : ℂ → ℝ) (y : ℂ) : ℝ :=
  γ * (Real.log (max 1 ‖y - a‖) - Real.log (max 1 ‖y‖)) * χ y

theorem locallyLipschitz_dmsCorrection (γ : ℝ) (a : ℂ) {χ : ℂ → ℝ} (hχ : LocallyLipschitz χ) :
    LocallyLipschitz (dmsCorrection γ a χ) := by
  have h1 := S11c.log_max_lipschitz (ε := 1) one_pos
  have hsub : LipschitzWith 1 (fun y : ℂ => y - a) := LipschitzWith.of_dist_le_mul fun x y => by
    simp only [NNReal.coe_one, one_mul, dist_sub_right, le_refl]
  have hL : LipschitzWith _ (fun y : ℂ => Real.log (max 1 ‖y - a‖) - Real.log (max 1 ‖y‖)) :=
    (h1.comp hsub).sub h1
  exact S11c.locallyLipschitz_mul_real
    (S11c.locallyLipschitz_mul_real (LocallyLipschitz.const γ) hL.locallyLipschitz) hχ

/-- **Cameron-Martin step.** For a whole-plane GFF, a bounded set `D`, points `a, z` and a measurable set `S` of marked
restrictions to `D` modulo constants: if the Campbell reference observation at `z` lies in `S` with probability zero,
then so does the observation `(z, (h - α₀ log|·| + f_{z-a}(· - a))|_D)` of the Lemma A.10 output on `B_1(a)`. -/
theorem lintegral_dmsShifted_eq_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) (γ α₀ : ℝ) {D : Set ℂ}
    (hD : Bornology.IsBounded D) (a z : ℂ) {S : Set (ℂ × (MeanZeroTest D → ℝ))} (hS : MeasurableSet S)
    (h0 : ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellReferenceObs γ α₀ D (hC ω) z) ∂P = 0) :
    ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞))
        (z, fun φ : MeanZeroTest D => fieldPairing α₀ (hC ω) φ.1 + ∫ y, dmsShift γ (z - a) (y - a) * φ.1 y) ∂P
      = 0 := by
  obtain ⟨r, hr⟩ := hD.subset_closedBall 0
  obtain ⟨χ, hcd, hcs, -, hone⟩ :=
    S11c.exists_cut_ball (0 : ℂ) (r := |r| + 1) (R := |r| + 2) (by positivity) (by linarith)
  have hDχ : ∀ y ∈ D, χ y = 1 := fun y hy =>
    hone y (closedBall_subset_closedBall (by linarith [le_abs_self r]) (hr hy))
  set g := dmsCorrection γ a χ with hgdef
  have hgL : LocallyLipschitz g := locallyLipschitz_dmsCorrection γ a hcd.locallyLipschitz
  have hgc : HasCompactSupport g := by
    have : g = (fun y => γ * (Real.log (max 1 ‖y - a‖) - Real.log (max 1 ‖y‖))) * χ := rfl
    rw [this]
    exact hcs.mul_left
  -- the deterministic part of the reference observation
  set d : MeanZeroTest D → ℝ := fun φ =>
    -(α₀ * ∫ x, φ.1 x * Real.log ‖x‖) - γ * ∫ w, (Real.log ‖w - z‖ - Real.log (max 1 ‖w‖)) * φ.1 w with hd
  set S' : Set (MeanZeroTest D → ℝ) := (fun u => (z, fun φ => u φ + d φ)) ⁻¹' S with hS'def
  have hS' : MeasurableSet S' :=
    (measurable_const.prodMk (measurable_pi_iff.mpr fun φ => (measurable_pi_apply φ).add_const _)) hS
  have hU : Measurable fun ω => fun φ : MeanZeroTest D => hC ω φ.1 :=
    measurable_pi_iff.mpr fun φ => hh.measurable_pairing φ.1 ⟨φ.2.1.1, φ.2.1.2.1, subset_univ _⟩
  have hUg : Measurable fun ω => fun φ : MeanZeroTest D => hC ω φ.1 + ∫ x, φ.1 x * g x :=
    measurable_pi_iff.mpr fun φ =>
      (hh.measurable_pairing φ.1 ⟨φ.2.1.1, φ.2.1.2.1, subset_univ _⟩).add_const _
  -- the reference observation is `(z, u + d)`
  have href : ∀ ω, S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellReferenceObs γ α₀ D (hC ω) z)
      = S'.indicator (fun _ => (1 : ℝ≥0∞)) (fun φ : MeanZeroTest D => hC ω φ.1) := by
    intro ω
    have : campbellReferenceObs γ α₀ D (hC ω) z = (z, fun φ : MeanZeroTest D => hC ω φ.1 + d φ) := by
      refine Prod.ext rfl (funext fun φ => ?_)
      simp only [campbellReferenceObs, fieldPairing, hd]
      ring
    rw [this]
    rfl
  have h0' : P {ω | (fun φ : MeanZeroTest D => hC ω φ.1) ∈ S'} = 0 := by
    rw [← lintegral_indicator_comp P hU hS', ← h0]
    exact lintegral_congr fun ω => (href ω).symm
  have hCM := cameronMartinLocallyLipschitzShiftAbsCont_holds Ω P hC hcirc D g hh hgL hgc S' hS' h0'
  -- the shifted observation is `(z, u + ∫ φ g + d)`
  have hshift : ∀ (ω : Ω) (φ : MeanZeroTest D),
      fieldPairing α₀ (hC ω) φ.1 + ∫ y, dmsShift γ (z - a) (y - a) * φ.1 y
        = (hC ω φ.1 + ∫ x, φ.1 x * g x) + d φ := by
    intro ω φ
    obtain ⟨R, hR⟩ : ∃ R, ∀ y, φ.1 y ≠ 0 → ‖y‖ ≤ R :=
      ⟨r, fun y hy => mem_closedBall_zero_iff.mp (hr (φ.2.1.2.2 (subset_tsupport _ hy)))⟩
    have hφc : Continuous φ.1 := φ.2.1.1.continuous
    have hlogc : Continuous fun y : ℂ => Real.log (max 1 ‖y‖) := (S11c.log_max_lipschitz one_pos).continuous
    have h1 : Integrable fun y => φ.1 y * Real.log ‖y - z‖ :=
      integrable_mul_log_norm_sub ⟨φ.2.1.1, φ.2.1.2.1, subset_univ _⟩ hR z
    have h2 : Integrable fun y => φ.1 y * Real.log (max 1 ‖y‖) :=
      (hφc.mul hlogc).integrable_of_hasCompactSupport φ.2.1.2.1.mul_right
    have hB : Integrable fun y => φ.1 y * g y :=
      (hφc.mul hgL.continuous).integrable_of_hasCompactSupport φ.2.1.2.1.mul_right
    have hA : Integrable fun y => -γ * ((Real.log ‖y - z‖ - Real.log (max 1 ‖y‖)) * φ.1 y) :=
      ((h1.sub h2).const_mul (-γ)).congr (ae_of_all _ fun y => by simp only [Pi.sub_apply]; ring)
    have hpt : ∀ y, dmsShift γ (z - a) (y - a) * φ.1 y
        = φ.1 y * g y + -γ * ((Real.log ‖y - z‖ - Real.log (max 1 ‖y‖)) * φ.1 y) := by
      intro y
      by_cases hy : φ.1 y = 0
      · simp only [hy, mul_zero, zero_mul, add_zero]
      · have hχy : χ y = 1 := hDχ y (φ.2.1.2.2 (subset_tsupport _ hy))
        simp only [dmsShift, hgdef, dmsCorrection, hχy, sub_sub_sub_cancel_right, max_comm ‖y - a‖ 1]
        ring
    rw [integral_congr_ae (ae_of_all _ hpt), integral_add hB hA, integral_const_mul]
    simp only [fieldPairing, hd]
    ring
  have hobs : ∀ ω, S.indicator (fun _ => (1 : ℝ≥0∞))
      (z, fun φ : MeanZeroTest D => fieldPairing α₀ (hC ω) φ.1 + ∫ y, dmsShift γ (z - a) (y - a) * φ.1 y)
      = S'.indicator (fun _ => (1 : ℝ≥0∞)) (fun φ : MeanZeroTest D => hC ω φ.1 + ∫ x, φ.1 x * g x) := by
    intro ω
    have : (z, fun φ : MeanZeroTest D => fieldPairing α₀ (hC ω) φ.1 + ∫ y, dmsShift γ (z - a) (y - a) * φ.1 y)
        = (z, fun φ : MeanZeroTest D => (hC ω φ.1 + ∫ x, φ.1 x * g x) + d φ) :=
      Prod.ext rfl (funext fun φ => hshift ω φ)
    rw [this]
    rfl
  rw [lintegral_congr hobs, lintegral_indicator_comp P hUg hS']
  exact hCM

end CampbellShiftCM

end HarmonicBalls
