import HarmonicBalls.FirstPass.Phase2.CampbellTranslate
import HarmonicBalls.FirstPass.Phase2.CampbellMarkedExt
import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# The rooted (Campbell) identity on a translated unit disc

For a whole-plane GFF `h` (pairings `hC`, circle averages `hcirc`) and its `α = 0` LQG measure `μ₀`, the normalized
translate `h' = h(· + a) - h_1(a)` is again a whole-plane GFF (`S11c.isWholePlaneGFF_translate`) with LQG measure
`e^{-γ h_1(a)} μ₀(· + a)` (`IsLQGMeasureOfField.translate_zero`). The marked Duplantier-Miller-Sheffield identity
(Lemma A.10, whole-plane clause, `dmsLemmaA10WholePlaneMarkedSub_holds`) for `h'` on the unit disc, with a test that
reads the restriction of `h - α₀ log|·|` modulo constants to a set `D` at the root `z + a`, becomes an identity on the
disc `B_1(a)`:

`E[e^{-γ h_1(a)} ∫_{B_1(a)} 1_S(z, (h - α₀ log|·|)|_D mod ℝ) dμ₀(z)]
  = ∫_{B_1(a)} P((z, (h - α₀ log|·| + f_{z-a}(· - a))|_D mod ℝ) ∈ S) dz`,

with `f_w = dmsShift γ w` the shift `-γ log|· - w| + γ log max(|·|, 1)` of Lemma A.10. Only mean-zero test functions are
read, so the additive constants (`h_1(a)` and the constant of Lemma A.10) drop out.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

namespace CampbellObsTransfer

open CampbellKernel

attribute [local instance] markObsSigma

/-- Mean-zero test functions supported in `D`: the index set of the restriction of a field to `D` modulo constants. -/
abbrev MeanZeroTest (D : Set ℂ) : Type := {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0}

/-- The marked observation of the translated field: a pairing functional `T` of `h' = h(· + a) - c` and a root `w`
give the root `w + a` and the pairings `φ ↦ (h', φ(· + a)) - α₀ ∫ φ log|·|` of `h - α₀ log|·|` with the mean-zero test
functions supported in `D`. -/
noncomputable def transObs (α₀ : ℝ) (D : Set ℂ) (a : ℂ) (q : MarkObs) : ℂ × (MeanZeroTest D → ℝ) :=
  (q.2 + a, fun φ => q.1 (fun y => φ.1 (y + a)) - α₀ * ∫ x, φ.1 x * Real.log ‖x‖)

theorem isTestFunction_add_right {D : Set ℂ} {φ : ℂ → ℝ} (hφ : IsTestFunction D φ) (a : ℂ) :
    IsTestFunction univ (fun y => φ (y + a)) := by
  simpa only [sub_neg_eq_add] using S11c.isTestFunction_shift (φ := φ) ⟨hφ.1, hφ.2.1, subset_univ _⟩ (-a)

theorem measurable_transObs (α₀ : ℝ) (D : Set ℂ) (a : ℂ) : Measurable (transObs α₀ D a) := by
  show Measurable fun q : MarkObs => (q.2 + a,
    fun φ : MeanZeroTest D => q.1 (fun y => φ.1 (y + a)) - α₀ * ∫ x, φ.1 x * Real.log ‖x‖)
  refine (measurable_snd.add_const a).prodMk (measurable_pi_iff.mpr fun φ => ?_)
  exact (measurable_eval_markObs (isTestFunction_add_right φ.2.1 a)).sub_const _

/-- A mean-zero test function translated by `a` still has integral zero. -/
theorem integral_add_right_meanZero {D : Set ℂ} (φ : MeanZeroTest D) (a : ℂ) : ∫ y, φ.1 (y + a) = 0 :=
  (integral_add_right_eq_self (μ := volume) (fun y => φ.1 y) a).trans φ.2.2

/-- The observation of the translated field at the root `z - a` is the marked observation of the field at `z`. -/
theorem transObs_translatedPairing {Ω : Type*} (α₀ : ℝ) (D : Set ℂ) (a : ℂ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) (z : ℂ) :
    transObs α₀ D a (S11c.translatedPairing hC hcirc a ω, z - a) = campbellMarkedObs α₀ D (hC ω) z := by
  refine Prod.ext (sub_add_cancel z a) (funext fun φ => ?_)
  have h2 := integral_add_right_meanZero φ a
  simp only [transObs, campbellMarkedObs, fieldPairing, S11c.translatedPairing, sub_add_cancel, h2, mul_zero,
    sub_zero]

/-- The observation of the Lemma A.10 output for the translated field at the root `z - a`. -/
theorem transObs_dmsShiftedPairing {Ω : Type*} (γ α₀ : ℝ) (D : Set ℂ) (a : ℂ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) (w : ℂ) (c : ℝ) (z : ℂ) :
    transObs α₀ D a (dmsShiftedPairing γ w (S11c.translatedPairing hC hcirc a ω) c, z - a)
      = (z, fun φ : MeanZeroTest D => fieldPairing α₀ (hC ω) φ.1 + ∫ y, dmsShift γ w (y - a) * φ.1 y) := by
  refine Prod.ext (sub_add_cancel z a) (funext fun φ => ?_)
  have h2 := integral_add_right_meanZero φ a
  have h3 := integral_add_right_eq_self (μ := volume) (fun y => dmsShift γ w (y - a) * φ.1 y) a
  simp only [add_sub_cancel_right] at h3
  simp only [transObs, dmsShiftedPairing, fieldPairing, S11c.translatedPairing, sub_add_cancel, h2, h3, mul_zero,
    sub_zero, add_zero]
  ring

/-- Change of variables `w = z - a` in a Lebesgue integral over the unit disc. -/
theorem setLIntegral_ball_zero_eq (a : ℂ) (F : ℂ → ℝ≥0∞) :
    ∫⁻ w in ball (0 : ℂ) 1, F w = ∫⁻ z in ball a 1, F (z - a) := by
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball,
    ← lintegral_sub_right_eq_self _ a]
  refine lintegral_congr fun z => ?_
  simp only [indicator, mem_ball, dist_eq_norm, sub_zero]

/-- **The rooted identity on the translated disc `B_1(a)`.** For a whole-plane GFF, `0 < γ < 2`, its `α = 0` LQG
measure `μ₀`, a point `a` and a measurable set `S` of marked restrictions to `D` modulo constants,
`E[e^{-γ h_1(a)} ∫_{B_1(a)} 1_S(z, (h - α₀ log|·|)|_D) dμ₀(z)]` equals the Lebesgue integral over `z ∈ B_1(a)` of the
probability that `(z, (h - α₀ log|·| + f_{z-a}(· - a))|_D)` lies in `S`, where `f_w = dmsShift γ w`. -/
theorem lintegral_translate_campbell {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ₀ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ₀) (α₀ : ℝ) (D : Set ℂ) (a : ℂ)
    {S : Set (ℂ × (MeanZeroTest D → ℝ))} (hS : MeasurableSet S) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-(γ * hcirc ω 1 a))) *
        ∫⁻ z in ball a 1, S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ D (hC ω) z) ∂(μ₀ ω) ∂P
      = ∫⁻ z in ball a 1, ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞))
          (z, fun φ : MeanZeroTest D => fieldPairing α₀ (hC ω) φ.1 + ∫ y, dmsShift γ (z - a) (y - a) * φ.1 y)
          ∂P ∂volume := by
  set Ψ : MarkObs → ℝ≥0∞ := fun q => S.indicator (fun _ => (1 : ℝ≥0∞)) (transObs α₀ D a q) with hΨdef
  have hΨ : Measurable Ψ := (measurable_const.indicator hS).comp (measurable_transObs α₀ D a)
  have hT1 := dmsLemmaA10WholePlaneMarkedSub_holds P γ (S11c.translatedPairing hC hcirc a)
    (S11c.translatedCircle hcirc a)
    (fun ω => ENNReal.ofReal (Real.exp (-(γ * hcirc ω 1 a))) • (μ₀ ω).map (· - a))
    (S11c.isWholePlaneGFF_translate hh a)
    (IsLQGMeasureOfField.translate_zero hh.ae_continuousOn_circle hμ a) hγ0 hγ2 Ψ hΨ
  have hL : ∀ ω, ∫⁻ w in ball (0 : ℂ) 1, Ψ (S11c.translatedPairing hC hcirc a ω, w)
      ∂(ENNReal.ofReal (Real.exp (-(γ * hcirc ω 1 a))) • (μ₀ ω).map (· - a))
      = ENNReal.ofReal (Real.exp (-(γ * hcirc ω 1 a))) *
        ∫⁻ z in ball a 1, S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ D (hC ω) z) ∂(μ₀ ω) := by
    intro ω
    have hsec : Measurable fun w => Ψ (S11c.translatedPairing hC hcirc a ω, w) :=
      hΨ.comp (measurable_const.prodMk measurable_id)
    rw [Measure.restrict_smul, lintegral_smul_measure,
      setLIntegral_map measurableSet_ball hsec (measurable_sub_const a)]
    have hpre : (fun z : ℂ => z - a) ⁻¹' ball 0 1 = ball a 1 := by
      ext z
      simp only [mem_preimage, mem_ball, dist_eq_norm, sub_zero]
    rw [hpre]
    congr 1
    refine lintegral_congr fun z => ?_
    simp only [hΨdef, transObs_translatedPairing]
  have hR : ∀ w, ∫⁻ ω, Ψ (dmsShiftedPairing γ w (S11c.translatedPairing hC hcirc a ω)
      (S11c.translatedCircle hcirc a ω 1 0), w) ∂P
      = ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞))
          (w + a, fun φ : MeanZeroTest D => fieldPairing α₀ (hC ω) φ.1 + ∫ y, dmsShift γ w (y - a) * φ.1 y) ∂P := by
    intro w
    refine lintegral_congr fun ω => ?_
    have h := transObs_dmsShiftedPairing γ α₀ D a hC hcirc ω w (S11c.translatedCircle hcirc a ω 1 0) (w + a)
    rw [add_sub_cancel_right] at h
    simp only [hΨdef, h]
  simp only [hL] at hT1
  rw [hT1, setLIntegral_ball_zero_eq a]
  refine lintegral_congr fun z => ?_
  rw [hR (z - a), sub_add_cancel]

end CampbellObsTransfer

end HarmonicBalls
