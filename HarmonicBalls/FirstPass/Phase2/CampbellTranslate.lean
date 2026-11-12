import HarmonicBalls.FirstPass.Phase2.CampbellInsertionMeasure
import HarmonicBalls.FirstPass.S11c.TranslateField11_7

/-!
# The LQG measure of a translated field

For circle averages `h_r(x)` with vague limit `m` of the regularized measures `ε^{γ²/2} e^{γ h_ε(z)} dz`, the translated
and recentred circle averages `h_r(x + a) - c` have vague limit `e^{-γc} m(· + a)`, the image of `m` under `z ↦ z - a`
scaled by `e^{-γc}` (`IsLQGLimit.translate`). The regularized measures transform exactly, at every scale, by the
translation invariance of Lebesgue measure (`integral_lqgApprox_translate`). For the whole-plane GFF with `c = h_1(a)`
this gives the LQG measure of the normalized translate `h(· + a) - h_1(a)` (`IsLQGMeasureOfField.translate_zero`).
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- Without insertion, the circle averages of the field are those of `h`. -/
theorem fieldCircleAverage_zero_eq (h : ℝ → ℂ → ℝ) : fieldCircleAverage 0 h = h := by
  funext r z
  simp [fieldCircleAverage]

/-- Integrals against the regularized measure `ε^{γ²/2} e^{γ h_ε(z)} dz`. -/
theorem integral_lqgApprox_eq {γ ε : ℝ} (hε : 0 ≤ ε) {h : ℝ → ℂ → ℝ} (hm : Measurable (h ε)) (f : ℂ → ℝ) :
    ∫ z, f z ∂(lqgApprox γ h ε) = ∫ z, ε ^ (γ ^ 2 / 2) * Real.exp (γ * h ε z) * f z := by
  have hF : Measurable fun z : ℂ => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * h ε z)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul hm)))
  unfold lqgApprox
  rw [integral_withDensity_eq_integral_toReal_smul hF (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]

/-- **Translation of the regularized measure.** The regularized measure of the translated and recentred circle
averages `h_r(x + a) - c` integrates `f` as `e^{-γc}` times the regularized measure of `h` integrates `f(· - a)`. -/
theorem integral_lqgApprox_translate {γ ε c : ℝ} (hε : 0 ≤ ε) {h : ℝ → ℂ → ℝ} (hm : Measurable (h ε)) (a : ℂ)
    (f : ℂ → ℝ) :
    ∫ z, f z ∂(lqgApprox γ (fun r x => h r (x + a) - c) ε) =
      Real.exp (-(γ * c)) * ∫ z, f (z - a) ∂(lqgApprox γ h ε) := by
  have hm' : Measurable fun x => h ε (x + a) - c := (hm.comp (measurable_id.add_const a)).sub_const c
  rw [integral_lqgApprox_eq (h := fun r x => h r (x + a) - c) hε hm', integral_lqgApprox_eq hε hm,
    ← integral_add_right_eq_self (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ * h ε z) * f (z - a)) a,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [add_sub_cancel_right]
  rw [show γ * (h ε (z + a) - c) = -(γ * c) + γ * h ε (z + a) by ring, Real.exp_add]
  ring

/-- **The LQG measure of a translated field.** If `m` is the vague limit of the regularized measures of the circle
averages `h`, then `e^{-γc} m(· + a)` (the image of `m` under `z ↦ z - a`, scaled by `e^{-γc}`) is the vague limit for the
translated and recentred circle averages `h_r(x + a) - c`. The dyadic slices `h (2^{-k})` are assumed measurable. -/
theorem IsLQGLimit.translate {γ : ℝ} {h : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (hm : ∀ k : ℕ, Measurable (h (dyadicScale k))) (hL : IsLQGLimit γ h m) (a : ℂ) (c : ℝ) :
    IsLQGLimit γ (fun r x => h r (x + a) - c) (ENNReal.ofReal (Real.exp (-(γ * c))) • m.map (· - a)) where
  isLocallyFiniteMeasure := by
    have := hL.isLocallyFiniteMeasure
    have : IsFiniteMeasureOnCompacts (m.map fun z => z - a) := Measure.IsFiniteMeasureOnCompacts.map m (Homeomorph.subRight a)
    have : IsFiniteMeasureOnCompacts (ENNReal.ofReal (Real.exp (-(γ * c))) • m.map fun z => z - a) :=
      IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top
    infer_instance
  tendsto_integral f hf hfs := by
    have hT : Measurable fun z : ℂ => z - a := measurable_id.sub_const a
    have hfa : Continuous fun z => f (z - a) := hf.comp (continuous_id.sub continuous_const)
    have hfas : HasCompactSupport fun z => f (z - a) := hfs.comp_homeomorph (Homeomorph.subRight a)
    rw [integral_smul_measure, integral_map hT.aemeasurable hf.aestronglyMeasurable,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
    refine ((hL.tendsto_integral _ hfa hfas).const_mul (Real.exp (-(γ * c)))).congr fun k => ?_
    have hk : 0 ≤ dyadicScale k := by unfold dyadicScale; positivity
    exact (integral_lqgApprox_translate hk (hm k) a f).symm

/-- **The LQG measure of the normalized translate of the field.** If `μ₀` is the γ-LQG measure (no insertion) of a
random field whose circle average process is a.s. continuous on `(0, ∞) × ℂ`, then
`e^{-γ h_1(a)} μ₀(· + a)` is the γ-LQG measure of the normalized translate `h(· + a) - h_1(a)` (`translatedCircle`). -/
theorem IsLQGMeasureOfField.translate_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ₀ : Ω → Measure ℂ}
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ))
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ₀) (a : ℂ) :
    IsLQGMeasureOfField P γ 0 (S11c.translatedCircle hcirc a)
      (fun ω => ENNReal.ofReal (Real.exp (-(γ * hcirc ω 1 a))) • (μ₀ ω).map (· - a)) := by
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage 0 (hcirc ω)) (μ₀ ω) := hμ
  show ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage 0 (S11c.translatedCircle hcirc a ω)) _
  filter_upwards [hcont, hμ'] with ω hc hL
  rw [fieldCircleAverage_zero_eq] at hL ⊢
  have hm : ∀ k : ℕ, Measurable (hcirc ω (dyadicScale k)) := fun k => by
    have hk : 0 < dyadicScale k := by unfold dyadicScale; positivity
    exact (hc.comp_continuous (continuous_const.prodMk continuous_id) fun z => ⟨hk, mem_univ z⟩).measurable
  exact hL.translate hm a (hcirc ω 1 a)

end HarmonicBalls
