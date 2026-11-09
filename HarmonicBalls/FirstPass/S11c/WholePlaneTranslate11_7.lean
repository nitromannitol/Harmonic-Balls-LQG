import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proofs.Sec8.CircleLogPotential
import HarmonicBalls.Steps.Sec11.PairingCovarianceLinearity

/-!
# Translation identity of the normalized whole-plane kernel (Lemma 11.7, operator route Q1)

Deterministic part of the translation `h ↦ h(· + z) - h_1(z)` of the whole-plane GFF. For an observable `o`
let `shiftObs z o` be the observable with smearing `f ↦ o.smear (f (· + z))`, let `b = circle 1 z`, let
`L = wholePlaneNormalization = log max(|·|,1)`, `m = circleAverage L z 1` and `a(x) = L(x+z) - L(x)`
(`shiftDiff z x`). With `W = wholePlaneGFFCov` and `mass o = o.smear 1` (`∫ φ` for a pairing, `1` for a circle):

* `W(shift o, shift o') = W(o,o') + mass o' · o.smear a + mass o · o'.smear a`   (`wholePlaneGFFCov_shift_shift`)
* `W(shift o, b) = o.smear a + m · mass o`                                        (`wholePlaneGFFCov_shift_circle`)
* `W(b, b) = 2m`                                                                  (`wholePlaneGFFCov_circle_circle`)

Hence `W(shift o, shift o') - mass o' W(shift o, b) - mass o W(shift o', b) + mass o mass o' W(b,b) = W(o,o')`
(`wholePlaneGFFCov_shift_combo`). The proof uses the closed form of the circle average of the kernel
(Proofs/Sec8/CircleLogPotential.lean, `circleAverage_wholePlaneCov_eq`) and a.e. identity off the diagonal
(`wholePlaneCov (x+z) (y+z) = wholePlaneCov x y + a x + a y` for `x ≠ y`). The probabilistic part is in
TranslateField11_7.lean.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace HarmonicBalls.S11c

open HarmonicBalls

/-- The observable of the translated field `x ↦ h(x + z)`: its smearing is `f ↦ o.smear (f (· + z))`. -/
def shiftObs (z : ℂ) : GFFObservable → GFFObservable
  | .pairing φ => .pairing (fun y => φ (y - z))
  | .circle r x => .circle r (x + z)

/-- `a(x) = L(x + z) - L(x)` with `L = wholePlaneNormalization`. -/
noncomputable def shiftDiff (z x : ℂ) : ℝ :=
  wholePlaneNormalization (x + z) - wholePlaneNormalization x

/-- The mass `o.smear 1` of an observable: `∫ φ` for a pairing, `1` for a circle average. -/
noncomputable def mass (o : GFFObservable) : ℝ := o.smear (fun _ => 1)

lemma continuous_shiftDiff (z : ℂ) : Continuous (shiftDiff z) := by
  unfold shiftDiff
  exact (continuous_wholePlaneNormalization.comp (continuous_id.add continuous_const)).sub
    continuous_wholePlaneNormalization

lemma isTestFunction_shift {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) (z : ℂ) :
    IsTestFunction univ (fun y => φ (y - z)) := by
  refine ⟨hφ.1.comp (contDiff_id.sub contDiff_const), ?_, subset_univ _⟩
  have h := hφ.2.1.comp_homeomorph (Homeomorph.subRight z)
  simpa [Function.comp_def, Homeomorph.subRight] using h

lemma shiftObs_isAdmissible (z : ℂ) {o : GFFObservable} (ho : o.IsAdmissible) :
    (shiftObs z o).IsAdmissible := by
  cases o with
  | pairing φ => exact isTestFunction_shift ho z
  | circle r x => exact ho

/-- Circle averages are invariant under translation of the centre and of the function. -/
lemma circleAverage_comp_add_right (F : ℂ → ℝ) (w z : ℂ) (s : ℝ) :
    Real.circleAverage (fun y => F (y + z)) w s = Real.circleAverage F (w + z) s := by
  unfold Real.circleAverage circleMap
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  congr 1
  ring

lemma smear_shiftObs (z : ℂ) (o : GFFObservable) (f : ℂ → ℝ) :
    (shiftObs z o).smear f = o.smear (fun x => f (x + z)) := by
  cases o with
  | pairing φ =>
    simp only [shiftObs, GFFObservable.smear]
    rw [← integral_add_right_eq_self (fun y => φ (y - z) * f y) z]
    simp
  | circle r x =>
    simp only [shiftObs, GFFObservable.smear]
    exact (circleAverage_comp_add_right f x z r).symm

lemma smear_const (o : GFFObservable) (c : ℝ) : o.smear (fun _ => c) = c * mass o := by
  unfold mass
  cases o with
  | pairing φ => simp only [GFFObservable.smear]; rw [← integral_const_mul]; congr 1; ext; ring
  | circle r x => simp only [GFFObservable.smear, Real.circleAverage_const, mul_one]

lemma smear_mass_circle (r : ℝ) (x : ℂ) : mass (.circle r x) = 1 := by
  simp [mass, GFFObservable.smear, Real.circleAverage_const]

lemma smear_add_of_continuous (o : GFFObservable) (ho : o.IsAdmissible) {f g : ℂ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    o.smear (fun x => f x + g x) = o.smear f + o.smear g := by
  cases o with
  | pairing φ =>
    have hφ : IsTestFunction univ φ := ho
    simp only [GFFObservable.smear, mul_add]
    exact integral_add ((hφ.1.continuous.mul hf).integrable_of_hasCompactSupport hφ.2.1.mul_right)
      ((hφ.1.continuous.mul hg).integrable_of_hasCompactSupport hφ.2.1.mul_right)
  | circle r x =>
    simp only [GFFObservable.smear]
    exact Real.circleAverage_fun_add hf.continuousOn.circleIntegrable' hg.continuousOn.circleIntegrable'

lemma smear_const_mul (o : GFFObservable) (ho : o.IsAdmissible) (k : ℝ) (f : ℂ → ℝ) :
    o.smear (fun x => k * f x) = k * o.smear f := by
  cases o with
  | pairing φ =>
    simp only [GFFObservable.smear]
    rw [← integral_const_mul]
    congr 1
    ext x
    ring
  | circle r x =>
    simp only [GFFObservable.smear, Real.circleAverage, smul_eq_mul]
    rw [intervalIntegral.integral_const_mul]
    ring

/-- Off the diagonal the kernel is translated up to `a(x) + a(y)`. -/
lemma wholePlaneCov_shift_of_ne (z : ℂ) {x y : ℂ} (h : x ≠ y) :
    wholePlaneCov (x + z) (y + z) = wholePlaneCov x y + shiftDiff z x + shiftDiff z y := by
  have hd : ‖x + z - (y + z)‖ = ‖x - y‖ := by rw [add_sub_add_right_eq_sub]
  have hdpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  have hA : ∀ w : ℂ, 0 < max ‖w‖ 1 := fun w => lt_of_lt_of_le one_pos (le_max_right _ _)
  have e : ∀ p q : ℝ, 0 < p → 0 < q → Real.log (p * q / ‖x - y‖) =
      Real.log p + Real.log q - Real.log ‖x - y‖ := by
    intro p q hp hq
    rw [Real.log_div (mul_pos hp hq).ne' hdpos.ne', Real.log_mul hp.ne' hq.ne']
  unfold wholePlaneCov shiftDiff wholePlaneNormalization
  rw [hd, e _ _ (hA _) (hA _), e _ _ (hA x) (hA y)]
  ring

/-- The pointwise identity integrated against a pairing (a.e. off the diagonal). -/
lemma inner_shift_pairing (z x : ℂ) {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    (GFFObservable.pairing φ).smear (fun y => wholePlaneCov (x + z) (y + z)) =
      (GFFObservable.pairing φ).smear (fun y => wholePlaneCov x y) + shiftDiff z x * mass (.pairing φ) +
        (GFFObservable.pairing φ).smear (shiftDiff z) := by
  have hae : ∀ᵐ y ∂(volume : Measure ℂ), y ≠ x := by
    rw [ae_iff]
    simp
  have hI1 : Integrable (fun y => φ y * wholePlaneCov x y) :=
    integrable_mul_wholePlaneCov hφ.1.continuous hφ.2.1 x
  have hI2 : Integrable (fun y => φ y * shiftDiff z y) :=
    (hφ.1.continuous.mul (continuous_shiftDiff z)).integrable_of_hasCompactSupport hφ.2.1.mul_right
  have hI3 : Integrable (fun y => shiftDiff z x * φ y) :=
    (hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1).const_mul _
  have hI12 : Integrable (fun y => φ y * wholePlaneCov x y + shiftDiff z x * φ y) := hI1.add hI3
  have hpt : ∀ᵐ y ∂(volume : Measure ℂ), φ y * wholePlaneCov (x + z) (y + z) =
      φ y * wholePlaneCov x y + shiftDiff z x * φ y + φ y * shiftDiff z y := by
    filter_upwards [hae] with y hy
    rw [wholePlaneCov_shift_of_ne z hy.symm]
    ring
  simp only [GFFObservable.smear, mass, mul_one]
  rw [integral_congr_ae hpt, integral_add hI12 hI2, integral_add hI1 hI3, integral_const_mul]

/-- The pointwise identity integrated against a circle average. -/
lemma inner_shift_circle (z x w : ℂ) {s : ℝ} (hs : 0 < s) :
    Real.circleAverage (fun y => wholePlaneCov (x + z) (y + z)) w s =
      Real.circleAverage (fun y => wholePlaneCov x y) w s + shiftDiff z x +
        Real.circleAverage (shiftDiff z) w s := by
  have hLc : Continuous wholePlaneNormalization := continuous_wholePlaneNormalization
  have hLt : Continuous fun y : ℂ => wholePlaneNormalization (y + z) :=
    hLc.comp (continuous_id.add continuous_const)
  have h1 : Real.circleAverage (fun y => wholePlaneCov (x + z) (y + z)) w s =
      Real.circleAverage (wholePlaneCov (x + z)) (w + z) s :=
    circleAverage_comp_add_right _ w z s
  have h2 : Real.circleAverage (shiftDiff z) w s =
      Real.circleAverage wholePlaneNormalization (w + z) s -
        Real.circleAverage wholePlaneNormalization w s := by
    have hfun : shiftDiff z = fun y => wholePlaneNormalization (y + z) - wholePlaneNormalization y := by
      funext y
      rfl
    rw [hfun, Real.circleAverage_fun_sub hLt.continuousOn.circleIntegrable' hLc.continuousOn.circleIntegrable',
      circleAverage_comp_add_right wholePlaneNormalization w z s]
  have h3 : ‖w + z - (x + z)‖ = ‖w - x‖ := by rw [add_sub_add_right_eq_sub]
  rw [h1, h2, circleAverage_wholePlaneCov_eq hs (w + z) (x + z),
    circleAverage_wholePlaneCov_eq hs w x, h3]
  unfold shiftDiff
  ring

lemma inner_shift (z x : ℂ) {o : GFFObservable} (ho : o.IsAdmissible) :
    o.smear (fun y => wholePlaneCov (x + z) (y + z)) =
      o.smear (fun y => wholePlaneCov x y) + shiftDiff z x * mass o + o.smear (shiftDiff z) := by
  cases o with
  | pairing φ => exact inner_shift_pairing z x ho
  | circle r w =>
    have hr : 0 < r := ho
    have hm : mass (.circle r w) = 1 := smear_mass_circle r w
    simp only [GFFObservable.smear, hm, mul_one]
    exact inner_shift_circle z x w hr

lemma continuous_inner (o : GFFObservable) (ho : o.IsAdmissible) :
    Continuous (fun x => o.smear (fun y => wholePlaneCov x y)) := by
  cases o with
  | pairing φ => exact continuous_wholePlaneCov_potential_general ho.1.continuous ho.2.1
  | circle r w => exact continuous_circleAverage_wholePlaneCov ho w

lemma smear_add3 (o : GFFObservable) (ho : o.IsAdmissible) {F s : ℂ → ℝ} (hF : Continuous F)
    (hs : Continuous s) (k c : ℝ) :
    o.smear (fun x => F x + s x * k + c) = o.smear F + k * o.smear s + c * mass o := by
  have hF' : Continuous fun x => F x + s x * k := hF.add (hs.mul continuous_const)
  have hks : Continuous fun x => s x * k := hs.mul continuous_const
  have h1 : o.smear (fun x => F x + s x * k + c) =
      o.smear (fun x => F x + s x * k) + o.smear (fun _ => c) :=
    smear_add_of_continuous o ho hF' continuous_const
  have h2 : o.smear (fun x => F x + s x * k) = o.smear F + o.smear (fun x => s x * k) :=
    smear_add_of_continuous o ho hF hks
  have h3 : o.smear (fun x => s x * k) = k * o.smear s := by
    rw [← smear_const_mul o ho k s]
    congr 1
    funext x
    ring
  rw [h1, h2, h3, smear_const o c]

/-- `W(shift o, shift o') = W(o,o') + mass o' · o.a + mass o · o'.a`. -/
lemma wholePlaneGFFCov_shift_shift (z : ℂ) {o o' : GFFObservable} (ho : o.IsAdmissible)
    (ho' : o'.IsAdmissible) :
    wholePlaneGFFCov (shiftObs z o) (shiftObs z o') =
      wholePlaneGFFCov o o' + mass o' * o.smear (shiftDiff z) + mass o * o'.smear (shiftDiff z) := by
  have hin : ∀ x, o'.smear (fun y => wholePlaneCov (x + z) (y + z)) =
      o'.smear (fun y => wholePlaneCov x y) + shiftDiff z x * mass o' + o'.smear (shiftDiff z) :=
    fun x => inner_shift z x ho'
  unfold wholePlaneGFFCov
  simp only [smear_shiftObs, hin]
  have key := smear_add3 o ho (continuous_inner o' ho') (continuous_shiftDiff z) (mass o')
    (o'.smear (shiftDiff z))
  beta_reduce at key
  rw [key]
  ring

/-- `W(shift o, b) = o.a + m · mass o` for the unit circle `b = circle 1 z`, `m = circleAverage L z 1`. -/
lemma wholePlaneGFFCov_shift_circle (z : ℂ) {o : GFFObservable} (ho : o.IsAdmissible) :
    wholePlaneGFFCov (shiftObs z o) (.circle 1 z) =
      o.smear (shiftDiff z) + Real.circleAverage wholePlaneNormalization z 1 * mass o := by
  have hpt : ∀ x : ℂ, (GFFObservable.circle 1 z).smear (fun y => wholePlaneCov (x + z) y) =
      shiftDiff z x + Real.circleAverage wholePlaneNormalization z 1 := by
    intro x
    simp only [GFFObservable.smear]
    rw [circleAverage_wholePlaneCov_eq one_pos z (x + z)]
    have hn : ‖z - (x + z)‖ = ‖x‖ := by
      rw [show z - (x + z) = -x by ring, norm_neg]
    rw [hn, max_comm]
    unfold shiftDiff wholePlaneNormalization
    ring
  unfold wholePlaneGFFCov
  simp only [smear_shiftObs, hpt]
  have h1 : o.smear (fun x => shiftDiff z x + Real.circleAverage wholePlaneNormalization z 1) =
      o.smear (shiftDiff z) + o.smear (fun _ => Real.circleAverage wholePlaneNormalization z 1) :=
    smear_add_of_continuous o ho (continuous_shiftDiff z) continuous_const
  rw [h1, smear_const o]

/-- `W(b, b) = 2m` for `b = circle 1 z`. -/
lemma wholePlaneGFFCov_circle_circle (z : ℂ) :
    wholePlaneGFFCov (.circle 1 z) (.circle 1 z) = 2 * Real.circleAverage wholePlaneNormalization z 1 := by
  unfold wholePlaneGFFCov
  simp only [GFFObservable.smear, circleAverage_wholePlaneCov_eq one_pos]
  have hsph : Real.circleAverage (fun x => wholePlaneNormalization x +
      Real.circleAverage wholePlaneNormalization z 1 - Real.log (max 1 ‖z - x‖)) z 1 =
      Real.circleAverage (fun x => wholePlaneNormalization x +
        Real.circleAverage wholePlaneNormalization z 1) z 1 := by
    apply Real.circleAverage_congr_sphere
    intro x hx
    have hx1 : ‖z - x‖ = 1 := by
      rw [mem_sphere, dist_eq_norm] at hx
      rw [norm_sub_rev]
      simpa using hx
    simp only [hx1, max_self, Real.log_one, sub_zero]
  rw [hsph]
  have hL : CircleIntegrable wholePlaneNormalization z 1 :=
    continuous_wholePlaneNormalization.continuousOn.circleIntegrable'
  have hc : CircleIntegrable (fun _ : ℂ => Real.circleAverage wholePlaneNormalization z 1) z 1 :=
    continuous_const.continuousOn.circleIntegrable'
  rw [Real.circleAverage_fun_add hL hc, Real.circleAverage_const, two_mul]

/-- Kernel identity behind Lemma 11.7's translation: the translated covariance matrix of
`(o, b)` is the original kernel. -/
lemma wholePlaneGFFCov_shift_combo (z : ℂ) {o o' : GFFObservable} (ho : o.IsAdmissible)
    (ho' : o'.IsAdmissible) :
    wholePlaneGFFCov (shiftObs z o) (shiftObs z o') - mass o' * wholePlaneGFFCov (shiftObs z o) (.circle 1 z)
      - mass o * wholePlaneGFFCov (shiftObs z o') (.circle 1 z)
      + mass o * mass o' * wholePlaneGFFCov (.circle 1 z) (.circle 1 z) = wholePlaneGFFCov o o' := by
  rw [wholePlaneGFFCov_shift_shift z ho ho', wholePlaneGFFCov_shift_circle z ho,
    wholePlaneGFFCov_shift_circle z ho', wholePlaneGFFCov_circle_circle z]
  ring

end HarmonicBalls.S11c
