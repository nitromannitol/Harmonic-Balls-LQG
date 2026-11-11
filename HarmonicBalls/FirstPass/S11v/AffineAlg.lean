import HarmonicBalls.FirstPass.S11v.AffineKernel

open scoped ContDiff

/-!
# Deterministic covariance identity for the affine pull-back

For `a ≠ 0`, `b ∈ ℂ`, the observables of the transformed field are `affC a o • (affP a b o) - (mass o) • (circle |a| b)`
(`hC'`, `hcirc'` of `WholePlaneGFFAffineInvariance`, Proposed/LQG.lean). This file proves the kernel identity
`cov(T o, T o') = wholePlaneGFFCov o o' - mass(o) wholePlaneGFFCov(circle 1 0, o')` in its deterministic form
`cov_det_identity`, from the change of variables (AffineCore), the pointwise affine identity and its smeared forms
(AffineKernel), and the linearity of smearing functionals against continuous potentials.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology

/-- Pull-back of an observable by `F z = a z + b`: a pairing `φ` becomes `φ ∘ F⁻¹`; a circle average `(r, z)`
becomes the circle average `(|a| r, F z)`. -/
noncomputable def affP (a b : ℂ) : GFFObservable → GFFObservable
  | .pairing φ => .pairing (fun y => φ ((y - b) / a))
  | .circle r z => .circle (‖a‖ * r) (a * z + b)

/-- Coefficient of the pulled-back observable: `|a|⁻²` for a pairing (Jacobian), `1` for a circle average. -/
noncomputable def affC (a : ℂ) : GFFObservable → ℝ
  | .pairing _ => (‖a‖ ^ 2)⁻¹
  | .circle _ _ => 1

/-- Smearing against the circle average of the base point `b` in the original coordinates. -/
theorem smear_circle_affine_base {a : ℂ} (b : ℂ) (f : ℂ → ℝ) :
    (GFFObservable.circle ‖a‖ b).smear f = (GFFObservable.circle 1 0).smear (fun x => f (a * x + b)) := by
  have := circleAverage_affine_comp (a := a) b f 0 1
  simp only [mul_one, mul_zero, zero_add] at this
  exact this

/-- **Core change of variables.** For every observable `o` and every function `f` (no integrability needed):
`affC a o · (affP a b o)[f] - m_o · (circle |a| b)[f] = o[f ∘ F] - m_o · (circle 1 0)[f ∘ F]`, where `m_o = o[1]`. -/
theorem smear_affine_core {a : ℂ} (ha : a ≠ 0) (b : ℂ) (o : GFFObservable) (f : ℂ → ℝ) :
    affC a o * (affP a b o).smear f - (o.smear fun _ => 1) * (GFFObservable.circle ‖a‖ b).smear f =
      o.smear (fun x => f (a * x + b)) -
        (o.smear fun _ => 1) * (GFFObservable.circle 1 0).smear (fun x => f (a * x + b)) := by
  cases o with
  | pairing φ =>
    have h := smear_affine_pairing ha b φ f
    have hb := smear_circle_affine_base (a := a) b f
    simp only [affC, affP]
    linear_combination h - (GFFObservable.pairing φ).smear (fun _ => 1) * hb
  | circle r z =>
    have h := smear_affine_circle_sub (a := a) b z r f
    have hm : (GFFObservable.circle r z).smear (fun _ => 1) = 1 := Real.circleAverage_const (1 : ℝ) z r
    simp only [affC, affP]
    rw [hm, one_mul, one_mul]
    linear_combination h

/-- Linear combinations of smearing functionals against continuous functions (`o` admissible). -/
theorem smear_lincomb {q : GFFObservable} (hq : q.IsAdmissible) {g₁ g₂ : ℂ → ℝ} (h₁ : Continuous g₁)
    (h₂ : Continuous g₂) (α β : ℝ) :
    q.smear (fun x => α * g₁ x + β * g₂ x) = α * q.smear g₁ + β * q.smear g₂ := by
  cases q with
  | pairing ψ =>
    have i1 := (integrable_test_mul_continuous hq h₁).const_mul α
    have i2 := (integrable_test_mul_continuous hq h₂).const_mul β
    simp only [GFFObservable.smear]
    rw [show (fun x => ψ x * (α * g₁ x + β * g₂ x)) = fun x => α * (ψ x * g₁ x) + β * (ψ x * g₂ x) from
      funext fun x => by ring, integral_add i1 i2, integral_const_mul, integral_const_mul]
  | circle r z =>
    have hr : 0 < r := hq
    have c1 : CircleIntegrable (fun x => α * g₁ x) z r :=
      ((continuous_const.mul h₁).continuousOn).circleIntegrable'
    have c2 : CircleIntegrable (fun x => β * g₂ x) z r :=
      ((continuous_const.mul h₂).continuousOn).circleIntegrable'
    show Real.circleAverage (fun x => α * g₁ x + β * g₂ x) z r = _
    rw [Real.circleAverage_fun_add c1 c2]
    have e1 : Real.circleAverage (fun x => α * g₁ x) z r = α * Real.circleAverage g₁ z r := by
      rw [show (fun x => α * g₁ x) = fun x => α • g₁ x from rfl, Real.circleAverage_fun_smul, smul_eq_mul]
    have e2 : Real.circleAverage (fun x => β * g₂ x) z r = β * Real.circleAverage g₂ z r := by
      rw [show (fun x => β * g₂ x) = fun x => β • g₂ x from rfl, Real.circleAverage_fun_smul, smul_eq_mul]
    rw [e1, e2]
    rfl

/-- Adding a constant: `q[g + c] = q[g] + c · q[1]`. -/
theorem smear_add_const {q : GFFObservable} (hq : q.IsAdmissible) {g : ℂ → ℝ} (hg : Continuous g) (c : ℝ) :
    q.smear (fun x => g x + c) = q.smear g + c * q.smear (fun _ => 1) := by
  have h := smear_lincomb (g₂ := fun _ : ℂ => (1 : ℝ)) hq hg continuous_const 1 c
  simp only [one_mul, mul_one] at h
  exact h

/-- Composition with the affine map `y ↦ (y - b)/a` preserves test functions. -/
theorem isTestFunction_affine {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsTestFunction univ (fun y => φ ((y - b) / a)) := by
  obtain ⟨h1, h2, -⟩ := hφ
  let H : ℂ ≃ₜ ℂ := (Homeomorph.addRight (-b)).trans (Homeomorph.mulLeft₀ a⁻¹ (inv_ne_zero ha))
  have e : (fun y => φ ((y - b) / a)) = φ ∘ H := by
    funext y
    change φ ((y - b) / a) = φ (a⁻¹ * (y + -b))
    congr 1
    ring
  refine ⟨?_, ?_, subset_univ _⟩
  · rw [e]
    refine h1.comp ?_
    show ContDiff ℝ ∞ (fun y : ℂ => a⁻¹ * (y + -b))
    fun_prop
  · rw [e]
    exact h2.comp_homeomorph H

/-- The pulled-back observable is admissible. -/
theorem isAdmissible_affP {a : ℂ} (ha : a ≠ 0) (b : ℂ) {o : GFFObservable} (ho : o.IsAdmissible) :
    (affP a b o).IsAdmissible := by
  cases o with
  | pairing φ => exact isTestFunction_affine ho ha b
  | circle r z => exact mul_pos (norm_pos_iff.2 ha) ho

/-- The potential of an admissible observable transforms as the kernel at `F x` (smeared form). -/
theorem smear_potential_affine {a : ℂ} (ha : a ≠ 0) (b x : ℂ) {q : GFFObservable} (hq : q.IsAdmissible) :
    q.smear (fun y => wholePlaneCov (a * x + b) (a * y + b)) =
      q.smear (fun y => wholePlaneCov x y) + (q.smear fun _ => 1) * affM a b x + q.smear (affM a b) -
        (q.smear fun _ => 1) * affM0 a b := by
  cases q with
  | pairing ψ =>
    have h := integral_potential_affine_pairing ha b x hq
    simp only [GFFObservable.smear, mul_one]
    exact h
  | circle r z =>
    have hr : 0 < r := hq
    have h := circleAverage_potential_affine ha b x z hr
    have hm : (GFFObservable.circle r z).smear (fun _ => 1) = 1 := Real.circleAverage_const (1 : ℝ) z r
    rw [hm, one_mul, one_mul]
    exact h

/-- The transformed potential at `F x`: the kernel potential of `o'` at `x`, up to a constant. -/
theorem transformed_potential_affine {a : ℂ} (ha : a ≠ 0) (b x : ℂ) {o' : GFFObservable} (ho' : o'.IsAdmissible) :
    affC a o' * (affP a b o').smear (fun w => wholePlaneCov (a * x + b) w) -
        (o'.smear fun _ => 1) * (GFFObservable.circle ‖a‖ b).smear (fun w => wholePlaneCov (a * x + b) w) =
      o'.smear (fun y => wholePlaneCov x y) + (o'.smear (affM a b) - (o'.smear fun _ => 1) * affM0 a b) := by
  have hcore := smear_affine_core ha b o' (fun w => wholePlaneCov (a * x + b) w)
  beta_reduce at hcore
  have hC1 : (GFFObservable.circle 1 0).IsAdmissible := one_pos
  rw [hcore, smear_potential_affine ha b x ho', smear_potential_affine ha b x hC1]
  have hC1K : (GFFObservable.circle 1 0).smear (fun y => wholePlaneCov x y) = 0 :=
    circleAverage_wholePlaneCov_unit x
  have hC1M : (GFFObservable.circle 1 0).smear (affM a b) = affM0 a b := circleAverage_affM_unit a b
  have hC1one : (GFFObservable.circle 1 0).smear (fun _ => 1) = 1 := Real.circleAverage_const (1 : ℝ) 0 1
  rw [hC1K, hC1M, hC1one]
  ring

/-- **Deterministic covariance identity of the affine pull-back.** For admissible `o, o'` the bilinear expansion of
`cov(T o, T o')`, with `T o = affC · affP - mass(o) · circle |a| b`, equals `B(o, o') - mass(o) B(circle 1 0, o')`. -/
theorem cov_det_identity {a : ℂ} (ha : a ≠ 0) (b : ℂ) {o o' : GFFObservable} (ho : o.IsAdmissible)
    (ho' : o'.IsAdmissible) :
    affC a o * affC a o' * wholePlaneGFFCov (affP a b o) (affP a b o') -
        affC a o * (o'.smear fun _ => 1) * wholePlaneGFFCov (affP a b o) (GFFObservable.circle ‖a‖ b) -
      (o.smear fun _ => 1) * affC a o' * wholePlaneGFFCov (GFFObservable.circle ‖a‖ b) (affP a b o') +
        (o.smear fun _ => 1) * (o'.smear fun _ => 1) *
          wholePlaneGFFCov (GFFObservable.circle ‖a‖ b) (GFFObservable.circle ‖a‖ b) =
      wholePlaneGFFCov o o' - (o.smear fun _ => 1) * wholePlaneGFFCov (GFFObservable.circle 1 0) o' := by
  unfold wholePlaneGFFCov
  have hpo : (affP a b o).IsAdmissible := isAdmissible_affP ha b ho
  have hp' : (affP a b o').IsAdmissible := isAdmissible_affP ha b ho'
  have hS : (GFFObservable.circle ‖a‖ b).IsAdmissible := norm_pos_iff.2 ha
  have cP : Continuous (fun w => (affP a b o').smear (fun y => wholePlaneCov w y)) :=
    continuous_potential hp'
  have cS : Continuous (fun w => (GFFObservable.circle ‖a‖ b).smear (fun y => wholePlaneCov w y)) :=
    continuous_potential hS
  have hA : Continuous (fun x => o'.smear (fun y => wholePlaneCov x y)) := continuous_potential ho'
  set G : ℂ → ℝ := fun w => affC a o' * (affP a b o').smear (fun y => wholePlaneCov w y) -
    (o'.smear fun _ => 1) * (GFFObservable.circle ‖a‖ b).smear (fun y => wholePlaneCov w y) with hG
  have hGeq : G = fun w => affC a o' * (affP a b o').smear (fun y => wholePlaneCov w y) +
      (-(o'.smear fun _ => 1)) * (GFFObservable.circle ‖a‖ b).smear (fun y => wholePlaneCov w y) :=
    funext fun w => by simp only [hG]; ring
  have s1 : (affP a b o).smear G =
      affC a o' * (affP a b o).smear (fun w => (affP a b o').smear (fun y => wholePlaneCov w y)) +
        (-(o'.smear fun _ => 1)) *
          (affP a b o).smear (fun w => (GFFObservable.circle ‖a‖ b).smear (fun y => wholePlaneCov w y)) :=
    by rw [hGeq]; exact smear_lincomb hpo cP cS _ _
  have s2 : (GFFObservable.circle ‖a‖ b).smear G =
      affC a o' * (GFFObservable.circle ‖a‖ b).smear (fun w => (affP a b o').smear (fun y => wholePlaneCov w y)) +
        (-(o'.smear fun _ => 1)) *
          (GFFObservable.circle ‖a‖ b).smear (fun w => (GFFObservable.circle ‖a‖ b).smear (fun y => wholePlaneCov w y)) :=
    by rw [hGeq]; exact smear_lincomb hS cP cS _ _
  have hcore := smear_affine_core ha b o G
  have hGF : (fun x => G (a * x + b)) = fun x =>
      o'.smear (fun y => wholePlaneCov x y) + (o'.smear (affM a b) - (o'.smear fun _ => 1) * affM0 a b) :=
    funext fun x => transformed_potential_affine ha b x ho'
  rw [hGF] at hcore
  have hC1 : (GFFObservable.circle 1 0).IsAdmissible := one_pos
  have hc0 := smear_add_const ho hA (o'.smear (affM a b) - (o'.smear fun _ => 1) * affM0 a b)
  have hc1 := smear_add_const hC1 hA (o'.smear (affM a b) - (o'.smear fun _ => 1) * affM0 a b)
  have hC1one : (GFFObservable.circle 1 0).smear (fun _ => 1) = 1 := Real.circleAverage_const (1 : ℝ) 0 1
  beta_reduce at hc0 hc1
  rw [hc0, hc1, hC1one] at hcore
  linear_combination hcore - affC a o * s1 + (o.smear fun _ => 1) * s2

end HarmonicBalls
