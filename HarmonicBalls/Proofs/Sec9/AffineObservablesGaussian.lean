import HarmonicBalls.Proofs.Sec9.CircleCovarianceAffine

/-! # Gaussianity of affine-transformed GFF observables

The pairing and circle observables remain jointly Gaussian after affine
pullback and normalization. This does not establish covariance invariance.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

/-- Pulling a test function back by the inverse of a nonconstant complex
affine map preserves smoothness and compact support. -/
theorem IsTestFunction.comp_inverse_complex_affine {φ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsTestFunction univ (fun y => φ ((y - b) / a)) := by
  refine ⟨hφ.1.comp ?_, ?_, subset_univ _⟩
  · fun_prop
  · let e : ℂ ≃ₜ ℂ := (Homeomorph.addRight (-b)).trans
        (Homeomorph.mulLeft₀ a⁻¹ (inv_ne_zero ha))
    simpa [e, Function.comp_def, sub_eq_add_neg, div_eq_mul_inv, mul_comm] using
      hφ.2.1.comp_homeomorph e

/-- Any family of weighted, recentered GFF observables is jointly Gaussian.
The same reference observable can be used for pairings and circles. -/
theorem IsWholePlaneGFF.isGaussianProcess_weighted_recentered
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (o : ι → GFFObservable.Admissible)
    (q : GFFObservable.Admissible) (c d : ι → ℝ) :
    IsGaussianProcess (fun i ω => c i * (o i).1.eval (hC ω) (hcirc ω) -
      d i * q.1.eval (hC ω) (hcirc ω)) P := by
  classical
  apply h.isGaussianProcess.of_isGaussianProcess
  intro i
  let I : Finset GFFObservable.Admissible := {o i, q}
  let p : (I → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj ⟨o i, by simp [I]⟩
  let r : (I → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj ⟨q, by simp [I]⟩
  refine ⟨I, c i • p - d i • r, ?_⟩
  intro ω
  rfl

/-- Weighted, recentered admissible GFF observables remain centered. -/
theorem IsWholePlaneGFF.integral_weighted_recentered_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (o q : GFFObservable.Admissible) (c d : ℝ) :
    ∫ ω, (c * o.1.eval (hC ω) (hcirc ω) - d * q.1.eval (hC ω) (hcirc ω)) ∂P = 0 := by
  have ho := (h.isGaussianProcess.hasGaussianLaw_eval o).integrable
  have hq := (h.isGaussianProcess.hasGaussianLaw_eval q).integrable
  rw [integral_sub (ho.const_mul c) (hq.const_mul d), integral_const_mul,
    integral_const_mul, h.integral_eq_zero o.1 o.2, h.integral_eq_zero q.1 q.2]
  simp only [mul_zero, sub_self]

/-- The affine-transformed pairings and circle averages form a jointly
Gaussian process. The covariance identities required for affine invariance
are separate from this Gaussianity statement. -/
theorem IsWholePlaneGFF.isGaussianProcess_complex_affine
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsGaussianProcess (fun (o : GFFObservable.Admissible) ω => o.1.eval
      (fun φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) -
        hcirc ω ‖a‖ b * ∫ x, φ x)
      (fun r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b)) P := by
  let o : GFFObservable.Admissible → GFFObservable.Admissible := fun i =>
    match i with
    | ⟨.pairing φ, hφ⟩ => ⟨.pairing (fun y => φ ((y - b) / a)),
        hφ.comp_inverse_complex_affine ha b⟩
    | ⟨.circle r z, hr⟩ => ⟨.circle (‖a‖ * r) (a * z + b),
        mul_pos (norm_pos_iff.mpr ha) hr⟩
  let q : GFFObservable.Admissible := ⟨.circle ‖a‖ b, norm_pos_iff.mpr ha⟩
  let c : GFFObservable.Admissible → ℝ := fun i =>
    match i.1 with
    | .pairing _ => (‖a‖ ^ 2)⁻¹
    | .circle _ _ => 1
  let d : GFFObservable.Admissible → ℝ := fun i =>
    match i.1 with
    | .pairing φ => ∫ x, φ x
    | .circle _ _ => 1
  have hg := h.isGaussianProcess_weighted_recentered o q c d
  convert hg using 1
  funext i ω
  rcases i with ⟨oi, hi⟩
  cases oi with
  | pairing φ => simp only [o, q, c, d, GFFObservable.eval, mul_comm]
  | circle r z => simp only [o, q, c, d, GFFObservable.eval, one_mul]

/-- Every admissible affine-transformed observable is centered. -/
theorem IsWholePlaneGFF.integral_complex_affine_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {a : ℂ} (ha : a ≠ 0) (b : ℂ)
    (o : GFFObservable) (ho : o.IsAdmissible) :
    ∫ ω, o.eval
      (fun φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) -
        hcirc ω ‖a‖ b * ∫ x, φ x)
      (fun r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b) ∂P = 0 := by
  let q : GFFObservable.Admissible := ⟨.circle ‖a‖ b, norm_pos_iff.mpr ha⟩
  cases o with
  | pairing φ =>
    let p : GFFObservable.Admissible := ⟨.pairing (fun y => φ ((y - b) / a)),
      ho.comp_inverse_complex_affine ha b⟩
    simpa only [p, q, GFFObservable.eval, mul_comm] using
      h.integral_weighted_recentered_eq_zero p q (‖a‖ ^ 2)⁻¹ (∫ x, φ x)
  | circle r z =>
    let p : GFFObservable.Admissible := ⟨.circle (‖a‖ * r) (a * z + b),
      mul_pos (norm_pos_iff.mpr ha) ho⟩
    simpa only [p, q, GFFObservable.eval, one_mul] using
      h.integral_weighted_recentered_eq_zero p q 1 1

/-- The circle-circle part of the affine covariance identity holds without
additional assumptions. -/
theorem IsWholePlaneGFF.covariance_complex_affine_circles
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {a : ℂ} (ha : a ≠ 0) (b : ℂ)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    cov[fun ω => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b,
      fun ω => hcirc ω (‖a‖ * s) (a * w + b) - hcirc ω ‖a‖ b; P] =
      wholePlaneGFFCov (.circle r z) (.circle s w) := by
  have hc := h.covariance_circle_increments_complex_affine ha hr hs
    (show (0 : ℝ) < 1 from zero_lt_one) z w 0 b
  simp only [mul_one, mul_zero, zero_add] at hc
  have hi (t : ℝ) (v : ℂ) :
      (fun ω => hcirc ω t v - hcirc ω 1 0) =ᵐ[P] (fun ω => hcirc ω t v) := by
    filter_upwards [h.ae_circleAverage_one_zero] with ω hω
    simp only [hω, sub_zero]
  have hcov : cov[fun ω => hcirc ω r z - hcirc ω 1 0,
      fun ω => hcirc ω s w - hcirc ω 1 0; P] =
      cov[fun ω => hcirc ω r z, fun ω => hcirc ω s w; P] := by
    unfold ProbabilityTheory.covariance
    have hi₁ := integral_congr_ae (hi r z)
    have hi₂ := integral_congr_ae (hi s w)
    rw [hi₁, hi₂]
    apply integral_congr_ae
    filter_upwards [hi r z, hi s w] with ω h₁ h₂
    rw [h₁, h₂]
  rw [hcov] at hc
  rw [hc]
  simpa only [GFFObservable.eval] using h.covariance_eq (.circle r z) (.circle s w) hr hs

/-- Affine invariance reduces to the covariance identity for admissible
observables. The identity includes pairing-pairing and mixed cases. -/
theorem IsWholePlaneGFF.complex_affine_of_covariance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {a : ℂ} (ha : a ≠ 0) (b : ℂ)
    (hcov : ∀ o o' : GFFObservable, o.IsAdmissible → o'.IsAdmissible →
      cov[fun ω => o.eval
        (fun φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) -
          hcirc ω ‖a‖ b * ∫ x, φ x)
        (fun r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b),
      fun ω => o'.eval
        (fun φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) -
          hcirc ω ‖a‖ b * ∫ x, φ x)
        (fun r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b); P] =
        wholePlaneGFFCov o o') :
    IsWholePlaneGFF P
      (fun ω φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) -
        hcirc ω ‖a‖ b * ∫ x, φ x)
      (fun ω r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b) := by
  refine ⟨?_, ?_, h.isGaussianProcess_complex_affine ha b,
    h.integral_complex_affine_eq_zero ha b, hcov, ?_⟩
  · intro φ hφ
    exact (measurable_const.mul (h.measurable_pairing _ (hφ.comp_inverse_complex_affine ha b))).sub
      ((h.measurable_circle _ _ (norm_pos_iff.mpr ha)).mul measurable_const)
  · intro r z hr
    exact (h.measurable_circle _ _ (mul_pos (norm_pos_iff.mpr ha) hr)).sub
      (h.measurable_circle _ _ (norm_pos_iff.mpr ha))
  · filter_upwards [h.ae_continuousOn_circle] with ω hω
    have hf : Continuous (fun p : ℝ × ℂ => (‖a‖ * p.1, a * p.2 + b)) := by fun_prop
    have hs : MapsTo (fun p : ℝ × ℂ => (‖a‖ * p.1, a * p.2 + b))
        (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) := by
      intro p hp
      exact ⟨mul_pos (norm_pos_iff.mpr ha) hp.1, mem_univ _⟩
    exact (hω.comp hf.continuousOn hs).sub continuousOn_const

/-- The covariance kernel of admissible observables is symmetric, as a
consequence of the covariance specification of the field. -/
theorem IsWholePlaneGFF.wholePlaneGFFCov_comm
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (o o' : GFFObservable)
    (ho : o.IsAdmissible) (ho' : o'.IsAdmissible) :
    wholePlaneGFFCov o o' = wholePlaneGFFCov o' o := by
  rw [← h.covariance_eq o o' ho ho', ← h.covariance_eq o' o ho' ho]
  exact covariance_comm _ _

/-- To prove affine invariance it suffices to establish covariance identities
with a pairing in the first argument; the circle-circle identity is proved
and symmetry supplies the other mixed orientation. -/
theorem IsWholePlaneGFF.complex_affine_of_pairing_covariance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {a : ℂ} (ha : a ≠ 0) (b : ℂ)
    (hcov : ∀ (φ : ℂ → ℝ), IsTestFunction univ φ →
      ∀ o : GFFObservable, o.IsAdmissible →
      cov[fun ω => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) -
          hcirc ω ‖a‖ b * ∫ x, φ x,
        fun ω => o.eval
          (fun ψ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => ψ ((y - b) / a)) -
            hcirc ω ‖a‖ b * ∫ x, ψ x)
          (fun r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b); P] =
        wholePlaneGFFCov (.pairing φ) o) :
    IsWholePlaneGFF P
      (fun ω φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) -
        hcirc ω ‖a‖ b * ∫ x, φ x)
      (fun ω r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b) := by
  apply h.complex_affine_of_covariance ha b
  intro o o' ho ho'
  cases o with
  | pairing φ => exact hcov φ ho o' ho'
  | circle r z =>
    cases o' with
    | pairing φ =>
      have hc := hcov φ ho' (.circle r z) ho
      simp only [GFFObservable.eval] at hc ⊢
      rw [covariance_comm]
      exact hc.trans (h.wholePlaneGFFCov_comm (.pairing φ) (.circle r z) ho' ho)
    | circle s w => exact h.covariance_complex_affine_circles ha b ho ho' z w

end HarmonicBalls
