import HarmonicBalls.FirstPass.S11v.AffineAlg
import HarmonicBalls.Proposed.LQG

/-!
# `WholePlaneGFFAffineInvariance` is a theorem (fp-S11v, P6; operator note 01:44 UTC, `notes/fp-gaps/CHATGPT-n1-hAff-hhom.md` §1)

`WholePlaneGFFAffineInvariance P hC hcirc` (Proposed/LQG.lean) says that the transformed pairings
`hC' ω φ = |a|⁻² hC ω (φ ∘ F⁻¹) - hcirc ω |a| b ∫φ` and circle averages `hcirc' ω r z = hcirc ω (|a| r) (a z + b) -
hcirc ω |a| b` (`F z = a z + b`) again form a whole-plane GFF whenever `hC, hcirc` do. It is derived here from
`IsWholePlaneGFF` alone: the transformed observables are the finite combinations `affC · affP - mass · circle |a| b`
(`AffineAlg.lean`), which gives the Gaussian, measurability, centring and continuity clauses, and the covariance clause
through the deterministic identity `cov_det_identity` and `cov(circle 1 0, ·) = 0`, the unit-circle value being
almost surely zero (`IsWholePlaneGFF.ae_circleAverage_one_zero`).
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The value of a transformed observable in terms of the original field (`affP`, `affC`, mass). -/
theorem eval_affine {a : ℂ} (b : ℂ) (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ)
    (o : GFFObservable) :
    o.eval (fun φ => (‖a‖ ^ 2)⁻¹ * hC (fun y => φ ((y - b) / a)) - hcirc ‖a‖ b * ∫ x, φ x)
        (fun r z => hcirc (‖a‖ * r) (a * z + b) - hcirc ‖a‖ b) =
      affC a o * (affP a b o).eval hC hcirc - (o.smear fun _ => 1) * hcirc ‖a‖ b := by
  cases o with
  | pairing φ =>
    simp only [GFFObservable.eval, affC, affP, GFFObservable.smear, mul_one]
    ring
  | circle r z =>
    have hm : (GFFObservable.circle r z).smear (fun _ => 1) = 1 := Real.circleAverage_const (1 : ℝ) z r
    simp only [GFFObservable.eval, affC, affP]
    rw [hm]
    ring

/-- A covariance of two linear combinations of four variables, expanded bilinearly. -/
theorem cov_sub_mul_sub {P : Measure Ω} [IsFiniteMeasure P] {X₁ X₂ Y₁ Y₂ : Ω → ℝ} (c m d n : ℝ)
    (h₁ : MemLp X₁ 2 P) (h₂ : MemLp X₂ 2 P) (k₁ : MemLp Y₁ 2 P) (k₂ : MemLp Y₂ 2 P) :
    cov[fun ω => c * X₁ ω - m * X₂ ω, fun ω => d * Y₁ ω - n * Y₂ ω; P] =
      c * d * cov[X₁, Y₁; P] - c * n * cov[X₁, Y₂; P] - m * d * cov[X₂, Y₁; P] + m * n * cov[X₂, Y₂; P] := by
  have kk : MemLp (fun ω => d * Y₁ ω - n * Y₂ ω) 2 P := (k₁.const_mul d).sub (k₂.const_mul n)
  rw [covariance_fun_sub_left (h₁.const_mul c) (h₂.const_mul m) kk,
    covariance_fun_sub_right (h₁.const_mul c) (k₁.const_mul d) (k₂.const_mul n),
    covariance_fun_sub_right (h₂.const_mul m) (k₁.const_mul d) (k₂.const_mul n)]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  ring

/-- A variable that vanishes almost surely has zero covariance with anything. -/
theorem covariance_eq_zero_of_ae_zero {P : Measure Ω} {X Y : Ω → ℝ} (hX : X =ᵐ[P] 0) :
    cov[X, Y; P] = 0 := by
  have hEX : P[X] = 0 := by
    rw [integral_congr_ae hX]
    simp
  have hint : (fun ω => (X ω - P[X]) * (Y ω - P[Y])) =ᵐ[P] 0 := by
    filter_upwards [hX] with ω hω
    simp [hEX, hω]
  unfold covariance
  rw [integral_congr_ae hint]
  simp

/-- Gaussian second moments of the observables of a whole-plane GFF. -/
theorem memLp_two_obs {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {o : GFFObservable} (ho : o.IsAdmissible) :
    MemLp (fun ω => o.eval (hC ω) (hcirc ω)) 2 P :=
  (hG.isGaussianProcess.hasGaussianLaw_eval (⟨o, ho⟩ : GFFObservable.Admissible)).memLp
    (by norm_num)

/-- The unit-circle average of a whole-plane GFF is orthogonal to every observable (a.s. zero). -/
theorem cov_circle_one_zero {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {o : GFFObservable} (ho : o.IsAdmissible) :
    wholePlaneGFFCov (GFFObservable.circle 1 0) o = 0 := by
  have h := hG.covariance_eq (GFFObservable.circle 1 0) o one_pos ho
  rw [← h]
  apply covariance_eq_zero_of_ae_zero
  exact IsWholePlaneGFF.ae_circleAverage_one_zero hG


omit [MeasurableSpace Ω] in
/-- The transformed observable at `ω`, as a combination of the original ones (pointwise in `ω`). -/
theorem eval_affine_fun {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {a : ℂ} (b : ℂ)
    (o : GFFObservable) (ω : Ω) :
    o.eval (fun φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) - hcirc ω ‖a‖ b * ∫ x, φ x)
        (fun r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b) =
      affC a o * (affP a b o).eval (hC ω) (hcirc ω) -
        (o.smear fun _ => 1) * (GFFObservable.circle ‖a‖ b).eval (hC ω) (hcirc ω) :=
  eval_affine b (hC ω) (hcirc ω) o

/-- The Gaussian clause of the transformed field. -/
theorem isGaussianProcess_affine {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsGaussianProcess (fun (t : GFFObservable.Admissible) ω =>
      t.1.eval (fun φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) - hcirc ω ‖a‖ b * ∫ x, φ x)
        (fun r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b)) P := by
  classical
  apply IsGaussianProcess.of_isGaussianProcess hG.isGaussianProcess
  rintro ⟨o, ho⟩
  have hp : (affP a b o).IsAdmissible := isAdmissible_affP ha b ho
  have hs : (GFFObservable.circle ‖a‖ b).IsAdmissible := norm_pos_iff.2 ha
  let I : Finset GFFObservable.Admissible := {⟨affP a b o, hp⟩, ⟨GFFObservable.circle ‖a‖ b, hs⟩}
  refine ⟨I, affC a o • ContinuousLinearMap.proj
      (⟨⟨affP a b o, hp⟩, Finset.mem_insert_self _ _⟩ : I) -
      (o.smear fun _ => 1) • ContinuousLinearMap.proj
      (⟨⟨GFFObservable.circle ‖a‖ b, hs⟩, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩ : I),
    fun ω => ?_⟩
  simp only [sub_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  exact eval_affine_fun b o ω

/-- The covariance clause of the transformed field, from the deterministic identity. -/
theorem covariance_affine {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {a : ℂ} (ha : a ≠ 0) (b : ℂ) {o o' : GFFObservable}
    (ho : o.IsAdmissible) (ho' : o'.IsAdmissible) :
    cov[fun ω => o.eval (fun φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) - hcirc ω ‖a‖ b * ∫ x, φ x)
        (fun r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b),
      fun ω => o'.eval (fun φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) - hcirc ω ‖a‖ b * ∫ x, φ x)
        (fun r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b); P] =
      wholePlaneGFFCov o o' := by
  have := hG.isGaussianProcess.isProbabilityMeasure
  have hp : (affP a b o).IsAdmissible := isAdmissible_affP ha b ho
  have hp' : (affP a b o').IsAdmissible := isAdmissible_affP ha b ho'
  have hS : (GFFObservable.circle ‖a‖ b).IsAdmissible := norm_pos_iff.2 ha
  have e1 : (fun ω => o.eval (fun φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) - hcirc ω ‖a‖ b * ∫ x, φ x)
        (fun r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b)) =
      fun ω => affC a o * (affP a b o).eval (hC ω) (hcirc ω) -
        (o.smear fun _ => 1) * (GFFObservable.circle ‖a‖ b).eval (hC ω) (hcirc ω) :=
    funext fun ω => eval_affine_fun b o ω
  have e2 : (fun ω => o'.eval (fun φ => (‖a‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - b) / a)) - hcirc ω ‖a‖ b * ∫ x, φ x)
        (fun r z => hcirc ω (‖a‖ * r) (a * z + b) - hcirc ω ‖a‖ b)) =
      fun ω => affC a o' * (affP a b o').eval (hC ω) (hcirc ω) -
        (o'.smear fun _ => 1) * (GFFObservable.circle ‖a‖ b).eval (hC ω) (hcirc ω) :=
    funext fun ω => eval_affine_fun b o' ω
  rw [e1, e2, cov_sub_mul_sub _ _ _ _ (memLp_two_obs hG hp) (memLp_two_obs hG hS)
    (memLp_two_obs hG hp') (memLp_two_obs hG hS),
    hG.covariance_eq _ _ hp hp', hG.covariance_eq _ _ hp hS, hG.covariance_eq _ _ hS hp',
    hG.covariance_eq _ _ hS hS]
  have hdet := cov_det_identity ha b ho ho'
  have hB := cov_circle_one_zero hG ho'
  linear_combination hdet - (o.smear fun _ => 1) * hB

/-- **`WholePlaneGFFAffineInvariance` is a theorem** (Proposed/LQG.lean): every whole-plane GFF, after the affine
change `F z = a z + b` (`a ≠ 0`), is again a whole-plane GFF, with the recentred pairings and circle averages.
Derived from `IsWholePlaneGFF` alone (no hypothesis beyond it). -/
theorem wholePlaneGFFAffineInvariance_derived (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) : WholePlaneGFFAffineInvariance P hC hcirc := by
  intro hG a ha b
  have := hG.isGaussianProcess.isProbabilityMeasure
  refine
    { measurable_pairing := ?_
      measurable_circle := ?_
      isGaussianProcess := isGaussianProcess_affine hG ha b
      integral_eq_zero := ?_
      covariance_eq := ?_
      ae_continuousOn_circle := ?_ }
  · intro φ hφ
    exact ((hG.measurable_pairing _ (isTestFunction_affine hφ ha b)).const_mul _).sub
      ((hG.measurable_circle ‖a‖ b (norm_pos_iff.2 ha)).mul_const _)
  · intro r z hr
    exact (hG.measurable_circle (‖a‖ * r) (a * z + b) (mul_pos (norm_pos_iff.2 ha) hr)).sub
      (hG.measurable_circle ‖a‖ b (norm_pos_iff.2 ha))
  · intro o ho
    have hp := isAdmissible_affP ha b ho
    have hS : (GFFObservable.circle ‖a‖ b).IsAdmissible := norm_pos_iff.2 ha
    have hint1 := ((memLp_two_obs hG hp).integrable one_le_two).const_mul (affC a o)
    have hint2 := ((memLp_two_obs hG hS).integrable one_le_two).const_mul (o.smear fun _ => 1)
    simp only [eval_affine_fun b o]
    rw [integral_sub hint1 hint2, integral_const_mul, integral_const_mul,
      hG.integral_eq_zero _ hp, hG.integral_eq_zero _ hS]
    ring
  · intro o o' ho ho'
    exact covariance_affine hG ha b ho ho'
  · filter_upwards [hG.ae_continuousOn_circle] with ω hω
    have hmap : MapsTo (fun p : ℝ × ℂ => (‖a‖ * p.1, a * p.2 + b)) (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) :=
      fun p hp => ⟨mul_pos (norm_pos_iff.2 ha) hp.1, mem_univ _⟩
    have hcont : Continuous (fun p : ℝ × ℂ => (‖a‖ * p.1, a * p.2 + b)) := by fun_prop
    exact (hω.comp hcont.continuousOn hmap).sub continuousOn_const

end HarmonicBalls
