import HarmonicBalls.Defs.GFF
import HarmonicBalls.FirstPass.S11c.WholePlaneTranslate11_7

/-!
# The translated whole-plane GFF is a whole-plane GFF (Lemma 11.7)

For a whole-plane GFF `(hC, hcirc)` and `z ∈ ℂ`, the field `h(· + z) - h_1(z)` is again a whole-plane GFF:
`hC' ω φ = hC ω (φ(· - z)) - hcirc ω 1 z · ∫ φ` and `hcirc' ω r x = hcirc ω r (x + z) - hcirc ω 1 z`.
This is the normalized translation lemma `hW'` used by the rooted-measure chain of Lemma 11.7
(`ae_rootedMeasure_eq_translate`, `fixedRoot_null_of_origin`). No external input: each translated observable is a finite
linear combination of observables of the original field (Gaussianity, Mathlib `IsGaussianProcess.of_isGaussianProcess`),
and the covariance is the kernel identity of `WholePlaneTranslate11_7.lean`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HarmonicBalls.S11c

open HarmonicBalls

/-- The pairings of the translated field. -/
noncomputable def translatedPairing {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ) (ω : Ω)
    (φ : ℂ → ℝ) : ℝ :=
  hC ω (fun y => φ (y - z)) - hcirc ω 1 z * ∫ x, φ x

/-- The circle averages of the translated field. -/
def translatedCircle {Ω : Type*} (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ) (ω : Ω) (r : ℝ) (x : ℂ) : ℝ :=
  hcirc ω r (x + z) - hcirc ω 1 z

/-- The admissible observable `shift o` of the translated index. -/
def shiftAdm (z : ℂ) (o : GFFObservable.Admissible) : GFFObservable.Admissible :=
  ⟨shiftObs z o.1, shiftObs_isAdmissible z o.2⟩

/-- The unit circle at `z`, as an admissible observable. -/
def unitCircleAdm (z : ℂ) : GFFObservable.Admissible :=
  ⟨.circle 1 z, zero_lt_one⟩

lemma eval_translated {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ) (ω : Ω)
    (o : GFFObservable.Admissible) :
    o.1.eval (translatedPairing hC hcirc z ω) (translatedCircle hcirc z ω) =
      (shiftAdm z o).1.eval (hC ω) (hcirc ω) - mass o.1 * (unitCircleAdm z).1.eval (hC ω) (hcirc ω) := by
  obtain ⟨o, ho⟩ := o
  cases o with
  | pairing φ =>
    have hm : mass (.pairing φ) = ∫ x, φ x := by
      simp [mass, GFFObservable.smear]
    simp only [GFFObservable.eval, shiftAdm, shiftObs, unitCircleAdm, translatedPairing, hm]
    ring
  | circle r x =>
    have hm : mass (.circle r x) = 1 := smear_mass_circle r x
    simp only [GFFObservable.eval, shiftAdm, shiftObs, unitCircleAdm, translatedCircle, hm, one_mul]


variable {Ω : Type*} [MeasurableSpace Ω]

lemma isGaussianProcess_translated {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (z : ℂ) :
    IsGaussianProcess (fun (o : GFFObservable.Admissible) ω =>
      o.1.eval (translatedPairing hC hcirc z ω) (translatedCircle hcirc z ω)) P := by
  classical
  refine IsGaussianProcess.of_isGaussianProcess hh.isGaussianProcess ?_
  intro s
  let a : GFFObservable.Admissible := shiftAdm z s
  let b : GFFObservable.Admissible := unitCircleAdm z
  let I : Finset GFFObservable.Admissible := {a, b}
  let ia : I := ⟨a, Finset.mem_insert_self _ _⟩
  let ib : I := ⟨b, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
  let L0 : (I → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj ia - mass s.1 • LinearMap.proj ib
  refine ⟨I, LinearMap.toContinuousLinearMap L0, fun ω => ?_⟩
  rw [eval_translated]
  simp [L0, I, ia, ib, a, b, Finset.restrict]

lemma integral_translated {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) (z : ℂ)
    (o : GFFObservable.Admissible) :
    ∫ ω, o.1.eval (translatedPairing hC hcirc z ω) (translatedCircle hcirc z ω) ∂P = 0 := by
  have hint : ∀ o : GFFObservable.Admissible, Integrable (fun ω => o.1.eval (hC ω) (hcirc ω)) P :=
    fun o => (hh.isGaussianProcess.hasGaussianLaw_eval o).integrable
  simp only [eval_translated]
  rw [integral_sub (hint _) ((hint _).const_mul _), integral_const_mul,
    hh.integral_eq_zero (shiftAdm z o).1 (shiftAdm z o).2,
    hh.integral_eq_zero (unitCircleAdm z).1 (unitCircleAdm z).2]
  ring

/-- Covariance of two linear combinations `A - m B` and `C - m' D` of `L²` variables. -/
lemma covariance_linear_comb {P : Measure Ω} [IsProbabilityMeasure P] {A B C D : Ω → ℝ}
    (hA : MemLp A 2 P) (hB : MemLp B 2 P) (hC : MemLp C 2 P) (hD : MemLp D 2 P) (m m' : ℝ) :
    cov[fun ω => A ω - m * B ω, fun ω => C ω - m' * D ω; P] =
      cov[A, C; P] - m' * cov[A, D; P] - m * cov[B, C; P] + m * m' * cov[B, D; P] := by
  have hZ : MemLp (fun ω => C ω - m' * D ω) 2 P := hC.sub (hD.const_mul m')
  have hmB : MemLp (fun ω => m * B ω) 2 P := hB.const_mul m
  have h1 : cov[fun ω => A ω - m * B ω, fun ω => C ω - m' * D ω; P] =
      cov[A, fun ω => C ω - m' * D ω; P] - cov[fun ω => m * B ω, fun ω => C ω - m' * D ω; P] :=
    covariance_sub_left hA hmB hZ
  have h2 : cov[A, fun ω => C ω - m' * D ω; P] = cov[A, C; P] - m' * cov[A, D; P] := by
    rw [show (fun ω => C ω - m' * D ω) = C - (fun ω => m' * D ω) from rfl,
      covariance_sub_right hA hC (hD.const_mul m'), covariance_const_mul_right]
  have h3 : cov[fun ω => m * B ω, fun ω => C ω - m' * D ω; P] =
      m * (cov[B, C; P] - m' * cov[B, D; P]) := by
    rw [covariance_const_mul_left, show (fun ω => C ω - m' * D ω) = C - (fun ω => m' * D ω) from rfl,
      covariance_sub_right hB hC (hD.const_mul m'), covariance_const_mul_right]
  rw [h1, h2, h3]
  ring

/-- Covariance of the translated observables is the kernel of the original field evaluated at `o, o'`. -/
lemma covariance_translated {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) (z : ℂ)
    (o o' : GFFObservable.Admissible) :
    cov[fun ω => o.1.eval (translatedPairing hC hcirc z ω) (translatedCircle hcirc z ω),
      fun ω => o'.1.eval (translatedPairing hC hcirc z ω) (translatedCircle hcirc z ω); P] =
      wholePlaneGFFCov o.1 o'.1 := by
  have hm : ∀ X : GFFObservable.Admissible, MemLp (fun ω => X.1.eval (hC ω) (hcirc ω)) 2 P :=
    fun X => (hh.isGaussianProcess.hasGaussianLaw_eval X).memLp_two
  simp only [eval_translated]
  rw [covariance_linear_comb (hm _) (hm (unitCircleAdm z)) (hm _) (hm (unitCircleAdm z))]
  rw [covariance_comm (μ := P) (X := fun ω => (unitCircleAdm z).1.eval (hC ω) (hcirc ω))]
  rw [hh.covariance_eq _ _ (shiftAdm z o).2 (shiftAdm z o').2,
    hh.covariance_eq _ _ (shiftAdm z o).2 (unitCircleAdm z).2,
    hh.covariance_eq _ _ (shiftAdm z o').2 (unitCircleAdm z).2,
    hh.covariance_eq _ _ (unitCircleAdm z).2 (unitCircleAdm z).2]
  have key := wholePlaneGFFCov_shift_combo z o.2 o'.2
  simp only [shiftAdm, unitCircleAdm] at key ⊢
  linear_combination key

/-- Normalized translation of a whole-plane GFF (the `hW'` of Lemma 11.7): for `z ∈ ℂ` the field
`h(· + z) - h_1(z)` with pairings `translatedPairing` and circle averages `translatedCircle` is a whole-plane GFF.
Source of the kernel identity: whole-plane covariance `-log|x-y| + log max(|x|,1) + log max(|y|,1)` and the affine
invariance modulo constants (Holden-Sun arXiv:1610.05272 proof of Lemma 4.2; Duplantier-Miller-Sheffield
arXiv:1409.7055 Section 4.1); here it is derived from `IsWholePlaneGFF` itself, with no external input. -/
theorem isWholePlaneGFF_translate {P : Measure Ω} [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) (z : ℂ) :
    IsWholePlaneGFF P (translatedPairing hC hcirc z) (translatedCircle hcirc z) where
  measurable_pairing φ hφ :=
    (hh.measurable_pairing _ (isTestFunction_shift hφ z)).sub
      ((hh.measurable_circle 1 z zero_lt_one).mul_const _)
  measurable_circle r x hr :=
    (hh.measurable_circle r (x + z) hr).sub (hh.measurable_circle 1 z zero_lt_one)
  isGaussianProcess := isGaussianProcess_translated hh z
  integral_eq_zero o ho := integral_translated hh z ⟨o, ho⟩
  covariance_eq o o' ho ho' := covariance_translated hh z ⟨o, ho⟩ ⟨o', ho'⟩
  ae_continuousOn_circle := by
    filter_upwards [hh.ae_continuousOn_circle] with ω hω
    have hq : ContinuousOn (fun p : ℝ × ℂ => (p.1, p.2 + z)) (Ioi 0 ×ˢ univ) :=
      (continuous_fst.prodMk (continuous_snd.add continuous_const)).continuousOn
    have hmaps : MapsTo (fun p : ℝ × ℂ => (p.1, p.2 + z)) (Ioi 0 ×ˢ univ) (Ioi 0 ×ˢ univ) :=
      fun p hp => ⟨hp.1, mem_univ _⟩
    exact (hω.comp hq hmaps).sub continuousOn_const

end HarmonicBalls.S11c
