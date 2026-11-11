import HarmonicBalls.Proofs.GFF.GaussianCylinderMixing
import HarmonicBalls.Proofs.Sec6.ContinuousWeylCircleAverage

/-! # Finite observable mixing under normalized dilation

The covariance-potential and Gaussian-process developments imported here use
Leonardo Bonanno's work through the pinned Lattice-Probability dependency.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ProbabilityTheory

namespace HarmonicBalls

/-- The dyadic normalized-dilation covariance limit for two arbitrary
admissible pairing or circle observables. -/
def FullObservableDilationCovarianceDecay
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (o q : GFFObservable.Admissible) : Prop :=
  Tendsto (fun n : ℕ => cov[fun ω => o.1.eval (hC ω) (hcirc ω),
    fun ω => q.1.eval
      (affinePairing hC hcirc (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ)) 0 ω)
      (affineCircle hcirc (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ)) 0 ω); P])
    atTop (𝓝 0)

/-- The covariance kernel smeared against a fixed observable. -/
noncomputable def observableCovariancePotential (o : GFFObservable) (x : ℂ) : ℝ :=
  o.smear (fun y => wholePlaneCov x y)

/-- Pairing and positive-radius circle covariance potentials are continuous. -/
theorem continuous_observableCovariancePotential (o : GFFObservable.Admissible) :
    Continuous (observableCovariancePotential o.1) := by
  rcases o with ⟨o, ho⟩
  cases o with
  | pairing φ =>
      exact continuous_wholePlaneCov_potential_of_compact_support ho.1.continuous ho.2.1
  | circle r z =>
      exact continuous_circleAverage_wholePlaneCov ho z

/-- Circle averages of a continuous potential converge to its value at the
origin as both radius and center converge to zero. -/
theorem tendsto_circleAverage_origin {u : ℂ → ℝ} (hu : Continuous u)
    {r : ℕ → ℝ} {z : ℕ → ℂ}
    (hr : Tendsto r atTop (𝓝 0)) (hz : Tendsto z atTop (𝓝 0)) :
    Tendsto (fun n => Real.circleAverage u (z n) (r n)) atTop (𝓝 (u 0)) := by
  have ht := (Section6.continuous_circleAverage_radius_center hu).tendsto (0, 0)
  have hlim := ht.comp (hr.prodMk_nhds hz)
  change Tendsto (fun n => Real.circleAverage u (z n) (r n)) atTop
    (𝓝 (Real.circleAverage u 0 0)) at hlim
  simpa only [Real.circleAverage_zero] using hlim

/-- Covariance with a circle is the circle average of the covariance
potential, in the order supplied by the GFF covariance identity. -/
theorem IsWholePlaneGFF.covariance_observable_circle_eq_potential
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (o : GFFObservable.Admissible)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    cov[fun ω => o.1.eval (hC ω) (hcirc ω), fun ω => hcirc ω r z; P] =
      Real.circleAverage (observableCovariancePotential o.1) z r := by
  rw [covariance_comm]
  have hc := h.covariance_eq (.circle r z) o.1 hr o.2
  change cov[fun ω => hcirc ω r z, fun ω => o.1.eval (hC ω) (hcirc ω); P] =
    Real.circleAverage (observableCovariancePotential o.1) z r at hc
  exact hc

/-- Covariance with an affine-normalized circle is the difference of two
circle averages of the same continuous potential. -/
theorem IsWholePlaneGFF.covariance_observable_affineCircle_eq_potential
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (o : GFFObservable.Admissible)
    {r : ℝ} (hr : 0 < r) (z : ℂ) {a : ℂ} (ha : a ≠ 0) :
    cov[fun ω => o.1.eval (hC ω) (hcirc ω),
      fun ω => affineCircle hcirc a 0 ω r z; P] =
      Real.circleAverage (observableCovariancePotential o.1) (a * z) (‖a‖ * r) -
        Real.circleAverage (observableCovariancePotential o.1) 0 ‖a‖ := by
  let := h.isProbabilityMeasure
  have ho := (h.isGaussianProcess.hasGaussianLaw_eval o).memLp_two
  have hp := (h.hasGaussianLaw_circle (mul_pos (norm_pos_iff.mpr ha) hr) (a * z)).memLp_two
  have hq := (h.hasGaussianLaw_circle (norm_pos_iff.mpr ha) 0).memLp_two
  simp only [affineCircle, add_zero]
  rw [covariance_fun_sub_right ho hp hq,
    h.covariance_observable_circle_eq_potential o (mul_pos (norm_pos_iff.mpr ha) hr),
    h.covariance_observable_circle_eq_potential o (norm_pos_iff.mpr ha)]

/-- The affine-normalized pairing has covariance equal to an integral of
the covariance potential minus its normalizing circle average. -/
theorem IsWholePlaneGFF.covariance_observable_affinePairing_eq_potential
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (o : GFFObservable.Admissible)
    {ψ : ℂ → ℝ} (hψ : IsTestFunction univ ψ) {a : ℂ} (ha : a ≠ 0) :
    cov[fun ω => o.1.eval (hC ω) (hcirc ω),
      fun ω => affinePairing hC hcirc a 0 ω ψ; P] =
      (∫ y, ψ y * observableCovariancePotential o.1 (a * y)) -
        (∫ y, ψ y) * Real.circleAverage (observableCovariancePotential o.1) 0 ‖a‖ := by
  let := h.isProbabilityMeasure
  let ψa : ℂ → ℝ := fun y => ψ ((y - 0) / a)
  have hψa : IsTestFunction univ ψa := hψ.comp_inverse_complex_affine ha 0
  have ho := (h.isGaussianProcess.hasGaussianLaw_eval o).memLp_two
  have hp := (h.isGaussianProcess.hasGaussianLaw_eval
    (⟨.pairing ψa, hψa⟩ : GFFObservable.Admissible)).memLp_two
  change MemLp (fun ω => hC ω ψa) 2 P at hp
  have hq := (h.hasGaussianLaw_circle (norm_pos_iff.mpr ha) 0).memLp_two
  have hc := h.covariance_eq (.pairing ψa) o.1 hψa o.2
  change cov[fun ω => hC ω ψa, fun ω => o.1.eval (hC ω) (hcirc ω); P] =
    ∫ y, ψa y * observableCovariancePotential o.1 y at hc
  have hn : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  have he : (fun ω => affinePairing hC hcirc a 0 ω ψ) =
      fun ω => (‖a‖ ^ 2)⁻¹ * hC ω ψa - (∫ y, ψ y) * hcirc ω ‖a‖ 0 := by
    funext ω
    simp only [affinePairing, ψa, mul_comm]
  rw [he, covariance_fun_sub_right ho (hp.const_mul _) (hq.const_mul _),
    covariance_const_mul_right, covariance_const_mul_right,
    covariance_comm (fun ω => o.1.eval (hC ω) (hcirc ω)) (fun ω => hC ω ψa), hc,
    h.covariance_observable_circle_eq_potential o (norm_pos_iff.mpr ha)]
  change (‖a‖ ^ 2)⁻¹ * (∫ y, ψ ((y - 0) / a) *
    observableCovariancePotential o.1 y) - _ = _
  rw [integral_inverse_complex_affine_mul ψ _ ha 0]
  simp only [add_zero, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- Every admissible observable becomes asymptotically uncorrelated with
every admissible normalized dyadic dilation. -/
theorem IsWholePlaneGFF.fullObservableDilationCovarianceDecay
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (o q : GFFObservable.Admissible) :
    FullObservableDilationCovarianceDecay P hC hcirc o q := by
  let t : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ n
  let a : ℕ → ℂ := fun n => (t n : ℂ)
  let u := observableCovariancePotential o.1
  have hu : Continuous u := continuous_observableCovariancePotential o
  have ht : Tendsto t atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have htpos (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have ha (n : ℕ) : a n ≠ 0 := Complex.ofReal_ne_zero.mpr (htpos n).ne'
  have hanorm (n : ℕ) : ‖a n‖ = t n := by
    simp only [a, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (htpos n)]
  have havg (r : ℝ) (z : ℂ) : Tendsto (fun n =>
      Real.circleAverage u (a n * z) (‖a n‖ * r)) atTop (𝓝 (u 0)) := by
    have hr : Tendsto (fun n => ‖a n‖ * r) atTop (𝓝 0) := by
      simpa only [hanorm, zero_mul] using ht.mul_const r
    have hz : Tendsto (fun n => a n * z) atTop (𝓝 0) := by
      have hc := (Complex.continuous_ofReal.tendsto 0).comp ht
      change Tendsto (fun n => (t n : ℂ)) atTop (𝓝 0) at hc
      simpa only [a, zero_mul] using hc.mul_const z
    exact tendsto_circleAverage_origin hu hr hz
  have hbase : Tendsto (fun n => Real.circleAverage u 0 ‖a n‖) atTop (𝓝 (u 0)) := by
    have hx := havg 1 0
    simpa only [mul_zero, mul_one] using hx
  rcases q with ⟨q, hq⟩
  cases q with
  | pairing ψ =>
      have hi := tendsto_integral_mul_dyadic_comp hq.1.continuous hq.2.1 hu
      have hlim := hi.sub (hbase.const_mul (∫ y, ψ y))
      have hlim' : Tendsto (fun n => (∫ y, ψ y * u (a n * y)) -
          (∫ y, ψ y) * Real.circleAverage u 0 ‖a n‖) atTop (𝓝 0) := by
        simpa only [t, a, sub_self] using hlim
      change Tendsto (fun n => cov[fun ω => o.1.eval (hC ω) (hcirc ω),
        fun ω => affinePairing hC hcirc (a n) 0 ω ψ; P]) atTop (𝓝 0)
      apply hlim'.congr'
      filter_upwards with n
      exact (h.covariance_observable_affinePairing_eq_potential o hq (ha n)).symm
  | circle r z =>
      have hlim := (havg r z).sub hbase
      have hlim' : Tendsto (fun n => Real.circleAverage u (a n * z) (‖a n‖ * r) -
          Real.circleAverage u 0 ‖a n‖) atTop (𝓝 0) := by
        simpa only [sub_self] using hlim
      change Tendsto (fun n => cov[fun ω => o.1.eval (hC ω) (hcirc ω),
        fun ω => affineCircle hcirc (a n) 0 ω r z; P]) atTop (𝓝 0)
      apply hlim'.congr'
      filter_upwards with n
      exact (h.covariance_observable_affineCircle_eq_potential o hq z (ha n)).symm

/-- Each admissible observable is measurable. -/
theorem IsWholePlaneGFF.measurable_observable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (o : GFFObservable.Admissible) :
    Measurable (fun ω => o.1.eval (hC ω) (hcirc ω)) := by
  rcases o with ⟨o, ho⟩
  cases o with
  | pairing φ => exact h.measurable_pairing φ ho
  | circle r z => exact h.measurable_circle r z ho

/-- The uncentered image of an observable under a nonconstant affine map. -/
def affineImageObservable (a : ℂ) (ha : a ≠ 0) (q : GFFObservable.Admissible) :
    GFFObservable.Admissible :=
  match q with
  | ⟨.pairing ψ, hψ⟩ => ⟨.pairing (fun y => ψ ((y - 0) / a)),
      hψ.comp_inverse_complex_affine ha 0⟩
  | ⟨.circle r z, hr⟩ => ⟨.circle (‖a‖ * r) (a * z + 0),
      mul_pos (norm_pos_iff.mpr ha) hr⟩

/-- Coefficients of the uncentered affine observable and reference circle. -/
noncomputable def affineObservableWeights (a : ℂ) (q : GFFObservable) : ℝ × ℝ :=
  match q with
  | .pairing ψ => ((‖a‖ ^ 2)⁻¹, ∫ y, ψ y)
  | .circle _ _ => (1, 1)

/-- Finite collections of original and recentered affine observables are
jointly Gaussian. -/
theorem IsWholePlaneGFF.isGaussianProcess_original_affine_observables
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {m k : ℕ}
    (o : Fin m → GFFObservable.Admissible) (q : Fin k → GFFObservable.Admissible)
    {a : ℂ} (ha : a ≠ 0) :
    IsGaussianProcess (fun i ω => Fin.addCases
      (motive := fun _ : Fin (m+k) => ℝ)
      (fun j => (o j).1.eval (hC ω) (hcirc ω))
      (fun j => (q j).1.eval (affinePairing hC hcirc a 0 ω)
        (affineCircle hcirc a 0 ω)) i) P := by
  let p : GFFObservable.Admissible := ⟨.circle ‖a‖ 0, norm_pos_iff.mpr ha⟩
  let v : Fin (m+k) → GFFObservable.Admissible := Fin.addCases o (fun j => affineImageObservable a ha (q j))
  let c : Fin (m+k) → ℝ := Fin.addCases (fun _ => 1) (fun j => (affineObservableWeights a (q j).1).1)
  let d : Fin (m+k) → ℝ := Fin.addCases (fun _ => 0) (fun j => (affineObservableWeights a (q j).1).2)
  have hg := h.isGaussianProcess_weighted_recentered v p c d
  convert hg using 1
  funext i ω
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [v, c, d, p]
  · generalize heq : q j = qj
    rcases qj with ⟨qj, hqj⟩
    cases qj with
    | pairing ψ => simp [v, c, d, p, heq, affineImageObservable, affineObservableWeights,
        affinePairing, GFFObservable.eval, mul_comm]
    | circle r z => simp [v, c, d, p, heq, affineImageObservable, affineObservableWeights,
        affineCircle, GFFObservable.eval]

/-- Finite original and normalized dyadic observable vectors converge jointly
to independent copies of their original laws. -/
theorem IsWholePlaneGFF.tendstoInDistribution_dyadic_observables
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {m k : ℕ}
    (o : Fin m → GFFObservable.Admissible) (q : Fin k → GFFObservable.Admissible) :
    letI := h.isProbabilityMeasure
    TendstoInDistribution
      (fun n ω => (fun i => (o i).1.eval (hC ω) (hcirc ω), fun j => (q j).1.eval
        (affinePairing hC hcirc (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ)) 0 ω)
        (affineCircle hcirc (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ)) 0 ω))) atTop
      (fun ω : Ω × Ω => (fun i => (o i).1.eval (hC ω.1) (hcirc ω.1),
        fun j => (q j).1.eval (hC ω.2) (hcirc ω.2))) (fun _ => P) (P.prod P) := by
  let := h.isProbabilityMeasure
  let a : ℕ → ℂ := fun n => (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ))
  have ha (n : ℕ) : a n ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  let X : ℕ → Fin (m+k) → Ω → ℝ := fun n i ω => Fin.addCases
    (motive := fun _ : Fin (m+k) => ℝ)
    (fun j => (o j).1.eval (hC ω) (hcirc ω))
    (fun j => (q j).1.eval (affinePairing hC hcirc (a n) 0 ω)
      (affineCircle hcirc (a n) 0 ω)) i
  have hg (n : ℕ) : IsWholePlaneGFF P (affinePairing hC hcirc (a n) 0)
      (affineCircle hcirc (a n) 0) := h.complex_affine (ha n) 0
  have hX (n : ℕ) : IsGaussianProcess (X n) P :=
    h.isGaussianProcess_original_affine_observables o q (ha n)
  have hXm (n : ℕ) (i : Fin (m+k)) : Measurable (X n i) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [X, Fin.addCases_left] using h.measurable_observable (o j)
    · simpa only [X, Fin.addCases_right] using
        (hg n).measurable_observable (q j)
  have hX0 (n : ℕ) (i : Fin (m+k)) : ∫ ω, X n i ω ∂P = 0 := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [X, Fin.addCases_left] using h.integral_eq_zero (o j).1 (o j).2
    · simpa only [X, Fin.addCases_right] using
        (hg n).integral_eq_zero (q j).1 (q j).2
  have hAA (n : ℕ) (i j : Fin m) :
      cov[X n (Fin.castAdd k i), X n (Fin.castAdd k j); P] =
        cov[X 0 (Fin.castAdd k i), X 0 (Fin.castAdd k j); P] := by simp [X]
  have hBB (n : ℕ) (i j : Fin k) :
      cov[X n (Fin.natAdd m i), X n (Fin.natAdd m j); P] =
        cov[X 0 (Fin.natAdd m i), X 0 (Fin.natAdd m j); P] := by
    have h1 := (hg n).covariance_eq (q i).1 (q j).1 (q i).2 (q j).2
    have h2 := (hg 0).covariance_eq (q i).1 (q j).1 (q i).2 (q j).2
    simpa only [X, Fin.addCases_right] using h1.trans h2.symm
  have hAB (i : Fin m) (j : Fin k) : Tendsto (fun n =>
      cov[X n (Fin.castAdd k i), X n (Fin.natAdd m j); P]) atTop (𝓝 0) := by
    simpa only [X, Fin.addCases_left, Fin.addCases_right, a,
      FullObservableDilationCovarianceDecay] using h.fullObservableDilationCovarianceDecay (o i) (q j)
  have ht := tendstoInDistribution_gaussian_independent_blocks hX hXm hX0 hAA hBB hAB
  have heq : (fun ω : Ω × Ω => (fun i => X 0 (Fin.castAdd k i) ω.1,
      fun j => X 0 (Fin.natAdd m j) ω.2)) =ᵐ[P.prod P]
      (fun ω : Ω × Ω => (fun i => (o i).1.eval (hC ω.1) (hcirc ω.1),
        fun j => (q j).1.eval (hC ω.2) (hcirc ω.2))) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae h.ae_circleAverage_one_zero] with ω hω
    apply Prod.ext
    · simp [X]
    · funext j
      generalize he : q j = qj
      rcases qj with ⟨qj, hqj⟩
      cases qj with
      | pairing ψ => simp [X, a, he, affinePairing, GFFObservable.eval, hω]
      | circle r z => simp [X, a, he, affineCircle, GFFObservable.eval, hω]
  have ht' := TendstoInDistribution.congr (fun n => Filter.Eventually.of_forall fun _ => rfl) heq ht
  simpa only [X, Fin.addCases_left, Fin.addCases_right, a] using ht'

/-- Bounded continuous functions of the two observable blocks have
asymptotically factorized expectations. -/
theorem IsWholePlaneGFF.tendsto_integral_dyadic_observables_product
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {m k : ℕ}
    (o : Fin m → GFFObservable.Admissible) (q : Fin k → GFFObservable.Admissible)
    (f : BoundedContinuousFunction (Fin m → ℝ) ℝ)
    (g : BoundedContinuousFunction (Fin k → ℝ) ℝ) :
    Tendsto (fun n => ∫ ω, f (fun i => (o i).1.eval (hC ω) (hcirc ω)) *
      g (fun j => (q j).1.eval
        (affinePairing hC hcirc (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ)) 0 ω)
        (affineCircle hcirc (((((2 : ℝ)⁻¹ ^ n) : ℝ) : ℂ)) 0 ω)) ∂P)
      atTop (𝓝 ((∫ ω, f (fun i => (o i).1.eval (hC ω) (hcirc ω)) ∂P) *
        (∫ ω, g (fun j => (q j).1.eval (hC ω) (hcirc ω)) ∂P))) := by
  let := h.isProbabilityMeasure
  exact tendsto_cylinder_product_of_tendstoInDistribution
    (h.tendstoInDistribution_dyadic_observables o q) f g


end HarmonicBalls
