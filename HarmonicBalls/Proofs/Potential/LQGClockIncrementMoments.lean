import HarmonicBalls.Proofs.Potential.LQGClockProfileZeroOne

/-! # Moments of the dyadic clock increments along a fixed path

For the whole-plane GFF `h` (no insertion), a fixed path `w`, times `a ≤ b` and `ε = 2^{-k}`, let
`J_k(w) = ∫_a^b ε^{γ²/2} e^{γ h_ε(w_v)} dv`, read through the profile densities
(`profileDensity`). With `A(z) = avg_{∂B_ε(z)} log max(|·|, 1)` and the averaged potential
`Π(z, z') = avg_{x ∈ ∂B_ε(z)} log max(ε, |x - z'|)`, the circle-average covariances are
`Var h_ε(z) = 2 A(z) - log ε` and `Cov(h_ε(z), h_ε(z')) = A(z) + A(z') - Π(z, z')`
(`LatticeProb.Gauss.wholePlaneGFFCov_circle_circle_eq`). Hence

* `E[ε^{γ²/2} e^{γ h_ε(z)}] = e^{γ² A(z)} ≥ 1`, and `E[J_k(w)] ≥ b - a`;
* `E[ε^{γ²} e^{γ (h_ε(z) + h_ε(z'))}] = e^{2 γ² (A(z) + A(z'))} e^{-γ² Π(z, z')}
  ≤ (N + 1)^{4γ²} 2^{γ²} |z - z'|^{-γ²}` for `|z|, |z'| ≤ N`, since `A ≤ log (N + 1)` and
  `Π(z, z') ≥ log (|z - z'| / 2)`; so `E[J_k(w)²] ≤ (N + 1)^{4γ²} 2^{γ²} ∫∫ |w_s - w_t|^{-γ²}`
  when `|w| ≤ N` on `(a, b]`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

theorem measurable_dyadicProfile (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) :
    Measurable (fun ω => fun p : ℕ × ℂ => hcirc ω (dyadicScale p.1) p.2) :=
  measurable_pi_iff.mpr fun p => hh.measurable_circle _ _ (dyadicScale_pos p.1)

/-- A centred Gaussian variable `Z` has `E e^Z = e^{Var Z / 2}`. -/
theorem integral_exp_eq_of_hasGaussianLaw [IsProbabilityMeasure P] {Z : Ω → ℝ}
    (hZ : HasGaussianLaw Z P) (hm : P[Z] = 0) :
    Integrable (fun ω => Real.exp (Z ω)) P ∧
      ∫ ω, Real.exp (Z ω) ∂P = Real.exp (Var[Z; P] / 2) := by
  have hlaw : HasLaw Z (gaussianReal 0 Var[Z; P].toNNReal) P :=
    ⟨hZ.aemeasurable, by rw [hZ.map_eq_gaussianReal, hm]⟩
  have hm1 := mgf_gaussianReal hlaw 1
  have hv : (Var[Z; P].toNNReal : ℝ) = Var[Z; P] := Real.coe_toNNReal _ (variance_nonneg _ _)
  constructor
  · have : 0 < mgf Z P 1 := by rw [hm1]; positivity
    simpa using (mgf_pos_iff.mp this)
  · have : mgf Z P 1 = ∫ ω, Real.exp (Z ω) ∂P := by simp [mgf]
    rw [← this, hm1, hv]
    ring_nf

omit [MeasurableSpace Ω] in
theorem mem_span_circle {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (fun ω => hcirc ω r z) ∈ Submodule.span ℝ (Set.range
      fun (o : LatticeProb.Gauss.GFFObservable.Admissible) ω => o.1.eval (hC ω) (hcirc ω)) :=
  Submodule.subset_span ⟨⟨.circle r z, hr⟩, rfl⟩

theorem hasGaussianLaw_of_mem_span (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {Z : Ω → ℝ} (hZ : Z ∈ Submodule.span ℝ (Set.range
      fun (o : LatticeProb.Gauss.GFFObservable.Admissible) ω => o.1.eval (hC ω) (hcirc ω))) :
    HasGaussianLaw Z P :=
  (LatticeProb.GaussIndep.isGaussianProcess_of_mem_span (Y := fun (_ : Unit) => Z)
    hh.isGaussianProcess fun _ => hZ).hasGaussianLaw_eval ()

/-- `E[ε^{γ²/2} e^{γ h_ε(z)}] = e^{γ² A(z)}`. -/
theorem lintegral_ofReal_dyadicDensity (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (γ : ℝ) (k : ℕ) (z : ℂ) :
    ∫⁻ ω, ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * hcirc ω (dyadicScale k) z)) ∂P =
      ENNReal.ofReal (Real.exp (γ ^ 2 *
        Real.circleAverage LatticeProb.Gauss.logMaxAbs z (dyadicScale k))) := by
  have hPm := hh.isProbabilityMeasure
  have hε := dyadicScale_pos k
  have hfun : (fun ω => γ * hcirc ω (dyadicScale k) z) =
      γ • (fun ω => hcirc ω (dyadicScale k) z) := by
    funext ω
    simp
  have hZ : HasGaussianLaw (fun ω => γ * hcirc ω (dyadicScale k) z) P := by
    rw [hfun]
    exact hasGaussianLaw_of_mem_span hh (Submodule.smul_mem _ γ (mem_span_circle hε z))
  have hX0 : P[fun ω => hcirc ω (dyadicScale k) z] = 0 :=
    hh.integral_eq_zero (.circle (dyadicScale k) z) hε
  have hm : P[fun ω => γ * hcirc ω (dyadicScale k) z] = 0 := by
    rw [integral_const_mul, hX0, mul_zero]
  obtain ⟨hint, heq⟩ := integral_exp_eq_of_hasGaussianLaw hZ hm
  have hvar : Var[fun ω => γ * hcirc ω (dyadicScale k) z; P] =
      γ ^ 2 * (2 * Real.circleAverage LatticeProb.Gauss.logMaxAbs z (dyadicScale k) -
        Real.log (dyadicScale k)) := by
    rw [variance_const_mul, ← covariance_self (hh.measurable_circle _ _ hε).aemeasurable,
      hh.covariance_circle_circle hε hε, LatticeProb.Gauss.wholePlaneGFFCov_circle_circle_eq hε,
      LatticeProb.Gauss.circlePairPotential_self_center hε.le, max_self]
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
    (Filter.Eventually.of_forall fun ω => by positivity), integral_const_mul, heq, hvar,
    Real.rpow_def_of_pos hε, ← Real.exp_add]
  congr 2
  ring

theorem le_circlePairPotential_of_ne {ε : ℝ} (hε : 0 < ε) {z z' : ℂ} (hzz : z ≠ z') :
    Real.log (‖z - z'‖ / 2) ≤ LatticeProb.Gauss.circlePairPotential z ε z' ε := by
  have hd : 0 < ‖z - z'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzz)
  unfold LatticeProb.Gauss.circlePairPotential
  have hcp : CircleIntegrable (fun x : ℂ => Real.log (max ε ‖x - z'‖)) z ε :=
    (LatticeProb.Gauss.continuous_log_max_norm_sub hε z').continuousOn.circleIntegrable'
  have h := Real.circleAverage_mono (c := z) (R := ε) (f₁ := fun _ : ℂ => Real.log (‖z - z'‖ / 2))
    continuous_const.continuousOn.circleIntegrable' hcp (fun x hx => by
      have hx' : ‖x - z‖ = ε := (mem_sphere_iff_norm.1 hx).trans (abs_of_pos hε)
      have htri : ‖z - z'‖ ≤ ‖x - z‖ + ‖x - z'‖ := by
        have := norm_sub_le (z - x) (z' - x)
        rw [sub_sub_sub_cancel_right, norm_sub_rev z x, norm_sub_rev z' x] at this
        linarith
      refine Real.log_le_log (by positivity) ?_
      rcases le_or_gt (‖z - z'‖) (2 * ε) with h2 | h2
      · exact le_max_of_le_left (by linarith)
      · exact le_max_of_le_right (by linarith))
  rwa [Real.circleAverage_const] at h

theorem circleAverage_logMaxAbs_le_log_add_one {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {N : ℝ} {z : ℂ}
    (hz : ‖z‖ ≤ N) :
    Real.circleAverage LatticeProb.Gauss.logMaxAbs z ε ≤ Real.log (N + 1) := by
  have hN : 0 ≤ N := (norm_nonneg z).trans hz
  refine Real.circleAverage_mono_on_of_le_circle
    LatticeProb.Gauss.logMaxAbs_continuous.continuousOn.circleIntegrable' fun x hx => ?_
  have hx' : ‖x - z‖ = ε := (mem_sphere_iff_norm.1 hx).trans (abs_of_pos hε)
  have h3 : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by
    have := norm_add_le z (x - z)
    simpa using this
  exact Real.log_le_log (lt_of_lt_of_le one_pos (le_max_right _ _))
    (max_le (by linarith) (by linarith))

theorem circleAverage_logMaxAbs_nonneg (z : ℂ) (ε : ℝ) :
    0 ≤ Real.circleAverage LatticeProb.Gauss.logMaxAbs z ε :=
  Real.circleAverage_nonneg_of_nonneg fun _ _ => Real.log_nonneg (le_max_right _ _)

/-- The second moment of a product of two dyadic densities:
`E[ε^{γ²} e^{γ (h_ε(z) + h_ε(z'))}] ≤ (N + 1)^{4γ²} 2^{γ²} |z - z'|^{-γ²}` for `|z|, |z'| ≤ N`. -/
theorem lintegral_ofReal_dyadicDensity_mul_le (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (γ : ℝ) (k : ℕ) {N : ℝ} {z z' : ℂ} (hz : ‖z‖ ≤ N) (hz' : ‖z'‖ ≤ N) :
    ∫⁻ ω, ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω (dyadicScale k) z)) *
        ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
          Real.exp (γ * hcirc ω (dyadicScale k) z')) ∂P ≤
      ENNReal.ofReal ((N + 1) ^ (4 * γ ^ 2) * 2 ^ (γ ^ 2)) *
        (ENNReal.ofReal ‖z - z'‖) ^ (-γ ^ 2) := by
  have hPm := hh.isProbabilityMeasure
  have hN : 0 ≤ N := (norm_nonneg z).trans hz
  have hε := dyadicScale_pos k
  have hK : 0 < (N + 1) ^ (4 * γ ^ 2) * 2 ^ (γ ^ 2) := by positivity
  by_cases hγ : γ = 0
  · subst hγ
    simp
  by_cases hzz : z = z'
  · subst hzz
    have hγ2 : -γ ^ 2 < 0 := by
      have := pow_pos (abs_pos.mpr hγ) 2
      rw [sq_abs] at this
      linarith
    rw [sub_self, norm_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg hγ2,
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr hK).ne']
    exact le_top
  set ε := dyadicScale k with hεdef
  set A := Real.circleAverage LatticeProb.Gauss.logMaxAbs z ε
  set A' := Real.circleAverage LatticeProb.Gauss.logMaxAbs z' ε
  set Pz := LatticeProb.Gauss.circlePairPotential z ε z' ε
  have hd : 0 < ‖z - z'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzz)
  -- the product as one exponential
  have hprod : ∀ ω, ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z)) *
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z')) =
      ENNReal.ofReal (Real.exp (Real.log ε * γ ^ 2) *
        Real.exp (γ * (hcirc ω ε z + hcirc ω ε z'))) := by
    intro ω
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.rpow_def_of_pos hε, mul_add, Real.exp_add]
    have : Real.exp (Real.log ε * γ ^ 2) =
        Real.exp (Real.log ε * (γ ^ 2 / 2)) * Real.exp (Real.log ε * (γ ^ 2 / 2)) := by
      rw [← Real.exp_add]
      ring_nf
    rw [this]
    ring
  simp_rw [hprod]
  -- the Gaussian exponent
  have hfun : (fun ω => γ * (hcirc ω ε z + hcirc ω ε z')) =
      γ • ((fun ω => hcirc ω ε z) + (fun ω => hcirc ω ε z')) := by
    funext ω
    simp
  have hZ : HasGaussianLaw (fun ω => γ * (hcirc ω ε z + hcirc ω ε z')) P := by
    rw [hfun]
    exact hasGaussianLaw_of_mem_span hh (Submodule.smul_mem _ γ
      (Submodule.add_mem _ (mem_span_circle hε z) (mem_span_circle hε z')))
  have hX0 : P[fun ω => hcirc ω ε z] = 0 := hh.integral_eq_zero (.circle ε z) hε
  have hY0 : P[fun ω => hcirc ω ε z'] = 0 := hh.integral_eq_zero (.circle ε z') hε
  have hXi : Integrable (fun ω => hcirc ω ε z) P := (hh.hasGaussianLaw_circle hε z).integrable
  have hYi : Integrable (fun ω => hcirc ω ε z') P := (hh.hasGaussianLaw_circle hε z').integrable
  have hm : P[fun ω => γ * (hcirc ω ε z + hcirc ω ε z')] = 0 := by
    rw [integral_const_mul, integral_add hXi hYi, hX0, hY0, add_zero, mul_zero]
  obtain ⟨hint, heq⟩ := integral_exp_eq_of_hasGaussianLaw hZ hm
  have hXL : MemLp (fun ω => hcirc ω ε z) 2 P := (hh.hasGaussianLaw_circle hε z).memLp_two
  have hYL : MemLp (fun ω => hcirc ω ε z') 2 P := (hh.hasGaussianLaw_circle hε z').memLp_two
  have hvar : Var[fun ω => γ * (hcirc ω ε z + hcirc ω ε z'); P] =
      γ ^ 2 * (4 * A + 4 * A' - 2 * Real.log ε - 2 * Pz) := by
    have hadd : (fun ω => hcirc ω ε z + hcirc ω ε z') =
        (fun ω => hcirc ω ε z) + (fun ω => hcirc ω ε z') := rfl
    rw [variance_const_mul, hadd, variance_add hXL hYL,
      ← covariance_self (hh.measurable_circle _ _ hε).aemeasurable,
      ← covariance_self (hh.measurable_circle _ _ hε).aemeasurable,
      hh.covariance_circle_circle hε hε, hh.covariance_circle_circle hε hε,
      hh.covariance_circle_circle hε hε,
      LatticeProb.Gauss.wholePlaneGFFCov_circle_circle_eq hε ε z z,
      LatticeProb.Gauss.wholePlaneGFFCov_circle_circle_eq hε ε z z',
      LatticeProb.Gauss.wholePlaneGFFCov_circle_circle_eq hε ε z' z',
      LatticeProb.Gauss.circlePairPotential_self_center hε.le,
      LatticeProb.Gauss.circlePairPotential_self_center hε.le, max_self]
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
    (Filter.Eventually.of_forall fun ω => by positivity), integral_const_mul, heq, hvar,
    ← Real.exp_add, ENNReal.ofReal_rpow_of_pos hd, ← ENNReal.ofReal_mul hK.le]
  apply ENNReal.ofReal_le_ofReal
  -- compare exponents
  have hA := circleAverage_logMaxAbs_le_log_add_one hε (dyadicScale_le_one k) hz
  have hA' := circleAverage_logMaxAbs_le_log_add_one hε (dyadicScale_le_one k) hz'
  have hP := le_circlePairPotential_of_ne hε hzz
  rw [Real.log_div hd.ne' two_ne_zero] at hP
  have hrhs : (N + 1) ^ (4 * γ ^ 2) * 2 ^ (γ ^ 2) * ‖z - z'‖ ^ (-γ ^ 2) =
      Real.exp (Real.log (N + 1) * (4 * γ ^ 2) + Real.log 2 * γ ^ 2 +
        Real.log ‖z - z'‖ * (-γ ^ 2)) := by
    rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos two_pos,
      Real.rpow_def_of_pos hd, ← Real.exp_add, ← Real.exp_add]
  rw [hrhs]
  apply Real.exp_le_exp.mpr
  have hg2 : 0 ≤ γ ^ 2 := sq_nonneg γ
  have h1 : γ ^ 2 * A ≤ γ ^ 2 * Real.log (N + 1) := mul_le_mul_of_nonneg_left hA hg2
  have h2 : γ ^ 2 * A' ≤ γ ^ 2 * Real.log (N + 1) := mul_le_mul_of_nonneg_left hA' hg2
  have h3 : γ ^ 2 * (Real.log ‖z - z'‖ - Real.log 2) ≤ γ ^ 2 * Pz :=
    mul_le_mul_of_nonneg_left hP hg2
  nlinarith

/-! ### Moments of the increments along a path -/

/-- For almost every field the profile densities of the dyadic circle averages are the dyadic
densities `ε^{γ²/2} e^{γ h_ε(z)}`. -/
theorem ae_profileDensity_eq (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (z : ℂ),
      profileDensity γ 0 k (fun p => hcirc ω (dyadicScale p.1) p.2) z =
        ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω (dyadicScale k) z)) := by
  filter_upwards [ae_continuous_dyadic_circle hh] with ω hω k z
  rw [profileDensity_of_continuous (g := fun p : ℕ × ℂ => hcirc ω (dyadicScale p.1) p.2) (hω k)]
  simp only [zero_mul, sub_zero]

theorem measurable_profileDensity_path (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (γ : ℝ) (k : ℕ) (w : ContinuousPath ℂ) :
    Measurable (Function.uncurry fun (ω : Ω) (v : ℝ) =>
      profileDensity γ 0 k (fun p => hcirc ω (dyadicScale p.1) p.2) (w v.toNNReal)) :=
  measurable_profileDensity_comp γ 0 k
    (F := fun q : Ω × ℝ => fun p : ℕ × ℂ => hcirc q.1 (dyadicScale p.1) p.2)
    (G := fun q : Ω × ℝ => w q.2.toNNReal)
    ((measurable_dyadicProfile hh).comp measurable_fst)
    ((w.continuous.comp continuous_real_toNNReal).measurable.comp measurable_snd)

/-- The mean of the increment approximant along any path is at least the length of the
interval. -/
theorem le_lintegral_profileIncrement (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (γ : ℝ) (k : ℕ) (a b : ℝ) (w : ContinuousPath ℂ) :
    ENNReal.ofReal (b - a) ≤ ∫⁻ ω, (∫⁻ v in Ioc a b,
      profileDensity γ 0 k (fun p => hcirc ω (dyadicScale p.1) p.2) (w v.toNNReal)) ∂P := by
  have hPm := hh.isProbabilityMeasure
  rw [lintegral_lintegral_swap (measurable_profileDensity_path hh γ k w).aemeasurable]
  have hpt : ∀ v : ℝ, 1 ≤ ∫⁻ ω,
      profileDensity γ 0 k (fun p => hcirc ω (dyadicScale p.1) p.2) (w v.toNNReal) ∂P := by
    intro v
    have hae : (fun ω => profileDensity γ 0 k (fun p => hcirc ω (dyadicScale p.1) p.2)
        (w v.toNNReal)) =ᵐ[P] fun ω => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
          Real.exp (γ * hcirc ω (dyadicScale k) (w v.toNNReal))) := by
      filter_upwards [ae_profileDensity_eq hh γ] with ω hω
      exact hω k _
    rw [lintegral_congr_ae hae, lintegral_ofReal_dyadicDensity hh]
    exact ENNReal.one_le_ofReal.mpr
      (Real.one_le_exp (mul_nonneg (sq_nonneg γ) (circleAverage_logMaxAbs_nonneg _ _)))
  calc ENNReal.ofReal (b - a) = ∫⁻ _ in Ioc a b, (1 : ℝ≥0∞) := by
        rw [setLIntegral_const, one_mul, Real.volume_Ioc]
    _ ≤ _ := lintegral_mono fun v => hpt v

/-- The second moment of the increment approximant along a path bounded by `N` on `(a, b]` is at
most `(N + 1)^{4γ²} 2^{γ²} ∫∫ |w_s - w_t|^{-γ²}`. -/
theorem lintegral_profileIncrement_sq_le (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (γ : ℝ) (k : ℕ) {a b N : ℝ} (w : ContinuousPath ℂ)
    (hw : ∀ v ∈ Ioc a b, ‖w v.toNNReal‖ ≤ N) :
    ∫⁻ ω, (∫⁻ v in Ioc a b,
        profileDensity γ 0 k (fun p => hcirc ω (dyadicScale p.1) p.2) (w v.toNNReal)) ^ 2 ∂P ≤
      ENNReal.ofReal ((N + 1) ^ (4 * γ ^ 2) * 2 ^ (γ ^ 2)) *
        ∫⁻ s in Ioc a b, ∫⁻ t in Ioc a b,
          (ENNReal.ofReal ‖w s.toNNReal - w t.toNNReal‖) ^ (-γ ^ 2) := by
  have hPm := hh.isProbabilityMeasure
  set D : Ω → ℝ → ℝ≥0∞ := fun ω v =>
    profileDensity γ 0 k (fun p => hcirc ω (dyadicScale p.1) p.2) (w v.toNNReal) with hDdef
  have hD : Measurable (Function.uncurry D) := measurable_profileDensity_path hh γ k w
  have hsq : ∀ ω, (∫⁻ v in Ioc a b, D ω v) ^ 2 =
      ∫⁻ s in Ioc a b, ∫⁻ t in Ioc a b, D ω s * D ω t := by
    intro ω
    rw [sq, lintegral_lintegral_mul hD.of_uncurry_left.aemeasurable
      hD.of_uncurry_left.aemeasurable]
  change ∫⁻ ω, (∫⁻ v in Ioc a b, D ω v) ^ 2 ∂P ≤ _
  simp_rw [hsq]
  have h3 : Measurable (fun q : (Ω × ℝ) × ℝ => D q.1.1 q.1.2 * D q.1.1 q.2) :=
    (hD.comp (measurable_fst.fst.prodMk measurable_fst.snd)).mul
      (hD.comp (measurable_fst.fst.prodMk measurable_snd))
  have hG : Measurable (Function.uncurry fun ω s => ∫⁻ t in Ioc a b, D ω s * D ω t) :=
    h3.lintegral_prod_right'
  have hH : ∀ s, Measurable (Function.uncurry fun ω t => D ω s * D ω t) := fun s =>
    (hD.comp (measurable_fst.prodMk measurable_const)).mul hD
  have hpt : ∀ s ∈ Ioc a b, ∀ t ∈ Ioc a b, ∫⁻ ω, D ω s * D ω t ∂P ≤
      ENNReal.ofReal ((N + 1) ^ (4 * γ ^ 2) * 2 ^ (γ ^ 2)) *
        (ENNReal.ofReal ‖w s.toNNReal - w t.toNNReal‖) ^ (-γ ^ 2) := by
    intro s hs t ht
    have hae : (fun ω => D ω s * D ω t) =ᵐ[P] fun ω =>
        ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
          Real.exp (γ * hcirc ω (dyadicScale k) (w s.toNNReal))) *
        ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
          Real.exp (γ * hcirc ω (dyadicScale k) (w t.toNNReal))) := by
      filter_upwards [ae_profileDensity_eq hh γ] with ω hω
      exact congrArg₂ (· * ·) (hω k _) (hω k _)
    rw [lintegral_congr_ae hae]
    exact lintegral_ofReal_dyadicDensity_mul_le hh γ k (hw s hs) (hw t ht)
  calc ∫⁻ ω, (∫⁻ s in Ioc a b, ∫⁻ t in Ioc a b, D ω s * D ω t) ∂P
      = ∫⁻ s in Ioc a b, (∫⁻ ω, (∫⁻ t in Ioc a b, D ω s * D ω t) ∂P) :=
        lintegral_lintegral_swap hG.aemeasurable
    _ = ∫⁻ s in Ioc a b, ∫⁻ t in Ioc a b, (∫⁻ ω, D ω s * D ω t ∂P) :=
        lintegral_congr fun s => lintegral_lintegral_swap (hH s).aemeasurable
    _ ≤ ∫⁻ s in Ioc a b, ∫⁻ t in Ioc a b,
          ENNReal.ofReal ((N + 1) ^ (4 * γ ^ 2) * 2 ^ (γ ^ 2)) *
            (ENNReal.ofReal ‖w s.toNNReal - w t.toNNReal‖) ^ (-γ ^ 2) :=
        setLIntegral_mono' measurableSet_Ioc fun s hs =>
          setLIntegral_mono' measurableSet_Ioc fun t ht => hpt s hs t ht
    _ = _ := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun s => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end HarmonicBalls
