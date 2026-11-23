import HarmonicBalls.Proofs.Potential.LQGClockIncrementL1Rate
import LatticeProb.Prob.SummableIncrementsL1
import LatticeProb.LQG.GMCDyadicLimit

/-! # Positivity of the clock increments from one start for `0 < γ < 2`

For `0 < γ < 2` and every insertion `α`, for almost every field, the lower limit
`G_{a,b} = liminf_k ∫_a^b ε^{γ²/2} e^{γ h_ε(B_v)} dv` (`ε = 2^{-k}`, `dyadicIncrementLiminf`) is
positive almost surely under planar Brownian motion from the origin, for all rationals `0 < a < b`
(`ae_forall_rat_ae_dyadicIncrementLiminf_pos_of_lt_two`). This is the one-start event of
`LQGClockEveryStart` in the whole range `0 < γ < 2`.

The proof follows `ae_ae_dyadicIncrementLiminf_pos_of_ne_zero_zero` (Cameron-Martin zero-one law
along a fixed path, then a contradiction on the paths along which positivity has probability `0`),
with the `L²` bound, valid only for `γ² < 2`, replaced by an `L¹` argument valid for `γ < 2`.
* On a set `E` of paths bounded by `N` on `[a, b]`, with `R = N + 1`, the recentred approximants
  `Y_k = 1_E e^{-γ h_R(0)} I^k_{a,b}` have summable `L¹` increments under the joint law of the field
  and the path (`lintegral_ofReal_abs_integral_dyadicIncrement_le_exp`, the thick-point truncation
  with the occupation measure of the path as reference measure, and the finiteness of the Brownian
  interval energies `E_x ∫∫ |B_s - B_t|^{-β}`, `β < 2`). Hence they converge almost surely and in
  `L¹` (`LatticeProb.SummableIncrements`).
* Their means are `(b - a) R^{γ²/2} P_x(E)`, since `E[e^{γ (h_ε(z) - h_R(0))}] = (R/ε)^{γ²/2}`.
* If positivity had probability `0` along the paths of `E`, the almost sure limit would vanish, and
  so would the means: a contradiction when `P_x(E) > 0`.
The insertion and the passage to the origin are as in `LQGClockOneStart`.

This is Berestycki 2015, Section 2 (almost sure convergence along `2^{-k}`, thick-point truncation
for `γ ≥ √2`), with the quenched second moment and the occupation estimate of
Dembo-Peres-Rosen-Zeitouni replaced by an annealed `L¹` bound, and the nondegeneracy of Section 3
replaced by the Cameron-Martin zero-one law.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- Along a field with continuous dyadic circle averages, the recentred difference of consecutive
dyadic approximants without insertion is the time integral of the recentred density increments. -/
theorem exp_mul_dyadicIncrementApprox_succ_sub {γ : ℝ} {u : ℝ → ℂ → ℝ}
    (hu : ∀ k, Continuous (u (dyadicScale k))) (R : ℝ) (k : ℕ) {a b : ℝ} (hab : a ≤ b)
    (w : ContinuousPath ℂ) :
    rexp (-(γ * u R 0)) *
        dyadicIncrementApprox γ (LatticeProb.Gauss.fieldCircleAverage 0 u) (k + 1) a b w -
      rexp (-(γ * u R 0)) *
        dyadicIncrementApprox γ (LatticeProb.Gauss.fieldCircleAverage 0 u) k a b w =
    ∫ v in Ioc a b, (dyadicScale (k + 1) ^ (γ ^ 2 / 2) *
        rexp (γ * (u (dyadicScale (k + 1)) (w v.toNNReal) - u R 0)) -
        dyadicScale k ^ (γ ^ 2 / 2) * rexp (γ * (u (dyadicScale k) (w v.toNNReal) - u R 0))) := by
  have hf0 : ∀ (r : ℝ) (z : ℂ), LatticeProb.Gauss.fieldCircleAverage 0 u r z = u r z :=
    fun r z => by simp [LatticeProb.Gauss.fieldCircleAverage]
  have hpt : ∀ c y z : ℝ, rexp (-(γ * y)) * (c * rexp (γ * z)) = c * rexp (γ * (z - y)) := by
    intro c y z
    rw [mul_sub, sub_eq_add_neg, Real.exp_add]
    ring
  have hint : ∀ j, IntegrableOn (fun v : ℝ => dyadicScale j ^ (γ ^ 2 / 2) *
      rexp (γ * (u (dyadicScale j) (w v.toNNReal) - u R 0))) (Ioc a b) := fun j =>
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (((hu j).comp (continuous_comp_toNNReal w)).sub continuous_const)))).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  rw [integral_sub (hint _) (hint _)]
  simp only [dyadicIncrementApprox, hf0, intervalIntegral.integral_of_le hab,
    ← integral_const_mul, hpt]

section OneStartSubcritical

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- `E[e^{-γ h_R(0)} ε^{γ²/2} e^{γ h_ε(z)}] = R^{γ²/2}` for `‖z‖ + ε ≤ R`, `ε = 2^{-k}`. -/
theorem lintegral_ofReal_recentred_dyadicDensity
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ) (k : ℕ) {R : ℝ} {z : ℂ}
    (hz : ‖z‖ + dyadicScale k ≤ R) :
    ∫⁻ ω, ENNReal.ofReal (rexp (-(γ * hcirc ω R 0))) *
      ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * rexp (γ * hcirc ω (dyadicScale k) z)) ∂P =
      ENNReal.ofReal (R ^ (γ ^ 2 / 2)) := by
  have hε := dyadicScale_pos k
  have hR : 0 < R := by linarith [norm_nonneg z]
  have hRε : 1 ≤ R / dyadicScale k := (one_le_div hε).mpr (by linarith [norm_nonneg z])
  have hpt : ∀ ω, ENNReal.ofReal (rexp (-(γ * hcirc ω R 0))) *
      ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * rexp (γ * hcirc ω (dyadicScale k) z)) =
      ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2)) *
        ENNReal.ofReal (rexp (γ * (hcirc ω (dyadicScale k) z - hcirc ω R 0))) := by
    intro ω
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.rpow_nonneg hε.le _)]
    congr 1
    rw [mul_sub, sub_eq_add_neg, Real.exp_add]
    ring
  simp_rw [hpt]
  have hXm : Measurable fun ω => hcirc ω (dyadicScale k) z - hcirc ω R 0 :=
    (hh.measurable_circle _ z hε).sub (hh.measurable_circle R 0 hR)
  have hm : Measurable fun ω => ENNReal.ofReal
      (rexp (γ * (hcirc ω (dyadicScale k) z - hcirc ω R 0))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hXm.const_mul γ))
  rw [lintegral_const_mul _ hm,
    LatticeProb.GaussTail.lintegral_ofReal_exp_mul_of_hasLaw (hh.hasLaw_recentred_circle hε hz) γ,
    Real.coe_toNNReal _ (Real.log_nonneg hRε), ← ENNReal.ofReal_mul (Real.rpow_nonneg hε.le _)]
  congr 1
  rw [Real.rpow_def_of_pos hε, Real.rpow_def_of_pos hR, ← Real.exp_add, Real.log_div hR.ne' hε.ne']
  congr 1
  ring

/-- **Positivity without insertion** (`α = 0`) for `0 < γ < 2`, from every start. -/
theorem ae_ae_dyadicIncrementLiminf_pos_zero_of_lt_two
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (x : ℂ) {a b : ℝ≥0} (hab : a < b) :
    ∀ᵐ ω ∂P, ∀ᵐ w ∂(planarBrownianMotion x),
      0 < dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω)) a b w := by
  have hPm := hh.isProbabilityMeasure
  have hab' : (a : ℝ) < b := hab
  set Q := planarBrownianMotion x with hQdef
  have hXm := measurable_dyadicProfile hh
  have hcont := ae_continuous_dyadic_circle hh
  -- the profile functionals along the joint sample
  have hJm : ∀ k, Measurable (fun q : Ω × ContinuousPath ℂ => ∫⁻ v in Ioc (a : ℝ) b,
      profileDensity γ 0 k (fun p => hcirc q.1 (dyadicScale p.1) p.2) (q.2 v.toNNReal)) :=
    fun k => measurable_profileIncrement_comp γ 0 k a b
      (F := fun q : Ω × ContinuousPath ℂ => fun p : ℕ × ℂ => hcirc q.1 (dyadicScale p.1) p.2)
      (W := fun q => q.2) (hXm.comp measurable_fst) measurable_snd
  have hGm : Measurable (fun q : Ω × ContinuousPath ℂ => profileIncrementLiminf γ 0 a b
      (fun p => hcirc q.1 (dyadicScale p.1) p.2) q.2) :=
    measurable_profileIncrementLiminf_comp γ 0 a b
      (F := fun q : Ω × ContinuousPath ℂ => fun p : ℕ × ℂ => hcirc q.1 (dyadicScale p.1) p.2)
      (W := fun q => q.2) (hXm.comp measurable_fst) measurable_snd
  set M := {q : Ω × ContinuousPath ℂ | 0 < profileIncrementLiminf γ 0 a b
      (fun p => hcirc q.1 (dyadicScale p.1) p.2) q.2} with hMdef
  have hM : MeasurableSet M := measurableSet_lt measurable_const hGm
  have hGeq : ∀ ω, (∀ k, Continuous (hcirc ω (dyadicScale k))) → ∀ w,
      profileIncrementLiminf γ 0 a b (fun p => hcirc ω (dyadicScale p.1) p.2) w =
        dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω)) a b w :=
    fun ω hω w => profileIncrementLiminf_eq_dyadicIncrementLiminf hab'.le hω w
  -- the probabilities along the paths
  set pw : ContinuousPath ℂ → ℝ≥0∞ := fun w => P ((fun ω => (ω, w)) ⁻¹' M) with hpwdef
  have hpw : Measurable pw := measurable_measure_prodMk_right hM
  have h01 : ∀ w, pw w = 0 ∨ pw w = 1 := by
    intro w
    have hae : (fun ω => (ω, w)) ⁻¹' M =ᵐ[P]
        {ω | 0 < dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω)) a b w} := by
      filter_upwards [hcont] with ω hω
      show (0 < profileIncrementLiminf γ 0 a b (fun p => hcirc ω (dyadicScale p.1) p.2) w) =
        (0 < dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω)) a b w)
      rw [hGeq ω hω w]
    rw [hpwdef]
    simp only
    rw [measure_congr hae]
    exact measure_dyadicIncrementLiminf_pos_eq_zero_or_one hh γ 0 hab'.le w
  set W0 := {w | pw w = 0} with hW0def
  have hW0 : MeasurableSet W0 := hpw (measurableSet_singleton 0)
  have hW0null : Q W0 = 0 := by
    by_contra hne
    -- paths bounded by `N` on `[a, b]`
    set BN : ℕ → Set (ContinuousPath ℂ) :=
      fun N => {w | ∀ v ∈ Icc (a : ℝ) b, ‖w v.toNNReal‖ ≤ N} with hBNdef
    have hBNm : ∀ N, MeasurableSet (BN N) := by
      intro N
      have hcl : IsClosed (BN N) := by
        have : BN N = ⋂ v ∈ Icc (a : ℝ) b, {w : ContinuousPath ℂ | ‖w v.toNNReal‖ ≤ N} := by
          ext w
          simp [hBNdef]
        rw [this]
        exact isClosed_biInter fun v _ =>
          isClosed_le (continuous_norm.comp (continuous_eval_const _)) continuous_const
      exact hcl.measurableSet
    have hBNmono : Monotone BN := fun N N' h w hw v hv =>
      (hw v hv).trans (by exact_mod_cast h)
    have hBNcov : ∀ w : ContinuousPath ℂ, ∃ N : ℕ, w ∈ BN N := by
      intro w
      obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (a : ℝ)) (b := b)).image
        (w.continuous.comp continuous_real_toNNReal)).isBounded.exists_norm_le
      obtain ⟨N, hN⟩ := exists_nat_ge C
      exact ⟨N, fun v hv => (hC _ ⟨v, hv, rfl⟩).trans hN⟩
    have hlimN : Tendsto (fun N => Q (W0 ∩ BN N)) atTop (𝓝 (Q W0)) := by
      have h := tendsto_measure_iUnion_atTop (μ := Q)
        (fun N N' (h : N ≤ N') => Set.inter_subset_inter_right W0 (hBNmono h))
      have hU : ⋃ N, W0 ∩ BN N = W0 := by
        ext w
        simp only [Set.mem_iUnion, Set.mem_inter_iff]
        exact ⟨fun ⟨_, h1, _⟩ => h1, fun h1 => (hBNcov w).imp fun N hN => ⟨h1, hN⟩⟩
      rwa [hU] at h
    obtain ⟨N, hN⟩ : ∃ N : ℕ, Q (W0 ∩ BN N) ≠ 0 := by
      obtain ⟨N, hN⟩ := (hlimN.eventually (lt_mem_nhds (pos_iff_ne_zero.mpr hne))).exists
      exact ⟨N, hN.ne'⟩
    set E := W0 ∩ BN N with hEdef
    have hE : MeasurableSet E := hW0.inter (hBNm N)
    -- (i) the restricted approximants tend to `0`
    have hzeroE : ∀ᵐ q ∂(P.prod Q), q.2 ∈ E → profileIncrementLiminf γ 0 a b
        (fun p => hcirc q.1 (dyadicScale p.1) p.2) q.2 = 0 := by
      have hset : (P.prod Q) ((Prod.snd ⁻¹' E) ∩ M) = 0 := by
        rw [Measure.prod_apply_symm ((measurable_snd hE).inter hM)]
        refine (lintegral_eq_zero_iff (measurable_measure_prodMk_right
          ((measurable_snd hE).inter hM))).mpr (Filter.Eventually.of_forall fun w => ?_)
        by_cases hw : w ∈ E
        · have h1 : (fun ω => (ω, w)) ⁻¹' ((Prod.snd ⁻¹' E) ∩ M) =
              (fun ω => (ω, w)) ⁻¹' M := by
            ext ω
            simp [hw]
          simp only [Pi.zero_apply]
          rw [h1]
          exact hw.1
        · have h1 : (fun ω => (ω, w)) ⁻¹' ((Prod.snd ⁻¹' E) ∩ M) = ∅ := by
            ext ω
            simp [hw]
          simp only [Pi.zero_apply]
          rw [h1, measure_empty]
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hset] with q hq hqE
      by_contra hG
      exact hq ⟨hqE, pos_iff_ne_zero.mpr hG⟩
    have hcontP : ∀ᵐ q ∂(P.prod Q), ∀ k, Continuous (hcirc q.1 (dyadicScale k)) :=
      Measure.quasiMeasurePreserving_fst.ae hcont
    -- (ii) the recentred approximants restricted to `E`
    set R : ℝ := (N : ℝ) + 1 with hRdef
    have hR : 0 < R := by rw [hRdef]; positivity
    set c : Ω → ℝ := fun ω => rexp (-(γ * hcirc ω R 0)) with hcdef
    have hcm : Measurable c :=
      Real.measurable_exp.comp ((hh.measurable_circle R 0 hR).const_mul γ).neg
    have hc0 : ∀ ω, 0 ≤ c ω := fun ω => (Real.exp_pos _).le
    set Y : ℕ → Ω × ContinuousPath ℂ → ℝ := fun k => (Prod.snd ⁻¹' E).indicator
      (fun q => c q.1 * (∫⁻ v in Ioc (a : ℝ) b,
        profileDensity γ 0 k (fun p => hcirc q.1 (dyadicScale p.1) p.2) (q.2 v.toNNReal)).toReal)
      with hYdef
    have hYm : ∀ k, Measurable (Y k) := fun k =>
      ((hcm.comp measurable_fst).mul (hJm k).ennreal_toReal).indicator (measurable_snd hE)
    have hYnn : ∀ k q, 0 ≤ Y k q := fun k q =>
      Set.indicator_nonneg (fun q _ => mul_nonneg (hc0 _) ENNReal.toReal_nonneg) q
    have hYE : ∀ k ω w, w ∈ E → Y k (ω, w) = c ω * (∫⁻ v in Ioc (a : ℝ) b,
        profileDensity γ 0 k (fun p => hcirc ω (dyadicScale p.1) p.2) (w v.toNNReal)).toReal :=
      fun k ω w hw => Set.indicator_of_mem (show (ω, w) ∈ Prod.snd ⁻¹' E from hw) _
    have hYnE : ∀ k ω w, w ∉ E → Y k (ω, w) = 0 :=
      fun k ω w hw => Set.indicator_of_notMem (show (ω, w) ∉ Prod.snd ⁻¹' E from hw) _
    have hJeq : ∀ ω, (∀ k, Continuous (hcirc ω (dyadicScale k))) → ∀ k w,
        (∫⁻ v in Ioc (a : ℝ) b, profileDensity γ 0 k (fun p => hcirc ω (dyadicScale p.1) p.2)
          (w v.toNNReal)) = ENNReal.ofReal (dyadicIncrementApprox γ
            (LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω)) k a b w) :=
      fun ω hω k w => lintegral_profileDensity_eq_ofReal hab'.le hω k w
    have hInn : ∀ ω k w, 0 ≤ dyadicIncrementApprox γ
        (LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω)) k a b w := fun ω k w =>
      intervalIntegral.integral_nonneg hab'.le fun v _ => dyadicIncrementIntegrand_nonneg _ _ _ _ _
    have hJfin : ∀ ω, (∀ k, Continuous (hcirc ω (dyadicScale k))) → ∀ (k : ℕ) (w : ContinuousPath ℂ),
        (∫⁻ v in Ioc (a : ℝ) b, profileDensity γ 0 k (fun p => hcirc ω (dyadicScale p.1) p.2)
          (w v.toNNReal)) ≠ ⊤ := fun ω hω k w => by
      rw [hJeq ω hω k w]
      exact ENNReal.ofReal_ne_top
    have hYeq : ∀ ω, (∀ k, Continuous (hcirc ω (dyadicScale k))) → ∀ k w, w ∈ E →
        Y k (ω, w) = c ω * dyadicIncrementApprox γ
          (LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω)) k a b w := by
      intro ω hω k w hw
      rw [hYE k ω w hw, hJeq ω hω k w, ENNReal.toReal_ofReal (hInn ω k w)]
    -- (iii) the means are `(b - a) R^{γ²/2} Q(E)`
    have hmeanw : ∀ k, ∀ w ∈ E, ∫⁻ ω, ENNReal.ofReal (Y k (ω, w)) ∂P =
        ENNReal.ofReal (R ^ (γ ^ 2 / 2)) * ENNReal.ofReal ((b : ℝ) - a) := by
      intro k w hw
      have hwN : ∀ v ∈ Ioc (a : ℝ) b, ‖w v.toNNReal‖ ≤ N := fun v hv =>
        hw.2 v (Ioc_subset_Icc_self hv)
      set D : Ω → ℝ → ℝ≥0∞ := fun ω v => ENNReal.ofReal (c ω) *
        profileDensity γ 0 k (fun p => hcirc ω (dyadicScale p.1) p.2) (w v.toNNReal) with hDdef
      have hDm : Measurable (Function.uncurry D) :=
        (hcm.ennreal_ofReal.comp measurable_fst).mul (measurable_profileDensity_path hh γ k w)
      have h1 : (fun ω => ENNReal.ofReal (Y k (ω, w))) =ᵐ[P]
          fun ω => ∫⁻ v in Ioc (a : ℝ) b, D ω v := by
        filter_upwards [hcont] with ω hω
        rw [hYE k ω w hw, ENNReal.ofReal_mul (hc0 ω), ENNReal.ofReal_toReal (hJfin ω hω k w),
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [lintegral_congr_ae h1, lintegral_lintegral_swap hDm.aemeasurable]
      have h2 : ∀ v ∈ Ioc (a : ℝ) b, ∫⁻ ω, D ω v ∂P = ENNReal.ofReal (R ^ (γ ^ 2 / 2)) := by
        intro v hv
        have hae : (fun ω => D ω v) =ᵐ[P] fun ω => ENNReal.ofReal (rexp (-(γ * hcirc ω R 0))) *
            ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
              rexp (γ * hcirc ω (dyadicScale k) (w v.toNNReal))) := by
          filter_upwards [ae_profileDensity_eq hh γ] with ω hω
          simp only [hDdef, hcdef, hω k]
        rw [lintegral_congr_ae hae]
        exact lintegral_ofReal_recentred_dyadicDensity hh γ k
          (by linarith [hwN v hv, dyadicScale_le_one k, hRdef])
      rw [setLIntegral_congr_fun measurableSet_Ioc h2, setLIntegral_const, Real.volume_Ioc]
    have hmean : ∀ k, ∫⁻ q, ENNReal.ofReal (Y k q) ∂(P.prod Q) =
        ENNReal.ofReal (R ^ (γ ^ 2 / 2)) * ENNReal.ofReal ((b : ℝ) - a) * Q E := by
      intro k
      rw [lintegral_prod_symm _ (hYm k).ennreal_ofReal.aemeasurable]
      calc ∫⁻ w, ∫⁻ ω, ENNReal.ofReal (Y k (ω, w)) ∂P ∂Q
          = ∫⁻ w, E.indicator (fun _ => ENNReal.ofReal (R ^ (γ ^ 2 / 2)) *
              ENNReal.ofReal ((b : ℝ) - a)) w ∂Q := by
            refine lintegral_congr fun w => ?_
            by_cases hw : w ∈ E
            · rw [Set.indicator_of_mem hw]
              exact hmeanw k w hw
            · rw [Set.indicator_of_notMem hw]
              have h0 : ∀ ω, Y k (ω, w) = 0 := fun ω => hYnE k ω w hw
              simp [h0]
        _ = _ := lintegral_indicator_const hE _
    have hK : ENNReal.ofReal (R ^ (γ ^ 2 / 2)) * ENNReal.ofReal ((b : ℝ) - a) * Q E ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        (measure_ne_top Q E)
    have hK0 : ENNReal.ofReal (R ^ (γ ^ 2 / 2)) * ENNReal.ofReal ((b : ℝ) - a) * Q E ≠ 0 :=
      mul_ne_zero (mul_ne_zero (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hR _)).ne'
        (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab')).ne') hN
    have hYi : ∀ k, Integrable (Y k) (P.prod Q) := fun k =>
      ⟨(hYm k).aestronglyMeasurable, by
        rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (hYnn k)), hmean k]
        exact hK.lt_top⟩
    have hYint : ∀ k, ∫ q, Y k q ∂(P.prod Q) =
        (ENNReal.ofReal (R ^ (γ ^ 2 / 2)) * ENNReal.ofReal ((b : ℝ) - a) * Q E).toReal := by
      intro k
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hYnn k)) (hYm k).aestronglyMeasurable,
        hmean k]
    -- (iv) summable `L¹` increments
    obtain ⟨α, hγα, hα, hbb, hbb4, hαγ⟩ : ∃ α : ℝ, γ ≤ α ∧ α ≤ 2 * γ ∧
        0 < 2 - γ ^ 2 + (2 * γ - α) ^ 2 / 2 ∧ 2 - γ ^ 2 + (2 * γ - α) ^ 2 / 2 < 4 ∧
        0 < (α - γ) ^ 2 / 2 := by
      rcases lt_or_ge γ 1 with h1 | h1
      · exact ⟨2 * γ, by linarith, le_rfl, by nlinarith, by nlinarith, by nlinarith⟩
      · refine ⟨2, by linarith, by linarith, ?_, ?_, ?_⟩
        · nlinarith [sq_nonneg (γ - 1)]
        · nlinarith [sq_nonneg (γ - 1)]
        · have : 0 < 2 - γ := by linarith
          exact div_pos (pow_pos this 2) two_pos
    set β : ℝ := 2 - (2 - γ ^ 2 + (2 * γ - α) ^ 2 / 2) / 2 with hβdef
    have hβ : 0 < β := by rw [hβdef]; linarith
    have hβ2 : β < 2 := by rw [hβdef]; linarith
    set e : ℝ := (β - γ ^ 2 + (2 * γ - α) ^ 2 / 2) / 2 with hedef
    have he : 0 < e := by rw [hedef, hβdef]; linarith
    set Cb := ∫⁻ w, (∫⁻ s in Ioc (a : ℝ) b, ∫⁻ t in Ioc (a : ℝ) b,
      (ENNReal.ofReal ‖w s.toNNReal - w t.toNNReal‖) ^ (-β)) ∂Q with hCbdef
    have hCbfin : Cb ≠ ⊤ := (lintegral_planarBrownianMotion_Ioc_pair_lt_top x hβ hβ2 a.2 hab').ne
    set K₁ : ℝ := (rexp (γ ^ 2 * Real.log 2) - 1) *
      rexp (Real.log ((N : ℝ) + 1) * (2 * γ ^ 2 - (2 * γ - α) ^ 2 / 2)) * 2 ^ β / 2 with hK₁def
    have hK₁ : 0 ≤ K₁ := by
      have : 0 ≤ rexp (γ ^ 2 * Real.log 2) - 1 :=
        sub_nonneg.mpr (Real.one_le_exp (by positivity))
      exact div_nonneg (mul_nonneg (mul_nonneg this (Real.exp_pos _).le)
        (Real.rpow_nonneg two_pos.le _)) two_pos.le
    set K₃ : ℝ := 2 * ((b : ℝ) - a) *
      rexp (Real.log ((N : ℝ) + 1) * (γ ^ 2 / 2 - (α - γ) ^ 2 / 2)) with hK₃def
    have hK₃ : 0 ≤ K₃ := by
      have : 0 ≤ (b : ℝ) - a := (sub_pos.mpr hab').le
      exact mul_nonneg (mul_nonneg two_pos.le this) (Real.exp_pos _).le
    have hbk0 : ∀ k, 0 ≤ K₁ * rexp (Real.log (dyadicScale k) * e) * Cb.toReal ∧
        0 ≤ rexp (Real.log (dyadicScale k) * e) / 2 +
          K₃ * rexp (Real.log (dyadicScale k) * ((α - γ) ^ 2 / 2)) := fun k =>
      ⟨mul_nonneg (mul_nonneg hK₁ (Real.exp_pos _).le) ENNReal.toReal_nonneg,
        add_nonneg (div_nonneg (Real.exp_pos _).le two_pos.le)
          (mul_nonneg hK₃ (Real.exp_pos _).le)⟩
    set bk : ℕ → ℝ := fun k => K₁ * rexp (Real.log (dyadicScale k) * e) * Cb.toReal +
      (rexp (Real.log (dyadicScale k) * e) / 2 +
        K₃ * rexp (Real.log (dyadicScale k) * ((α - γ) ^ 2 / 2))) with hbkdef
    have hΔw : ∀ k, ∀ w ∈ E, ∫⁻ ω, ENNReal.ofReal |Y (k + 1) (ω, w) - Y k (ω, w)| ∂P ≤
        ENNReal.ofReal (K₁ * rexp (Real.log (dyadicScale k) * e)) *
          (∫⁻ s in Ioc (a : ℝ) b, ∫⁻ t in Ioc (a : ℝ) b,
            (ENNReal.ofReal ‖w s.toNNReal - w t.toNNReal‖) ^ (-β)) +
        ENNReal.ofReal (rexp (Real.log (dyadicScale k) * e) / 2 +
          K₃ * rexp (Real.log (dyadicScale k) * ((α - γ) ^ 2 / 2))) := by
      intro k w hw
      have hwN : ∀ v ∈ Ioc (a : ℝ) b, ‖w v.toNNReal‖ ≤ N := fun v hv =>
        hw.2 v (Ioc_subset_Icc_self hv)
      refine le_trans (le_of_eq (lintegral_congr_ae ?_))
        (lintegral_ofReal_abs_integral_dyadicIncrement_le_exp hh k (Nat.cast_nonneg N)
          hab'.le hwN hγα hα hβ)
      filter_upwards [hcont] with ω hω
      have h := exp_mul_dyadicIncrementApprox_succ_sub (γ := γ) hω R k hab'.le w
      rw [hYeq ω hω (k + 1) w hw, hYeq ω hω k w hw]
      exact congrArg (fun y => ENNReal.ofReal |y|) h
    have hΔ : ∀ k, ∫⁻ q, ENNReal.ofReal |Y (k + 1) q - Y k q| ∂(P.prod Q) ≤
        ENNReal.ofReal (bk k) := by
      intro k
      have hm : Measurable fun q => ENNReal.ofReal |Y (k + 1) q - Y k q| :=
        (continuous_abs.measurable.comp ((hYm (k + 1)).sub (hYm k))).ennreal_ofReal
      rw [lintegral_prod_symm _ hm.aemeasurable]
      calc ∫⁻ w, ∫⁻ ω, ENNReal.ofReal |Y (k + 1) (ω, w) - Y k (ω, w)| ∂P ∂Q
          ≤ ∫⁻ w, (ENNReal.ofReal (K₁ * rexp (Real.log (dyadicScale k) * e)) *
              (∫⁻ s in Ioc (a : ℝ) b, ∫⁻ t in Ioc (a : ℝ) b,
                (ENNReal.ofReal ‖w s.toNNReal - w t.toNNReal‖) ^ (-β)) +
            ENNReal.ofReal (rexp (Real.log (dyadicScale k) * e) / 2 +
              K₃ * rexp (Real.log (dyadicScale k) * ((α - γ) ^ 2 / 2)))) ∂Q := by
            refine lintegral_mono fun w => ?_
            by_cases hw : w ∈ E
            · exact hΔw k w hw
            · have h0 : ∀ j ω, Y j (ω, w) = 0 := fun j ω => hYnE j ω w hw
              simp [h0]
        _ = ENNReal.ofReal (K₁ * rexp (Real.log (dyadicScale k) * e)) * Cb +
            ENNReal.ofReal (rexp (Real.log (dyadicScale k) * e) / 2 +
              K₃ * rexp (Real.log (dyadicScale k) * ((α - γ) ^ 2 / 2))) := by
            rw [lintegral_add_right _ measurable_const,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const, measure_univ,
              mul_one]
        _ = ENNReal.ofReal (K₁ * rexp (Real.log (dyadicScale k) * e) * Cb.toReal +
            (rexp (Real.log (dyadicScale k) * e) / 2 +
              K₃ * rexp (Real.log (dyadicScale k) * ((α - γ) ^ 2 / 2)))) := by
            rw [ENNReal.ofReal_add (hbk0 k).1 (hbk0 k).2,
              ENNReal.ofReal_mul (mul_nonneg hK₁ (Real.exp_pos _).le),
              ENNReal.ofReal_toReal hCbfin]
    have hint : ∀ k, Integrable (fun q => Y (k + 1) q - Y k q) (P.prod Q) := fun k =>
      (hYi (k + 1)).sub (hYi k)
    have hbd : ∀ k, ∫ q, |Y (k + 1) q - Y k q| ∂(P.prod Q) ≤ bk k := by
      intro k
      have hbk : 0 ≤ bk k := add_nonneg (hbk0 k).1 (hbk0 k).2
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun q => abs_nonneg _)
        (hint k).abs.aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal hbk (hΔ k)
    have hsum : Summable bk := by
      have hs1 : Summable fun k : ℕ => rexp (Real.log (dyadicScale k) * e) :=
        LatticeProb.Gauss.summable_exp_log_dyadicScale_mul he
      have hs2 : Summable fun k : ℕ => rexp (Real.log (dyadicScale k) * ((α - γ) ^ 2 / 2)) :=
        LatticeProb.Gauss.summable_exp_log_dyadicScale_mul hαγ
      exact ((hs1.mul_left K₁).mul_right Cb.toReal).add ((hs1.div_const 2).add (hs2.mul_left K₃))
    -- (v) the almost sure limit vanishes
    have hlim := LatticeProb.SummableIncrements.ae_exists_tendsto_of_integral_abs_sub_le hint hbd
      hsum
    have hlim0 : ∀ᵐ q ∂(P.prod Q), Tendsto (fun k => Y k q) atTop (𝓝 0) := by
      filter_upwards [hlim, hzeroE, hcontP] with q h1 h2 h3
      rcases q with ⟨ω, w⟩
      dsimp only at h1 h2 h3 ⊢
      obtain ⟨l, hl⟩ := h1
      by_cases hqE : w ∈ E
      · have hG0 := h2 hqE
        rw [profileIncrementLiminf_eq_liminf] at hG0
        have hofY : ∀ k, ENNReal.ofReal (Y k (ω, w)) = ENNReal.ofReal (c ω) *
            ∫⁻ v in Ioc (a : ℝ) b,
              profileDensity γ 0 k (fun p => hcirc ω (dyadicScale p.1) p.2) (w v.toNNReal) := by
          intro k
          rw [hYE k ω w hqE, ENNReal.ofReal_mul (hc0 _), ENNReal.ofReal_toReal (hJfin ω h3 k w)]
        have hliminf : liminf (fun k => ENNReal.ofReal (Y k (ω, w))) atTop = 0 := by
          simp_rw [hofY]
          rw [ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top, hG0, mul_zero]
        have hofl : liminf (fun k => ENNReal.ofReal (Y k (ω, w))) atTop = ENNReal.ofReal l :=
          ((ENNReal.continuous_ofReal.tendsto l).comp hl).liminf_eq
        rw [hliminf] at hofl
        have hl0 : l ≤ 0 := ENNReal.ofReal_eq_zero.mp hofl.symm
        have hl0' : 0 ≤ l := ge_of_tendsto' hl fun k => hYnn k (ω, w)
        rwa [le_antisymm hl0 hl0'] at hl
      · have hY0 : ∀ k, Y k (ω, w) = 0 := fun k => hYnE k ω w hqE
        simp_rw [hY0]
        exact tendsto_const_nhds
    -- (vi) the contradiction
    have hL1 := LatticeProb.SummableIncrements.tendsto_integral_abs_sub_of_integral_abs_sub_le
      (fun k => (hYm k).aestronglyMeasurable) hint hbd hsum (L := fun _ => 0) hlim0
    have hconst : ∀ k, ∫ q, |Y k q| ∂(P.prod Q) =
        (ENNReal.ofReal (R ^ (γ ^ 2 / 2)) * ENNReal.ofReal ((b : ℝ) - a) * Q E).toReal := by
      intro k
      rw [← hYint k]
      exact integral_congr_ae (ae_of_all _ fun q => abs_of_nonneg (hYnn k q))
    have hL1' : Tendsto (fun k => ∫ q, |Y k q| ∂(P.prod Q)) atTop (𝓝 0) := by
      simpa only [sub_zero] using hL1
    simp_rw [hconst] at hL1'
    exact absurd (tendsto_nhds_unique tendsto_const_nhds hL1') (ENNReal.toReal_pos hK0 hK).ne'
  -- conclusion
  have hfull : ∀ᵐ w ∂Q, pw w = 1 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hW0null] with w hw
    rcases h01 w with h | h
    · exact absurd h hw
    · exact h
  have hprod : ∀ᵐ q ∂(P.prod Q), q ∈ M := by
    rw [ae_iff]
    change (P.prod Q) Mᶜ = 0
    rw [Measure.prod_apply_symm hM.compl]
    refine (lintegral_eq_zero_iff (measurable_measure_prodMk_right hM.compl)).mpr ?_
    filter_upwards [hfull] with w hw
    have hc : (fun ω => (ω, w)) ⁻¹' Mᶜ = ((fun ω => (ω, w)) ⁻¹' M)ᶜ := rfl
    simp only [Pi.zero_apply]
    rw [hc, prob_compl_eq_one_sub (measurable_prodMk_right hM)]
    rw [hpwdef] at hw
    simp only at hw
    rw [hw, tsub_self]
  filter_upwards [Measure.ae_ae_of_ae_prod hprod, hcont] with ω hω hωc
  filter_upwards [hω] with w hw
  rw [← hGeq ω hωc w]
  exact hw

/-- **Positivity from a start `x ≠ 0`, with every insertion `α`**, for `0 < γ < 2`. -/
theorem ae_ae_dyadicIncrementLiminf_pos_of_ne_zero_of_lt_two
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {x : ℂ} (hx : x ≠ 0) (α : ℝ) {a b : ℝ≥0} (hab : a < b) :
    ∀ᵐ ω ∂P, ∀ᵐ w ∂(planarBrownianMotion x),
      0 < dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) a b w := by
  have hab' : (a : ℝ) ≤ b := hab.le
  filter_upwards [ae_ae_dyadicIncrementLiminf_pos_zero_of_lt_two hh hγ hγ2 x hab,
    ae_continuous_dyadic_circle hh] with ω h0 hc
  filter_upwards [h0, Section6.planarBrownianMotion_point_avoidance x 0 hx] with w hw hwav
  obtain ⟨L, hL⟩ := exists_abs_log_max_le hab' (w := w) fun v _ => hwav _
  exact lt_of_lt_of_le (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' hw.ne')
    (dyadicIncrementLiminf_insertion_ge hab' hc hL)

/-- **Positivity from the origin** for `0 < γ < 2`, for real times `0 < a < b`: the path after
time `a` started at `0` has a law absolutely continuous with respect to the path after time `a`
started at `1`. -/
theorem ae_ae_dyadicIncrementLiminf_pos_origin_of_lt_two
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (α : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ᵐ ω ∂P, ∀ᵐ w ∂(planarBrownianMotion 0),
      0 < dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) a b w := by
  have hb : 0 < b := ha.trans hab
  have h1 := ae_ae_dyadicIncrementLiminf_pos_of_ne_zero_of_lt_two hh hγ hγ2
    (one_ne_zero : (1 : ℂ) ≠ 0) α
    (a := a.toNNReal) (b := b.toNNReal) ((Real.toNNReal_lt_toNNReal_iff hb).mpr hab)
  filter_upwards [h1, ae_continuous_dyadic_circle hh] with ω hω hc
  have hab' : 0 ≤ b - a := (sub_pos.mpr hab).le
  set E := {w' : ContinuousPath ℂ | 0 < profileIncrementLiminf γ α 0 (b - a)
    (fun p => hcirc ω (dyadicScale p.1) p.2) w'} with hEdef
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    (measurable_profileIncrementLiminf_comp γ α 0 (b - a)
      (F := fun _ : ContinuousPath ℂ => fun p : ℕ × ℂ => hcirc ω (dyadicScale p.1) p.2)
      (W := fun w' => w') measurable_const measurable_id)
  have hEq : ∀ w', w' ∈ E ↔
      0 < dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) 0 (b - a) w' := by
    intro w'
    show (0 < profileIncrementLiminf γ α 0 (b - a) (fun p => hcirc ω (dyadicScale p.1) p.2) w') ↔ _
    rw [profileIncrementLiminf_eq_dyadicIncrementLiminf hab' hc w']
  have hs : ∀ᵐ w ∂(planarBrownianMotion 1), ContinuousPath.shift a.toNNReal w ∈ E := by
    filter_upwards [hω] with w hw
    rw [Real.coe_toNNReal _ ha.le, Real.coe_toNNReal _ hb.le] at hw
    rw [hEq, ← dyadicIncrementLiminf_shift γ _ ha.le hab.le w]
    exact hw
  filter_upwards [ae_shift_mem_of_ae_shift_mem (Real.toNNReal_pos.mpr ha) hE hs 0] with w hw
  rw [dyadicIncrementLiminf_shift γ _ ha.le hab.le w, ← hEq]
  exact hw

/-- **The one-start event for `0 < γ < 2`.** For every insertion `α`, for almost every field,
the lower limit of the dyadic approximants of every clock increment between rational times
`0 < a < b` is positive almost surely under planar Brownian motion from the origin (the analogue
of Berestycki 2015, Theorem 1.2, nondegeneracy of the clock, for the circle-normalized whole-plane
field). -/
theorem ae_forall_rat_ae_dyadicIncrementLiminf_pos_of_lt_two
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (α : ℝ) :
    ∀ᵐ ω ∂P, ∀ a b : ℚ, 0 < a → a < b → ∀ᵐ w ∂(planarBrownianMotion 0),
      0 < dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) a b w := by
  have h : ∀ p : ℚ × ℚ, ∀ᵐ ω ∂P, 0 < p.1 → p.1 < p.2 → ∀ᵐ w ∂(planarBrownianMotion 0),
      0 < dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) p.1 p.2 w := by
    intro p
    by_cases hp : 0 < p.1 ∧ p.1 < p.2
    · filter_upwards [ae_ae_dyadicIncrementLiminf_pos_origin_of_lt_two hh hγ hγ2 α (a := (p.1 : ℝ))
        (b := (p.2 : ℝ)) (by exact_mod_cast hp.1) (by exact_mod_cast hp.2)] with ω hω _ _
      exact hω
    · exact Filter.Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hp
  filter_upwards [ae_all_iff.mpr h] with ω hω a b ha hab
  exact hω (a, b) ha hab

/-- Strict increase between rational times for `0 < γ < 2`: for every family of LQG clocks of the
inserted field from every start, for almost every field, the clock from each start increases
strictly between any two rational times almost surely. -/
theorem ae_forall_rat_lt_of_isLQGClock_of_lt_two
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) x (F ω x)) :
    ∀ᵐ ω ∂P, ∀ x : ℂ, ∀ s t : ℚ, 0 ≤ s → s < t → ∀ᵐ w ∂(planarBrownianMotion x),
      F ω x w (s : ℝ).toNNReal < F ω x w (t : ℝ).toNNReal :=
  ae_forall_rat_lt_of_dyadicIncrementLiminf_pos hh F hF
    (ae_forall_rat_ae_dyadicIncrementLiminf_pos_of_lt_two hh hγ hγ2 α)

/-- The lower limit `G_{0,1}` over `[0, 1]` is almost surely positive from the origin for almost
every field, for `0 < γ < 2` and every insertion `α`: it dominates `G_{1/2,1}`. -/
theorem ae_ae_dyadicIncrementLiminf_zero_one_pos_of_lt_two
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (α : ℝ) :
    ∀ᵐ ω ∂P, ∀ᵐ w ∂(planarBrownianMotion 0),
      0 < dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) 0 1 w := by
  filter_upwards [ae_ae_dyadicIncrementLiminf_pos_origin_of_lt_two hh hγ hγ2 α (a := 1 / 2)
    (b := 1) (by norm_num) (by norm_num), ae_continuous_fieldCircleAverage hh α] with ω hω hc
  filter_upwards [hω] with w hw
  refine lt_of_lt_of_le hw (liminf_le_liminf (Eventually.of_forall fun k =>
    ENNReal.ofReal_le_ofReal (dyadicIncrementApprox_mono (hc _ (dyadicScale_pos k)) w
      (by norm_num) (by norm_num) le_rfl)))

end OneStartSubcritical

end HarmonicBalls
