import HarmonicBalls.Proofs.Potential.LQGClockIncrementMoments
import HarmonicBalls.Proofs.Potential.LQGClockInsertedExistence
import HarmonicBalls.Proofs.Potential.BrownianTimeRieszEnergy
import HarmonicBalls.Proofs.Sec6.LogAnnulusHitting

/-! # Positivity of the clock increments from one start

For `0 < γ`, `γ² < 2` and every insertion `α`, for almost every field, the lower limit
`G_{a,b} = liminf_k ∫_a^b ε^{γ²/2} e^{γ h_ε(B_v)} dv` (`ε = 2^{-k}`, `dyadicIncrementLiminf`) is
positive almost surely under planar Brownian motion from the origin, for all rationals `0 < a < b`
(`ae_forall_rat_ae_dyadicIncrementLiminf_pos`). This is the one-start event of the time-change and
exit-time theorems of `LQGClockEveryStart`, which therefore hold without it.

Proof, first from a start `x ≠ 0` and without insertion.
* Along every fixed path the event `{G_{a,b} > 0}` has probability `0` or `1` under the field
  (`measure_dyadicIncrementLiminf_pos_eq_zero_or_one`, the Cameron-Martin zero-one law).
* Suppose the paths `w` along which it has probability `0` had positive probability. Restricted to
  these paths and to paths bounded by `N` on `[a, b]`, the approximants `I^k_{a,b}` converge almost
  surely under the joint law (Berestycki 2015, Section 2, on main as the locally uniform convergence
  of the half-disc and exterior clocks from `x ≠ 0`) to `0`, they are bounded in `L²` (the second
  moment is at most `(N + 1)^{4γ²} 2^{γ²} E_x ∫∫ |B_s - B_t|^{-γ²} < ∞` for `γ² < 2`), and their
  means are at least `(b - a)` times the probability of the restriction. Convergence to `0` with
  bounded second moments forces the means to `0`: a contradiction. So `G_{a,b} > 0` almost surely
  for almost every path, and by Fubini for almost every field almost surely.
* With an insertion `α`, the approximants change by the factor `e^{-γ α log max(ε, |B_v|)}`, which is
  bounded below on `[a, b]` since Brownian motion from `x ≠ 0` never visits `0`.
* From the origin: the path after time `a > 0` started at `0` has a law absolutely continuous with
  respect to the law of the path after time `a` started at `1` (`ae_shift_mem_of_ae_shift_mem`).

This replaces the nondegeneracy argument of Berestycki 2015, Section 3 (an `L^q` bound by Kahane's
convexity inequality and an exactly scale-invariant field, then a second-moment argument with the
domain Markov property), by the `L²` bound, valid for `γ² < 2`, and the Cameron-Martin zero-one law.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- Almost sure convergence to `0` with uniformly bounded second moments, on a finite measure,
implies convergence of the means to `0`. -/
theorem tendsto_lintegral_zero_of_ae_tendsto_zero_of_lintegral_sq_le {X : Type*}
    [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {Y : ℕ → X → ℝ≥0∞}
    (hY : ∀ k, Measurable (Y k)) (hlim : ∀ᵐ x ∂μ, Tendsto (fun k => Y k x) atTop (𝓝 0))
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hsq : ∀ k, ∫⁻ x, Y k x ^ 2 ∂μ ≤ C) :
    Tendsto (fun k => ∫⁻ x, Y k x ∂μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε.ne').ne'
  -- a truncation level `L` with `C / L ≤ ε / 2`
  have hCn : Tendsto (fun n : ℕ => C * (n : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hC)
    simpa using h
  obtain ⟨n, hn, hn1⟩ := ((ENNReal.tendsto_nhds_zero.mp hCn (ε / 2)
    (pos_iff_ne_zero.mpr hε2)).and (eventually_ge_atTop 1)).exists
  set L : ℝ≥0∞ := (n : ℝ≥0∞) with hLdef
  have hL0 : L ≠ 0 := by
    rw [hLdef]
    exact_mod_cast (show n ≠ 0 by omega)
  have hLtop : L ≠ ⊤ := ENNReal.natCast_ne_top n
  -- the truncations tend to `0` by dominated convergence
  have htr : Tendsto (fun k => ∫⁻ x, min (Y k x) L ∂μ) atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence (fun _ => L)
      (fun k => (hY k).min measurable_const)
      (fun k => Filter.Eventually.of_forall fun x => min_le_right _ _)
      (by rw [lintegral_const]; exact ENNReal.mul_ne_top hLtop (measure_ne_top μ Set.univ))
      (by
        filter_upwards [hlim] with x hx
        have := hx.min (tendsto_const_nhds (x := L))
        simpa using this)
    simpa using h
  filter_upwards [ENNReal.tendsto_nhds_zero.mp htr (ε / 2) (pos_iff_ne_zero.mpr hε2)] with k hk
  have hpt : ∀ x, Y k x ≤ min (Y k x) L + Y k x ^ 2 * L⁻¹ := by
    intro x
    rcases le_total (Y k x) L with h | h
    · rw [min_eq_left h]
      exact le_self_add
    · refine le_add_left ?_
      rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl hL0) (Or.inl hLtop), sq]
      exact mul_le_mul_right h _
  calc ∫⁻ x, Y k x ∂μ ≤ ∫⁻ x, (min (Y k x) L + Y k x ^ 2 * L⁻¹) ∂μ := lintegral_mono hpt
    _ = ∫⁻ x, min (Y k x) L ∂μ + (∫⁻ x, Y k x ^ 2 ∂μ) * L⁻¹ := by
        rw [lintegral_add_left ((hY k).min measurable_const),
          lintegral_mul_const _ ((hY k).pow_const 2)]
    _ ≤ ε / 2 + C * L⁻¹ := add_le_add hk (mul_le_mul_left (hsq k) _)
    _ ≤ ε / 2 + ε / 2 := add_le_add le_rfl hn
    _ = ε := ENNReal.add_halves ε

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Almost sure convergence of the increment approximants** (Berestycki 2015, Section 2) from a
start `x ≠ 0`, under the joint law: the half-disc and exterior clocks converge locally uniformly. -/
theorem ae_prod_tendsto_dyadicIncrementApprox_of_ne_zero
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2)
    {x : ℂ} (hx : x ≠ 0) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), ∀ s t : ℝ≥0, ∃ L : ℝ,
      Tendsto (fun k => dyadicIncrementApprox γ
        (LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1)) k s t q.2) atTop (𝓝 L) := by
  have hPm := hh.isProbabilityMeasure
  have hγ2' : γ < 2 := by nlinarith
  obtain ⟨Fh, -, -, hFh⟩ :=
    exists_measurable_locally_uniform_limit_halfDiscClock_of_ne_zero hh hx hγ hγ2 0
  obtain ⟨Ge, -, hGe⟩ := exists_measurable_locally_uniform_limit_exterior_clock hh hγ hγ2' 0 x
  have hden : ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), ∀ k : ℕ,
      Continuous (fun z => (dyadicScale k) ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (dyadicScale k) z)) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_continuous_inserted_dyadic_density hh γ 0)
  have hfca : ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), ∀ r : ℝ, 0 < r →
      Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) r z) :=
    Measure.quasiMeasurePreserving_fst.ae (ae_continuous_fieldCircleAverage hh 0)
  filter_upwards [hFh, hGe, hden, hfca] with q h1 h2 h3 h4
  have hclock : ∀ t : ℝ≥0, Tendsto (fun j => lqgClockApprox γ
      (LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1)) (dyadicScale (j + 1)) q.2 t) atTop
        (𝓝 (Fh (q, t) + Ge (q, t))) := by
    intro t
    have hA : Tendsto (fun j => ∫ s in (0 : ℝ)..(t : ℝ),
        {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (dyadicScale (j+1)) z))
              (q.2 s.toNNReal)) atTop (𝓝 (Fh (q, t))) :=
      Metric.tendsto_nhds.mpr fun η hη => (h1 t η hη).mono fun j hj => by
        simpa [Real.dist_eq] using hj t le_rfl
    have hB : Tendsto (fun j => ∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | 1/2 < ‖z‖}.indicator (fun z =>
            (dyadicScale (j+1)) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (dyadicScale (j+1)) z))
                (q.2 s.toNNReal)) atTop (𝓝 (Ge (q, t))) :=
      Metric.tendsto_nhds.mpr fun η hη => (h2 t η hη).mono fun j hj => by
        simpa [Real.dist_eq] using hj t le_rfl
    refine (hA.add hB).congr fun j => ?_
    exact (lqgClockApprox_eq_halfDisc_add_exterior (h3 (j + 1)) q.2 t).symm
  intro s t
  refine ⟨(Fh (q, t) + Ge (q, t)) - (Fh (q, s) + Ge (q, s)), ?_⟩
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  refine ((hclock t).sub (hclock s)).congr fun j => ?_
  exact lqgClockApprox_sub_eq_dyadicIncrementApprox (h4 _ (dyadicScale_pos (j + 1))) q.2 s t

/-- **Positivity from a start `x ≠ 0` without insertion.** -/
theorem ae_ae_dyadicIncrementLiminf_pos_of_ne_zero_zero
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2)
    {x : ℂ} (hx : x ≠ 0) {a b : ℝ≥0} (hab : a < b) :
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
    set Y : ℕ → Ω × ContinuousPath ℂ → ℝ≥0∞ := fun k => (Prod.snd ⁻¹' E).indicator
      (fun q => ∫⁻ v in Ioc (a : ℝ) b,
        profileDensity γ 0 k (fun p => hcirc q.1 (dyadicScale p.1) p.2) (q.2 v.toNNReal))
      with hYdef
    have hYm : ∀ k, Measurable (Y k) := fun k => (hJm k).indicator (measurable_snd hE)
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
    have hlimY : ∀ᵐ q ∂(P.prod Q), Tendsto (fun k => Y k q) atTop (𝓝 0) := by
      filter_upwards [ae_prod_tendsto_dyadicIncrementApprox_of_ne_zero hh hγ hγ2 hx, hzeroE,
        hcontP] with q h1 h2 h3
      by_cases hqE : q.2 ∈ E
      · obtain ⟨L, hL⟩ := h1 a b
        have hJ : ∀ k, Y k q = ENNReal.ofReal (dyadicIncrementApprox γ
            (LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1)) k a b q.2) := by
          intro k
          rw [hYdef]
          simp only
          rw [Set.indicator_of_mem (show q ∈ Prod.snd ⁻¹' E from hqE)]
          exact lintegral_profileDensity_eq_ofReal hab'.le h3 k q.2
        have hofL : Tendsto (fun k => Y k q) atTop (𝓝 (ENNReal.ofReal L)) := by
          simp_rw [hJ]
          exact (ENNReal.continuous_ofReal.tendsto L).comp hL
        have hG0 := h2 hqE
        rw [profileIncrementLiminf_eq_liminf] at hG0
        have hG0' : liminf (fun k => Y k q) atTop = 0 := by
          rw [← hG0]
          congr 1
          funext k
          rw [hYdef]
          simp only
          rw [Set.indicator_of_mem (show q ∈ Prod.snd ⁻¹' E from hqE)]
        rw [hofL.liminf_eq] at hG0'
        rwa [hG0'] at hofL
      · have hY0 : ∀ k, Y k q = 0 := fun k => by
          rw [hYdef]
          simp only
          rw [Set.indicator_of_notMem (show q ∉ Prod.snd ⁻¹' E from hqE)]
        simp_rw [hY0]
        exact tendsto_const_nhds
    -- (ii) the means are bounded below
    have hmean : ∀ k, ENNReal.ofReal ((b : ℝ) - a) * Q E ≤ ∫⁻ q, Y k q ∂(P.prod Q) := by
      intro k
      rw [lintegral_prod_symm _ (hYm k).aemeasurable]
      calc ENNReal.ofReal ((b : ℝ) - a) * Q E =
            ∫⁻ w, E.indicator (fun _ => ENNReal.ofReal ((b : ℝ) - a)) w ∂Q := by
            rw [lintegral_indicator_const hE, mul_comm]
        _ ≤ ∫⁻ w, ∫⁻ ω, Y k (ω, w) ∂P ∂Q := by
            refine lintegral_mono fun w => ?_
            by_cases hw : w ∈ E
            · rw [Set.indicator_of_mem hw]
              have hY : ∀ ω, Y k (ω, w) = ∫⁻ v in Ioc (a : ℝ) b,
                  profileDensity γ 0 k (fun p => hcirc ω (dyadicScale p.1) p.2)
                    (w v.toNNReal) := fun ω => by
                rw [hYdef]
                simp only
                rw [Set.indicator_of_mem (show (ω, w) ∈ Prod.snd ⁻¹' E from hw)]
              simp_rw [hY]
              exact le_lintegral_profileIncrement hh γ k a b w
            · rw [Set.indicator_of_notMem hw]
              exact zero_le
    -- (iii) the second moments are bounded
    obtain ⟨Cb, hCb, hCbeq⟩ :=
      exists_planarBrownianMotion_interval_pair_enorm_rpow_neg x (a := γ ^ 2) (pow_pos hγ 2) hγ2
    set K := ENNReal.ofReal (((N : ℝ) + 1) ^ (4 * γ ^ 2) * 2 ^ (γ ^ 2)) with hKdef
    set Cfin := K * (ENNReal.ofReal ((b : ℝ) - a) ^ (2 - γ ^ 2 / 2) * Cb) with hCfindef
    have hCfin : Cfin ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by nlinarith) ENNReal.ofReal_ne_top)
        hCb.ne)
    set ν := Measure.map Real.toNNReal (volume.restrict (Icc (a : ℝ) ((a : ℝ) + ((b : ℝ) - a))))
      with hνdef
    have hFle : ∀ w : ContinuousPath ℂ, (∫⁻ s in Ioc (a : ℝ) b, ∫⁻ t in Ioc (a : ℝ) b,
        (ENNReal.ofReal ‖w s.toNNReal - w t.toNNReal‖) ^ (-γ ^ 2)) ≤
        ∫⁻ p : ℝ≥0 × ℝ≥0, (ENNReal.ofReal ‖w p.1 - w p.2‖) ^ (-γ ^ 2) ∂(ν.prod ν) := by
      intro w
      have hg : Measurable (fun p : ℝ≥0 × ℝ≥0 => (ENNReal.ofReal ‖w p.1 - w p.2‖) ^ (-γ ^ 2)) :=
        ((continuous_norm.comp ((w.continuous.comp continuous_fst).sub
          (w.continuous.comp continuous_snd))).measurable.ennreal_ofReal).pow_const _
      have hab2 : (a : ℝ) + ((b : ℝ) - a) = b := by ring
      rw [lintegral_prod _ hg.aemeasurable, hνdef, hab2,
        lintegral_map (hg.lintegral_prod_right') measurable_real_toNNReal]
      have hin : ∀ s : ℝ, ∫⁻ t, (ENNReal.ofReal ‖w s.toNNReal - w t‖) ^ (-γ ^ 2)
          ∂(Measure.map Real.toNNReal (volume.restrict (Icc (a : ℝ) b))) =
          ∫⁻ t in Icc (a : ℝ) b, (ENNReal.ofReal ‖w s.toNNReal - w t.toNNReal‖) ^ (-γ ^ 2) := by
        intro s
        have hgs : Measurable (fun t : ℝ≥0 =>
            (ENNReal.ofReal ‖w s.toNNReal - w t‖) ^ (-γ ^ 2)) :=
          ((continuous_norm.comp (continuous_const.sub w.continuous)).measurable.ennreal_ofReal).pow_const _
        rw [lintegral_map hgs measurable_real_toNNReal]
      simp_rw [hin]
      refine (lintegral_mono fun s => ?_).trans
        (lintegral_mono' (Measure.restrict_mono Ioc_subset_Icc_self le_rfl) le_rfl)
      exact lintegral_mono' (Measure.restrict_mono Ioc_subset_Icc_self le_rfl) le_rfl
    have hsq : ∀ k, ∫⁻ q, Y k q ^ 2 ∂(P.prod Q) ≤ Cfin := by
      intro k
      rw [lintegral_prod_symm _ ((hYm k).pow_const 2).aemeasurable]
      calc ∫⁻ w, ∫⁻ ω, Y k (ω, w) ^ 2 ∂P ∂Q
          ≤ ∫⁻ w, K * ∫⁻ p : ℝ≥0 × ℝ≥0, (ENNReal.ofReal ‖w p.1 - w p.2‖) ^ (-γ ^ 2)
              ∂(ν.prod ν) ∂Q := by
            refine lintegral_mono fun w => ?_
            by_cases hw : w ∈ E
            · have hY : ∀ ω, Y k (ω, w) = ∫⁻ v in Ioc (a : ℝ) b,
                  profileDensity γ 0 k (fun p => hcirc ω (dyadicScale p.1) p.2)
                    (w v.toNNReal) := fun ω => by
                rw [hYdef]
                simp only
                rw [Set.indicator_of_mem (show (ω, w) ∈ Prod.snd ⁻¹' E from hw)]
              simp_rw [hY]
              have hwN : ∀ v ∈ Ioc (a : ℝ) b, ‖w v.toNNReal‖ ≤ (N : ℝ) := fun v hv =>
                hw.2 v (Ioc_subset_Icc_self hv)
              exact (lintegral_profileIncrement_sq_le hh γ k w hwN).trans
                (mul_le_mul_right (hFle w) K)
            · have hY : ∀ ω, Y k (ω, w) = 0 := fun ω => by
                rw [hYdef]
                simp only
                rw [Set.indicator_of_notMem (show (ω, w) ∉ Prod.snd ⁻¹' E from hw)]
              simp_rw [hY]
              simp
        _ = K * ∫⁻ w, ∫⁻ p : ℝ≥0 × ℝ≥0, (ENNReal.ofReal ‖w p.1 - w p.2‖) ^ (-γ ^ 2)
              ∂(ν.prod ν) ∂Q := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = Cfin := by
            rw [hCfindef, hνdef]
            congr 1
            exact hCbeq a ((b : ℝ) - a) a.2 (sub_pos.mpr hab')
    -- (iv) the contradiction
    have hto := tendsto_lintegral_zero_of_ae_tendsto_zero_of_lintegral_sq_le hYm hlimY hCfin hsq
    have hle := ge_of_tendsto hto (Filter.Eventually.of_forall hmean)
    have hpos : 0 < ENNReal.ofReal ((b : ℝ) - a) * Q E :=
      ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab')).ne' hN
    exact absurd hle (not_le.mpr hpos)
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

end HarmonicBalls
