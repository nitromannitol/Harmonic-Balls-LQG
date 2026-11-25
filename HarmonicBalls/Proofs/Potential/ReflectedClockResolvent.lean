import HarmonicBalls.Proofs.Potential.ReflectedClockOccupationEveryStart

/-!
# The resolvent identity of the time change

Let `A` be a clock of reflected Brownian motion in `K₀` (`IsUnitSquarePCAF A`), unbounded from
every start in `K₀`, `τ_u` its right inverse and `Y_u = b_{τ_u}` the time change. For `β, c ≥ 0`
and measurable `f ≥ 0` put

* `G f(x) = E_x ∫_0^∞ e^{-β s} f(b_s) dA_s = E_x ∫_0^∞ e^{-β τ_u} f(Y_u) du` (`clockGreen`),
* `U f(x) = E_x ∫_0^∞ e^{-c u} e^{-β τ_u} f(Y_u) du` (`clockResolvent`).

**Resolvent identity** (`clockResolvent_add_clockResolvent_clockGreen`):
`U f + c U (G f) = G f` on `K₀`. Writing `1 - e^{-c u} = ∫_0^u c e^{-c r} dr`, Tonelli's theorem
gives `G f(x) - U f(x) = c ∫_0^∞ e^{-c r} E_x ∫_r^∞ e^{-β τ_u} f(Y_u) du dr`; by additivity of the
clock at `τ_r` (`τ_{r+v} = τ_r + τ_v ∘ θ_{τ_r}`) the inner integral is
`e^{-β τ_r} ∫_0^∞ e^{-β τ_v} f(Y_v) dv ∘ θ_{τ_r}`, and the strong Markov property at `τ_r`
(`lintegral_shift_pcafClockInverse_eq`) gives its mean `E_x[e^{-β τ_r} G f(Y_r)]`. This is the
computation of Fukushima–Oshima–Takeda, *Dirichlet forms and symmetric Markov processes*, 2nd ed.
2011, proof of Theorem 6.2.1, written in the time of the time change; all quantities are
nonnegative and the identity holds in `[0, ∞]`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The discounted weight `(s, y) ↦ e^{-β s} f(y)`. -/
noncomputable def discountWeight (β : ℝ) (f : ℂ → ℝ≥0∞) (p : ℝ × ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(β * p.1))) * f p.2

theorem measurable_exp_neg_mul (β : ℝ) :
    Measurable fun s : ℝ => ENNReal.ofReal (Real.exp (-(β * s))) :=
  (Real.continuous_exp.measurable.comp ((measurable_id.const_mul β).neg)).ennreal_ofReal

theorem measurable_discountWeight (β : ℝ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (discountWeight β f) :=
  ((measurable_exp_neg_mul β).comp measurable_fst).mul (hf.comp measurable_snd)

/-- The `β`-potential of the clock: `G f(x) = E_x ∫_0^∞ e^{-β s} f(b_s) dA_s`, computed in the
time of the time change. -/
noncomputable def clockGreen (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (β : ℝ) (f : ℂ → ℝ≥0∞)
    (x : ℂ) : ℝ≥0∞ :=
  ∫⁻ b, clockOccupation A (discountWeight β f) b ∂reflectedPlanarBrownianMotion 0 1 x

/-- The pathwise resolvent occupation `∫_0^∞ e^{-c u} e^{-β τ_u} f(Y_u) du`. -/
noncomputable def resolventOccupation (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (β c : ℝ)
    (f : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) : ℝ≥0∞ :=
  ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(c * u))) *
    discountWeight β f ((pcafClockInverse (clockRationalRegularization A) u.toNNReal b : ℝ),
      unitSquareTimeChangeRegularized A u.toNNReal b)

/-- The resolvent of the time change killed at rate `β` in the time of the motion:
`U f(x) = E_x ∫_0^∞ e^{-c u} e^{-β τ_u} f(Y_u) du`. -/
noncomputable def clockResolvent (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (β c : ℝ)
    (f : ℂ → ℝ≥0∞) (x : ℂ) : ℝ≥0∞ :=
  ∫⁻ b, resolventOccupation A β c f b ∂reflectedPlanarBrownianMotion 0 1 x

theorem measurable_resolventOccupation {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (β c : ℝ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (resolventOccupation A β c f) := by
  have h : Measurable fun p : ContinuousPath ℂ × ℝ => ENNReal.ofReal (Real.exp (-(c * p.2))) *
      discountWeight β f ((pcafClockInverse (clockRationalRegularization A) p.2.toNNReal p.1 : ℝ),
        unitSquareTimeChangeRegularized A p.2.toNNReal p.1) :=
    ((measurable_exp_neg_mul c).comp measurable_snd).mul
      ((measurable_discountWeight β hf).comp (measurable_clockInverse_timeChange_uncurry hA))
  exact h.lintegral_prod_right'

theorem measurable_clockGreen {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (β : ℝ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (clockGreen A β f) :=
  (measurable_clockOccupation hA (measurable_discountWeight β hf)).lintegral_kernel

theorem measurable_clockResolvent {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) (β c : ℝ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (clockResolvent A β c f) :=
  (measurable_resolventOccupation hA β c hf).lintegral_kernel

/-- `1 - e^{-c u} = ∫_0^u c e^{-c r} dr` for `c, u ≥ 0`. -/
theorem ofReal_one_sub_exp_eq_setLIntegral {c : ℝ} (hc : 0 ≤ c) {u : ℝ} (hu : 0 ≤ u) :
    ENNReal.ofReal (1 - Real.exp (-(c * u))) =
      ∫⁻ r in Ioo 0 u, ENNReal.ofReal (c * Real.exp (-(c * r))) := by
  have hcont : Continuous fun r : ℝ => c * Real.exp (-(c * r)) := by fun_prop
  have hint : IntervalIntegrable (fun r : ℝ => c * Real.exp (-(c * r))) volume 0 u :=
    hcont.intervalIntegrable _ _
  have hderiv : ∀ r ∈ uIcc 0 u, HasDerivAt (fun r : ℝ => -Real.exp (-(c * r)))
      (c * Real.exp (-(c * r))) r := by
    intro r _
    have h3 : HasDerivAt (fun r : ℝ => -Real.exp (r * -c)) (-(Real.exp (r * -c) * -c)) r :=
      ((hasDerivAt_mul_const (-c)).exp).neg
    have hfun : (fun r : ℝ => -Real.exp (-(c * r))) = fun r => -Real.exp (r * -c) := by
      funext y
      rw [show y * -c = -(c * y) by ring]
    rw [hfun, show c * Real.exp (-(c * r)) = -(Real.exp (r * -c) * -c) by
      rw [show r * -c = -(c * r) by ring]
      ring]
    exact h3
  have hval : ∫ r in Ioo 0 u, c * Real.exp (-(c * r)) = 1 - Real.exp (-(c * u)) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hu,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp only [mul_zero, neg_zero, Real.exp_zero]
    ring
  rw [← hval, ofReal_integral_eq_lintegral_ofReal
    ((hcont.integrableOn_Icc (a := 0) (b := u)).mono_set Ioo_subset_Icc_self)
    (ae_of_all _ fun r => mul_nonneg hc (Real.exp_pos _).le)]

/-- A set integral over `(r, ∞)` as a set integral over `(0, ∞)` of the translate. -/
theorem setLIntegral_Ioi_eq_add {g : ℝ → ℝ≥0∞} (r : ℝ) :
    ∫⁻ u in Ioi r, g u = ∫⁻ v in Ioi 0, g (v + r) := by
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi,
    ← lintegral_add_right_eq_self ((Ioi r).indicator g) r]
  refine lintegral_congr fun v => ?_
  by_cases hv : 0 < v
  · rw [indicator_of_mem (show v + r ∈ Ioi r from lt_add_of_pos_left r hv),
      indicator_of_mem (show v ∈ Ioi (0 : ℝ) from hv)]
  · rw [indicator_of_notMem (show v + r ∉ Ioi r from fun h => hv (by simpa using h)),
      indicator_of_notMem (show v ∉ Ioi (0 : ℝ) from hv)]

/-- **The resolvent identity of the time change**: `U f + c U (G f) = G f` on `K₀`. -/
theorem clockResolvent_add_clockResolvent_clockGreen {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A)
    (hU : ∀ z ∈ closedSquare 0 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun t => A t b) atTop atTop)
    (β : ℝ) {c : ℝ} (hc : 0 ≤ c) {f : ℂ → ℝ≥0∞} (hf : Measurable f) {x : ℂ}
    (hx : x ∈ closedSquare 0 1) :
    clockResolvent A β c f x + ENNReal.ofReal c * clockResolvent A β c (clockGreen A β f) x =
      clockGreen A β f x := by
  set φ : ContinuousPath ℂ × ℝ → ℝ × ℂ := fun p =>
    ((pcafClockInverse (clockRationalRegularization A) p.2.toNNReal p.1 : ℝ),
      unitSquareTimeChangeRegularized A p.2.toNNReal p.1) with hφ_def
  have hφ : Measurable φ := measurable_clockInverse_timeChange_uncurry hA.measurable
  set F : ContinuousPath ℂ × ℝ → ℝ≥0∞ := fun p => discountWeight β f (φ p) with hF_def
  have hFm : Measurable F := (measurable_discountWeight β hf).comp hφ
  have hem := measurable_exp_neg_mul c
  have hwm : Measurable fun r : ℝ => ENNReal.ofReal (c * Real.exp (-(c * r))) :=
    (measurable_const.mul (Real.continuous_exp.measurable.comp
      ((measurable_id.const_mul c).neg))).ennreal_ofReal
  set I : ContinuousPath ℂ × ℝ → ℝ≥0∞ := fun p => ∫⁻ u in Ioi p.2, F (p.1, u) with hI_def
  have hIm : Measurable I := by
    have h : Measurable fun q : (ContinuousPath ℂ × ℝ) × ℝ =>
        {q : (ContinuousPath ℂ × ℝ) × ℝ | q.1.2 < q.2}.indicator (fun q => F (q.1.1, q.2)) q :=
      (hFm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).indicator
        (measurableSet_lt (measurable_snd.comp measurable_fst) measurable_snd)
    have hIeq : I = fun p => ∫⁻ u, {q : (ContinuousPath ℂ × ℝ) × ℝ | q.1.2 < q.2}.indicator
        (fun q => F (q.1.1, q.2)) (p, u) := by
      funext p
      rw [hI_def]
      simp only
      rw [← lintegral_indicator measurableSet_Ioi]
      rfl
    rw [hIeq]
    exact h.lintegral_prod_right'
  set J : ℝ → ℝ≥0∞ := fun r => ∫⁻ b, discountWeight β (clockGreen A β f) (φ (b, r))
    ∂reflectedPlanarBrownianMotion 0 1 x with hJ_def
  -- the pathwise identity
  have hpath : ∀ b, clockOccupation A (discountWeight β f) b =
      resolventOccupation A β c f b +
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (c * Real.exp (-(c * r))) * I (b, r) := by
    intro b
    have h1 : ∀ u ∈ Ioi (0 : ℝ), F (b, u) = ENNReal.ofReal (Real.exp (-(c * u))) * F (b, u) +
        ∫⁻ r in Ioi (0 : ℝ), (Iio u).indicator
          (fun r => ENNReal.ofReal (c * Real.exp (-(c * r)))) r * F (b, u) := by
      intro u hu
      have hle : Real.exp (-(c * u)) ≤ 1 :=
        Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hc (le_of_lt hu)))
      have hw_int : ∫⁻ r in Ioi (0 : ℝ), (Iio u).indicator
          (fun r => ENNReal.ofReal (c * Real.exp (-(c * r)))) r =
          ENNReal.ofReal (1 - Real.exp (-(c * u))) := by
        rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
          Iio_inter_Ioi]
        exact (ofReal_one_sub_exp_eq_setLIntegral hc (le_of_lt hu)).symm
      rw [lintegral_mul_const _ (hwm.indicator measurableSet_Iio), hw_int, ← add_mul,
        ← ENNReal.ofReal_add (Real.exp_pos _).le (sub_nonneg.2 hle),
        show Real.exp (-(c * u)) + (1 - Real.exp (-(c * u))) = 1 by ring, ENNReal.ofReal_one,
        one_mul]
    have hswap : ∫⁻ u in Ioi (0 : ℝ), ∫⁻ r in Ioi (0 : ℝ), (Iio u).indicator
        (fun r => ENNReal.ofReal (c * Real.exp (-(c * r)))) r * F (b, u) =
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (c * Real.exp (-(c * r))) * I (b, r) := by
      have hmeas : Measurable fun q : ℝ × ℝ => {q : ℝ × ℝ | q.2 < q.1}.indicator
          (fun q => ENNReal.ofReal (c * Real.exp (-(c * q.2)))) q * F (b, q.1) :=
        ((hwm.comp measurable_snd).indicator (measurableSet_lt measurable_snd measurable_fst)).mul
          (hFm.comp (measurable_const.prodMk measurable_fst))
      rw [lintegral_lintegral_swap (by exact hmeas.aemeasurable)]
      refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
      have h2 : ∀ u, (Iio u).indicator (fun r => ENNReal.ofReal (c * Real.exp (-(c * r)))) r *
          F (b, u) = ENNReal.ofReal (c * Real.exp (-(c * r))) *
            (Ioi r).indicator (fun u => F (b, u)) u := by
        intro u
        by_cases hru : r < u
        · rw [indicator_of_mem (show r ∈ Iio u from hru),
            indicator_of_mem (show u ∈ Ioi r from hru)]
        · rw [indicator_of_notMem (show r ∉ Iio u from hru),
            indicator_of_notMem (show u ∉ Ioi r from hru), zero_mul, mul_zero]
      simp_rw [h2]
      rw [lintegral_const_mul _ (show Measurable fun u => (Ioi r).indicator (fun u => F (b, u)) u
          from (hFm.comp measurable_prodMk_left).indicator measurableSet_Ioi),
        lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
        inter_eq_left.2 (Ioi_subset_Ioi (le_of_lt hr))]
    have hOG : clockOccupation A (discountWeight β f) b = ∫⁻ u in Ioi (0 : ℝ), F (b, u) := rfl
    have hOU : resolventOccupation A β c f b =
        ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(c * u))) * F (b, u) := rfl
    rw [hOG, hOU, ← hswap, ← lintegral_add_left
      (f := fun u => ENNReal.ofReal (Real.exp (-(c * u))) * F (b, u))
      (hem.mul (hFm.comp measurable_prodMk_left))]
    exact setLIntegral_congr_fun measurableSet_Ioi h1
  -- the mean of `I` at a fixed time, by the strong Markov property at `τ_r`
  have hfix : ∀ r ∈ Ioi (0 : ℝ), ∫⁻ b, I (b, r) ∂reflectedPlanarBrownianMotion 0 1 x = J r := by
    intro r hr
    have h1 : ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x, I (b, r) =
        ENNReal.ofReal (Real.exp (-(β * (pcafClockInverse A r.toNNReal b : ℝ)))) *
          clockOccupation A (discountWeight β f)
            (ContinuousPath.shift (pcafClockInverse A r.toNNReal b) b) := by
      filter_upwards [ae_pcafClockInverse_regularization_eq hA hx,
        ae_pcafClockInverse_add_eq_shift hA hx (hU x hx) r.toNNReal,
        ae_eval_pcafClockInverse_add_eq_shift hA hx (hU x hx) r.toNNReal] with b hreg hadd heval
      have key : ∀ v ∈ Ioi (0 : ℝ), F (b, v + r) =
          ENNReal.ofReal (Real.exp (-(β * (pcafClockInverse A r.toNNReal b : ℝ)))) *
            F (ContinuousPath.shift (pcafClockInverse A r.toNNReal b) b, v) := by
        intro v hv
        have hvr : (v + r).toNNReal = r.toNNReal + v.toNNReal := by
          rw [add_comm]
          exact Real.toNNReal_add hr.le (le_of_lt hv)
        show discountWeight β f
            ((pcafClockInverse (clockRationalRegularization A) (v + r).toNNReal b : ℝ),
              b (pcafClockInverse (clockRationalRegularization A) (v + r).toNNReal b)) =
          ENNReal.ofReal (Real.exp (-(β * (pcafClockInverse A r.toNNReal b : ℝ)))) *
            discountWeight β f ((pcafClockInverse (clockRationalRegularization A) v.toNNReal
              (ContinuousPath.shift (pcafClockInverse A r.toNNReal b) b) : ℝ),
              ContinuousPath.shift (pcafClockInverse A r.toNNReal b) b
                (pcafClockInverse (clockRationalRegularization A) v.toNNReal
                  (ContinuousPath.shift (pcafClockInverse A r.toNNReal b) b)))
        rw [hvr, hreg, heval v.toNNReal, hadd v.toNNReal]
        simp only [discountWeight, NNReal.coe_add, mul_add, neg_add, Real.exp_add]
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
      calc I (b, r) = ∫⁻ v in Ioi (0 : ℝ), F (b, v + r) :=
            setLIntegral_Ioi_eq_add (g := fun u => F (b, u)) r
        _ = ∫⁻ v in Ioi (0 : ℝ),
            ENNReal.ofReal (Real.exp (-(β * (pcafClockInverse A r.toNNReal b : ℝ)))) *
              F (ContinuousPath.shift (pcafClockInverse A r.toNNReal b) b, v) :=
            setLIntegral_congr_fun measurableSet_Ioi key
        _ = ENNReal.ofReal (Real.exp (-(β * (pcafClockInverse A r.toNNReal b : ℝ)))) *
            clockOccupation A (discountWeight β f)
              (ContinuousPath.shift (pcafClockInverse A r.toNNReal b) b) :=
            lintegral_const_mul _ (hFm.comp measurable_prodMk_left)
    have hH : Measurable fun p : ℝ≥0 × ContinuousPath ℂ =>
        ENNReal.ofReal (Real.exp (-(β * (p.1 : ℝ)))) * clockOccupation A (discountWeight β f) p.2 :=
      ((measurable_exp_neg_mul β).comp (NNReal.continuous_coe.measurable.comp measurable_fst)).mul
        ((measurable_clockOccupation hA.measurable (measurable_discountWeight β hf)).comp
          measurable_snd)
    have h2 := lintegral_shift_pcafClockInverse_eq hA hx (hU x hx) r.toNNReal hH
    refine (lintegral_congr_ae h1).trans (h2.trans (lintegral_congr_ae ?_))
    filter_upwards [ae_pcafClockInverse_regularization_eq hA hx] with b hreg
    show ∫⁻ ω', ENNReal.ofReal (Real.exp (-(β * (pcafClockInverse A r.toNNReal b : ℝ)))) *
        clockOccupation A (discountWeight β f) ω'
          ∂reflectedPlanarBrownianMotion 0 1 (b (pcafClockInverse A r.toNNReal b)) =
      ENNReal.ofReal (Real.exp (-(β *
        (pcafClockInverse (clockRationalRegularization A) r.toNNReal b : ℝ)))) *
        clockGreen A β f (b (pcafClockInverse (clockRationalRegularization A) r.toNNReal b))
    rw [hreg, lintegral_const_mul _
      (measurable_clockOccupation hA.measurable (measurable_discountWeight β hf))]
    rfl
  -- Tonelli in `(b, r)`
  have hB : ∫⁻ b, (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (c * Real.exp (-(c * r))) * I (b, r))
      ∂reflectedPlanarBrownianMotion 0 1 x = ∫⁻ r in Ioi (0 : ℝ),
        ENNReal.ofReal (c * Real.exp (-(c * r))) *
          ∫⁻ b, I (b, r) ∂reflectedPlanarBrownianMotion 0 1 x := by
    rw [lintegral_lintegral_swap (by exact ((hwm.comp measurable_snd).mul hIm).aemeasurable)]
    refine lintegral_congr fun r => ?_
    exact lintegral_const_mul _ (hIm.comp measurable_prodMk_right)
  have hD : clockResolvent A β c (clockGreen A β f) x =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(c * r))) * J r := by
    have hmeas : Measurable fun p : ContinuousPath ℂ × ℝ =>
        ENNReal.ofReal (Real.exp (-(c * p.2))) * discountWeight β (clockGreen A β f) (φ p) :=
      (hem.comp measurable_snd).mul ((measurable_discountWeight β
        (measurable_clockGreen hA.measurable β hf)).comp hφ)
    have h1 : clockResolvent A β c (clockGreen A β f) x =
        ∫⁻ (b : ContinuousPath ℂ), (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(c * r))) *
          discountWeight β (clockGreen A β f) (φ (b, r))) ∂reflectedPlanarBrownianMotion 0 1 x :=
      rfl
    have hmeas2 : ∀ r : ℝ, Measurable fun b : ContinuousPath ℂ =>
        discountWeight β (clockGreen A β f) (φ (b, r)) := fun r =>
      (measurable_discountWeight β (measurable_clockGreen hA.measurable β hf)).comp
        (hφ.comp measurable_prodMk_right)
    rw [h1, lintegral_lintegral_swap (by exact hmeas.aemeasurable)]
    refine lintegral_congr fun r => ?_
    exact lintegral_const_mul _ (hmeas2 r)
  have hG : clockGreen A β f x = ∫⁻ (b : ContinuousPath ℂ), (resolventOccupation A β c f b +
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (c * Real.exp (-(c * r))) * I (b, r))
        ∂reflectedPlanarBrownianMotion 0 1 x := by
    unfold clockGreen
    exact lintegral_congr hpath
  have hsplit : ∫⁻ (b : ContinuousPath ℂ), (resolventOccupation A β c f b +
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (c * Real.exp (-(c * r))) * I (b, r))
        ∂reflectedPlanarBrownianMotion 0 1 x = clockResolvent A β c f x +
      ∫⁻ (b : ContinuousPath ℂ), (∫⁻ r in Ioi (0 : ℝ),
        ENNReal.ofReal (c * Real.exp (-(c * r))) * I (b, r)) ∂reflectedPlanarBrownianMotion 0 1 x :=
    lintegral_add_left (measurable_resolventOccupation hA.measurable β c hf) _
  have hlast : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (c * Real.exp (-(c * r))) * J r =
      ENNReal.ofReal c * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(c * r))) * J r := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun r => ?_
    rw [ENNReal.ofReal_mul hc, mul_assoc]
  have hmid : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (c * Real.exp (-(c * r))) *
      ∫⁻ b, I (b, r) ∂reflectedPlanarBrownianMotion 0 1 x =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (c * Real.exp (-(c * r))) * J r :=
    setLIntegral_congr_fun measurableSet_Ioi fun r hr => by rw [hfix r hr]
  rw [hG, hsplit, hB, hmid, hlast, hD]

end HarmonicBalls
