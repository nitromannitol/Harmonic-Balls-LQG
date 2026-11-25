import HarmonicBalls.Proofs.Potential.ReflectedDiscountedGreen
import HarmonicBalls.Proofs.Potential.ReflectedClockUnbounded
import HarmonicBalls.Proofs.Potential.ReflectedClockResolvent

/-!
# The centered resolvent identity of the time change

Let `A` be a clock of reflected Brownian motion in `K₀` whose Revuz measure `ν` is a probability
measure with upper power bounds; by `ae_tendsto_atTop_of_isUnitSquarePCAF` the clock is unbounded
from every start. For bounded measurable `h` let
`R^β_c h(x) = E_x ∫_0^∞ e^{-c u} e^{-β τ_u} h(Y_u) du` (`resolventReal`), the real form of the
resolvent `clockResolvent` (`resolventReal_eq_toReal`).

**Centered resolvent identity** (`resolventReal_add_resolventReal_greenPotential`): for bounded
measurable `f` with `∫ f dν = 0`, `c > 0` and `x ∈ K₀`,
`R_c f(x) + c R_c (V f)(x) = V f(x)`, where `V f(z) = ∫ g(z, y) f(y) ν(dy)` is the centered Green
potential and `R_c = R^0_c`.

For `β > 0` and `p ≥ 0` the resolvent identity `U p + c U G_β p = G_β p` of
`ReflectedClockResolvent.lean` holds with `G_β p(z) = ∫ g̃_β(z, y) p(y) ν(dy) + ν(p)/β`
(`clockGreen_eq_ofReal`); writing `f = f⁺ - f⁻` with `ν(f⁺) = ν(f⁻)`, the terms `ν(f^±)/β` cancel
(`resolventReal_add_resolventReal_discountedGreenPotential`), and the identity passes to the limit
`β → 0` by dominated convergence, since the discounted potentials are bounded uniformly in `β` and
converge to `V f` on `K₀`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess
open scoped ENNReal NNReal

namespace HarmonicBalls

variable {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}

/-- The time-change pair `(τ̄_u, Y_u)` of the regularized clock. -/
noncomputable def clockPair (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (q : ContinuousPath ℂ × ℝ) :
    ℝ × ℂ :=
  ((pcafClockInverse (clockRationalRegularization A) q.2.toNNReal q.1 : ℝ),
    unitSquareTimeChangeRegularized A q.2.toNNReal q.1)

theorem measurable_clockPair (hA : ∀ t, Measurable (A t)) : Measurable (clockPair A) :=
  measurable_clockInverse_timeChange_uncurry hA

/-- The integrand `e^{-c u} e^{-β τ_u} h(Y_u)`. -/
noncomputable def resolventIntegrand (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (β c : ℝ) (h : ℂ → ℝ)
    (q : ContinuousPath ℂ × ℝ) : ℝ :=
  Real.exp (-(c * q.2)) * (Real.exp (-(β * (clockPair A q).1)) * h (clockPair A q).2)

/-- The real resolvent `R^β_c h(x) = E_x ∫_0^∞ e^{-c u} e^{-β τ_u} h(Y_u) du`. -/
noncomputable def resolventReal (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (β c : ℝ) (h : ℂ → ℝ)
    (x : ℂ) : ℝ :=
  ∫ b, (∫ u in Ioi (0 : ℝ), resolventIntegrand A β c h (b, u)) ∂reflectedPlanarBrownianMotion 0 1 x

theorem measurable_resolventIntegrand (hA : ∀ t, Measurable (A t)) (β c : ℝ) {h : ℂ → ℝ}
    (hh : Measurable h) : Measurable (resolventIntegrand A β c h) :=
  (Real.continuous_exp.measurable.comp ((measurable_snd.const_mul c).neg)).mul
    ((Real.continuous_exp.measurable.comp (((measurable_clockPair hA).fst.const_mul β).neg)).mul
      (hh.comp (measurable_clockPair hA).snd))

theorem clockPair_fst_nonneg (q : ContinuousPath ℂ × ℝ) : 0 ≤ (clockPair A q).1 :=
  NNReal.coe_nonneg _

theorem abs_resolventIntegrand_le {β c : ℝ} (hβ : 0 ≤ β) {h : ℂ → ℝ} {M : ℝ}
    (hM : ∀ z, |h z| ≤ M) (q : ContinuousPath ℂ × ℝ) :
    |resolventIntegrand A β c h q| ≤ M * Real.exp (-(c * q.2)) := by
  unfold resolventIntegrand
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  have h1 : Real.exp (-(β * (clockPair A q).1)) ≤ 1 :=
    exp_neg_mul_le_one hβ (clockPair_fst_nonneg q)
  have h2 := hM (clockPair A q).2
  have h3 : 0 ≤ Real.exp (-(c * q.2)) := (Real.exp_pos _).le
  calc Real.exp (-(c * q.2)) * (Real.exp (-(β * (clockPair A q).1)) * |h (clockPair A q).2|)
      ≤ Real.exp (-(c * q.2)) * (1 * M) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one) h3
    _ = M * Real.exp (-(c * q.2)) := by ring

theorem integrableOn_exp_neg_mul {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ => Real.exp (-(c * u))) (Ioi 0) := by
  have := exp_neg_integrableOn_Ioi 0 hc
  simpa only [neg_mul] using this

theorem setIntegral_exp_neg_mul {c : ℝ} (hc : 0 < c) :
    ∫ u in Ioi (0 : ℝ), Real.exp (-(c * u)) = 1 / c := by
  have := integral_exp_mul_Ioi (a := -c) (by linarith) 0
  simp only [mul_zero, Real.exp_zero, neg_mul] at this
  rw [this]
  field_simp

/-- Integrability of the inner integrand, and the bound `M / c` of the inner integral. -/
theorem integrable_resolventIntegrand (hA : ∀ t, Measurable (A t)) {β c : ℝ} (hβ : 0 ≤ β)
    (hc : 0 < c) {h : ℂ → ℝ} (hh : Measurable h) {M : ℝ} (hM : ∀ z, |h z| ≤ M)
    (b : ContinuousPath ℂ) :
    IntegrableOn (fun u => resolventIntegrand A β c h (b, u)) (Ioi 0) ∧
      |∫ u in Ioi (0 : ℝ), resolventIntegrand A β c h (b, u)| ≤ M / c := by
  have hm : Measurable fun u => resolventIntegrand A β c h (b, u) :=
    (measurable_resolventIntegrand hA β c hh).comp (measurable_const.prodMk measurable_id)
  have hmaj : IntegrableOn (fun u : ℝ => M * Real.exp (-(c * u))) (Ioi 0) :=
    (integrableOn_exp_neg_mul hc).const_mul M
  have hle : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ‖resolventIntegrand A β c h (b, u)‖ ≤
      M * Real.exp (-(c * u)) :=
    Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]; exact abs_resolventIntegrand_le hβ hM (b, u)
  refine ⟨hmaj.mono' hm.aestronglyMeasurable hle, ?_⟩
  have h := norm_integral_le_of_norm_le hmaj hle
  rw [Real.norm_eq_abs, integral_const_mul, setIntegral_exp_neg_mul hc] at h
  exact h.trans_eq (by ring)

theorem measurable_inner_resolventIntegrand (hA : ∀ t, Measurable (A t)) (β c : ℝ) {h : ℂ → ℝ}
    (hh : Measurable h) :
    Measurable fun b => ∫ u in Ioi (0 : ℝ), resolventIntegrand A β c h (b, u) := by
  have hs : StronglyMeasurable (resolventIntegrand A β c h) :=
    (measurable_resolventIntegrand hA β c hh).stronglyMeasurable
  exact (hs.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))).measurable

theorem integrable_inner_resolventIntegrand (hA : ∀ t, Measurable (A t)) {β c : ℝ} (hβ : 0 ≤ β)
    (hc : 0 < c) {h : ℂ → ℝ} (hh : Measurable h) {M : ℝ} (hM : ∀ z, |h z| ≤ M) (x : ℂ) :
    Integrable (fun b => ∫ u in Ioi (0 : ℝ), resolventIntegrand A β c h (b, u))
      (reflectedPlanarBrownianMotion 0 1 x) :=
  Integrable.of_bound (measurable_inner_resolventIntegrand hA β c hh).aestronglyMeasurable (M / c)
    (Eventually.of_forall fun b => by
      rw [Real.norm_eq_abs]; exact (integrable_resolventIntegrand hA hβ hc hh hM b).2)

/-- **Linearity**: `R(h₁ - h₂) = R h₁ - R h₂`. -/
theorem resolventReal_sub (hA : ∀ t, Measurable (A t)) {β c : ℝ} (hβ : 0 ≤ β) (hc : 0 < c)
    {h₁ h₂ : ℂ → ℝ} (hh₁ : Measurable h₁) (hh₂ : Measurable h₂) {M₁ M₂ : ℝ}
    (hM₁ : ∀ z, |h₁ z| ≤ M₁) (hM₂ : ∀ z, |h₂ z| ≤ M₂) (x : ℂ) :
    resolventReal A β c (fun z => h₁ z - h₂ z) x =
      resolventReal A β c h₁ x - resolventReal A β c h₂ x := by
  unfold resolventReal
  rw [← integral_sub (integrable_inner_resolventIntegrand hA hβ hc hh₁ hM₁ x)
    (integrable_inner_resolventIntegrand hA hβ hc hh₂ hM₂ x)]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only
  rw [← integral_sub (integrable_resolventIntegrand hA hβ hc hh₁ hM₁ b).1
    (integrable_resolventIntegrand hA hβ hc hh₂ hM₂ b).1]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [resolventIntegrand]
  ring

/-- `R_c` of a constant: `R_c k = k / c`. -/
theorem resolventReal_const {c : ℝ} (hc : 0 < c) (k : ℝ) (x : ℂ) :
    resolventReal A 0 c (fun _ => k) x = k / c := by
  unfold resolventReal resolventIntegrand
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul]
  rw [integral_mul_const, setIntegral_exp_neg_mul hc]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- The time-changed positions lie in `K₀`. -/
theorem ae_forall_clockPair_mem {x : ℂ} :
    ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x, ∀ u, (clockPair A (b, u)).2 ∈ closedSquare 0 1 := by
  filter_upwards [OptionalTime.ae_forall_mem_closedSquare_reflected x] with b hb u
  exact hb _

/-- **The resolvent only sees `K₀`.** -/
theorem resolventReal_congr {β c : ℝ} {h₁ h₂ : ℂ → ℝ}
    (h : ∀ z ∈ closedSquare (0 : ℂ) 1, h₁ z = h₂ z) (x : ℂ) :
    resolventReal A β c h₁ x = resolventReal A β c h₂ x := by
  unfold resolventReal
  refine integral_congr_ae ?_
  filter_upwards [ae_forall_clockPair_mem (A := A) (x := x)] with b hb
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [resolventIntegrand, h _ (hb u)]

theorem clockResolvent_congr {β c : ℝ} {f₁ f₂ : ℂ → ℝ≥0∞}
    (h : ∀ z ∈ closedSquare (0 : ℂ) 1, f₁ z = f₂ z) (x : ℂ) :
    clockResolvent A β c f₁ x = clockResolvent A β c f₂ x := by
  unfold clockResolvent resolventOccupation
  refine lintegral_congr_ae ?_
  filter_upwards [ae_forall_clockPair_mem (A := A) (x := x)] with b hb
  refine lintegral_congr fun u => ?_
  simp only [discountWeight]
  rw [h (unitSquareTimeChangeRegularized A u.toNNReal b) (hb u)]

theorem resolventIntegrand_nonneg {β c : ℝ} {h : ℂ → ℝ} (h0 : ∀ z, 0 ≤ h z)
    (q : ContinuousPath ℂ × ℝ) : 0 ≤ resolventIntegrand A β c h q :=
  mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (h0 _))

theorem resolventReal_nonneg {β c : ℝ} {h : ℂ → ℝ} (h0 : ∀ z, 0 ≤ h z) (x : ℂ) :
    0 ≤ resolventReal A β c h x := by
  unfold resolventReal
  exact integral_nonneg fun _ => setIntegral_nonneg measurableSet_Ioi fun _ _ =>
    resolventIntegrand_nonneg h0 _

/-- **The real resolvent of a nonnegative function** is the resolvent of the time change. -/
theorem clockResolvent_eq_ofReal (hA : ∀ t, Measurable (A t)) {β c : ℝ} (hβ : 0 ≤ β) (hc : 0 < c)
    {h : ℂ → ℝ} (hh : Measurable h) (h0 : ∀ z, 0 ≤ h z) {M : ℝ} (hM : ∀ z, |h z| ≤ M) (x : ℂ) :
    clockResolvent A β c (fun z => ENNReal.ofReal (h z)) x =
      ENNReal.ofReal (resolventReal A β c h x) := by
  have hinner : ∀ b, resolventOccupation A β c (fun z => ENNReal.ofReal (h z)) b =
      ENNReal.ofReal (∫ u in Ioi (0 : ℝ), resolventIntegrand A β c h (b, u)) := by
    intro b
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_resolventIntegrand hA hβ hc hh hM b).1
      (Eventually.of_forall fun u => resolventIntegrand_nonneg h0 _)]
    unfold resolventOccupation discountWeight
    refine lintegral_congr fun u => ?_
    unfold resolventIntegrand
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_mul (Real.exp_pos _).le]
    rfl
  unfold clockResolvent resolventReal
  simp_rw [hinner]
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_inner_resolventIntegrand hA hβ hc hh hM x)
    (Eventually.of_forall fun b => setIntegral_nonneg measurableSet_Ioi fun _ _ =>
      resolventIntegrand_nonneg h0 _)]

/-- **Convergence of the resolvents** as `β → 0`, for bounded measurable functions converging on
`K₀`. -/
theorem tendsto_resolventReal (hA : ∀ t, Measurable (A t)) {c : ℝ} (hc : 0 < c)
    {h : ℕ → ℂ → ℝ} {h₀ : ℂ → ℝ} (hh : ∀ n, Measurable (h n)) {M : ℝ}
    (hM : ∀ n z, |h n z| ≤ M) (hlim : ∀ z ∈ closedSquare (0 : ℂ) 1,
      Tendsto (fun n => h n z) atTop (𝓝 (h₀ z))) (x : ℂ) :
    Tendsto (fun n : ℕ => resolventReal A (1 / (n + 1)) c (h n) x) atTop
      (𝓝 (resolventReal A 0 c h₀ x)) := by
  have hβ : ∀ n : ℕ, (0 : ℝ) ≤ 1 / (n + 1) := fun n => by positivity
  have hβl : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  unfold resolventReal
  refine tendsto_integral_of_dominated_convergence (μ := reflectedPlanarBrownianMotion 0 1 x)
    (fun _ => M / c)
    (fun n => (measurable_inner_resolventIntegrand hA _ c (hh n)).aestronglyMeasurable)
    (integrable_const _) (fun n => Eventually.of_forall fun b => by
      rw [Real.norm_eq_abs]; exact (integrable_resolventIntegrand hA (hβ n) hc (hh n) (hM n) b).2) ?_
  filter_upwards [ae_forall_clockPair_mem (A := A) (x := x)] with b hb
  refine tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioi (0 : ℝ)))
    (fun u => M * Real.exp (-(c * u)))
    (fun n => ((measurable_resolventIntegrand hA _ c (hh n)).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    ((integrableOn_exp_neg_mul hc).const_mul M)
    (fun n => Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]; exact abs_resolventIntegrand_le (hβ n) (hM n) (b, u)) ?_
  refine Eventually.of_forall fun u => ?_
  unfold resolventIntegrand
  have he : Tendsto (fun n : ℕ => Real.exp (-((1 : ℝ) / (n + 1) * (clockPair A (b, u)).1)))
      atTop (𝓝 (Real.exp (-(0 * (clockPair A (b, u)).1)))) :=
    (Real.continuous_exp.tendsto _).comp ((hβl.mul_const _).neg)
  exact tendsto_const_nhds.mul (he.mul (hlim _ (hb u)))

section Identity

variable [IsProbabilityMeasure (unitSquareRevuzMeasure A)]

theorem IsUnitSquarePCAF.hU (hA : IsUnitSquarePCAF A) :
    ∀ z ∈ closedSquare (0 : ℂ) 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun t => A t b) atTop atTop := fun z hz =>
  ae_tendsto_atTop_of_isUnitSquarePCAF hA (by simp) hz

theorem integrable_of_abs_le {ν : Measure ℂ} [IsFiniteMeasure ν] {p : ℂ → ℝ} (hp : Measurable p)
    {M : ℝ} (hM : ∀ z, |p z| ≤ M) : Integrable p ν :=
  Integrable.of_bound hp.aestronglyMeasurable M
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM y)

theorem discountedGreenPotential_add_eq (hν : IsUpperRegularSpeed (unitSquareRevuzMeasure A))
    {β : ℝ} (hβ : 0 < β) {p : ℂ → ℝ} (hp : Measurable p) {M : ℝ}
    (hM : ∀ z, |p z| ≤ M) {z : ℂ} (hz : z ∈ closedSquare (0 : ℂ) 1) :
    Integrable (fun y => (discountedGreenKernel β z y + 1 / β) * p y) (unitSquareRevuzMeasure A) ∧
      discountedGreenPotential (unitSquareRevuzMeasure A) β p z +
        (∫ y, p y ∂unitSquareRevuzMeasure A) / β =
      ∫ y, (discountedGreenKernel β z y + 1 / β) * p y ∂unitSquareRevuzMeasure A := by
  obtain ⟨B, -, hB⟩ := hν.exists_potential_bound
  obtain ⟨hint, -⟩ := (hB hp hM z hz).1 β hβ.le
  have hp1 := integrable_of_abs_le (ν := unitSquareRevuzMeasure A) hp hM
  refine ⟨(hint.add (hp1.const_mul (1 / β))).congr (Eventually.of_forall fun y => by
      simp only [Pi.add_apply]; ring), ?_⟩
  unfold discountedGreenPotential
  rw [div_eq_mul_one_div, mul_comm, ← integral_const_mul, ← integral_add hint
    (hp1.const_mul (1 / β))]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

/-- **The potential of the time change as a Green potential**: for `β > 0` and bounded measurable
`p ≥ 0`, `G_β p(z) = ∫ g̃_β(z, y) p(y) ν(dy) + ν(p)/β ≥ 0` on `K₀`. -/
theorem clockGreen_eq_ofReal (hA : IsUnitSquarePCAF A)
    (hν : IsUpperRegularSpeed (unitSquareRevuzMeasure A)) {β : ℝ} (hβ : 0 < β) {p : ℂ → ℝ}
    (hp : Measurable p) (hp0 : ∀ z, 0 ≤ p z) {M : ℝ} (hM : ∀ z, |p z| ≤ M) {z : ℂ}
    (hz : z ∈ closedSquare (0 : ℂ) 1) :
    0 ≤ discountedGreenPotential (unitSquareRevuzMeasure A) β p z +
        (∫ y, p y ∂unitSquareRevuzMeasure A) / β ∧
      clockGreen A β (fun y => ENNReal.ofReal (p y)) z = ENNReal.ofReal
        (discountedGreenPotential (unitSquareRevuzMeasure A) β p z +
          (∫ y, p y ∂unitSquareRevuzMeasure A) / β) := by
  obtain ⟨hsum, hval⟩ := discountedGreenPotential_add_eq hν hβ hp hM hz
  have hnn : 0 ≤ᵐ[unitSquareRevuzMeasure A]
      fun y => (discountedGreenKernel β z y + 1 / β) * p y := by
    filter_upwards [hν.ae_mem, hν.ae_ne hz] with y hy hyz
    exact mul_nonneg (squareGreenKernel_eq_ofReal hβ hz hy (Ne.symm hyz)).1 (hp0 y)
  refine ⟨by rw [hval]; exact integral_nonneg_of_ae hnn, ?_⟩
  rw [clockGreen_eq_lintegral_squareGreenKernel hA hA.hU hν.carried hz β
    (f := fun y => ENNReal.ofReal (p y)) (ENNReal.measurable_ofReal.comp hp), hval,
    ofReal_integral_eq_lintegral_ofReal hsum hnn]
  refine lintegral_congr_ae ?_
  filter_upwards [hν.ae_mem, hν.ae_ne hz] with y hy hyz
  obtain ⟨h0, h⟩ := squareGreenKernel_eq_ofReal hβ hz hy (Ne.symm hyz)
  rw [h, ENNReal.ofReal_mul h0]

/-- **The resolvent identity in real form** for `β > 0` and bounded measurable `p ≥ 0`:
`R^β_c p + c R^β_c (G_β p) = G_β p` on `K₀`, with `G_β p = ∫ g̃_β(·, y) p(y) ν(dy) + ν(p)/β`. -/
theorem resolventReal_add_resolventReal_clockGreen (hA : IsUnitSquarePCAF A)
    (hν : IsUpperRegularSpeed (unitSquareRevuzMeasure A)) {β c : ℝ} (hβ : 0 < β) (hc : 0 < c)
    {p : ℂ → ℝ} (hp : Measurable p) (hp0 : ∀ z, 0 ≤ p z) {M : ℝ} (hM : ∀ z, |p z| ≤ M) {x : ℂ}
    (hx : x ∈ closedSquare (0 : ℂ) 1) :
    resolventReal A β c p x + c * resolventReal A β c ((closedSquare 0 1).indicator fun z =>
        discountedGreenPotential (unitSquareRevuzMeasure A) β p z +
          (∫ y, p y ∂unitSquareRevuzMeasure A) / β) x =
      discountedGreenPotential (unitSquareRevuzMeasure A) β p x +
        (∫ y, p y ∂unitSquareRevuzMeasure A) / β := by
  set ν := unitSquareRevuzMeasure A with hν_def
  obtain ⟨B, hB0, hB⟩ := hν.exists_potential_bound
  set Gp : ℂ → ℝ := (closedSquare 0 1).indicator fun z =>
    discountedGreenPotential ν β p z + (∫ y, p y ∂ν) / β with hGp
  have hGpm : Measurable Gp :=
    ((measurable_discountedGreenPotential β hp).add measurable_const).indicator
      measurableSet_closedSquare_zero_one
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hGp0 : ∀ z, 0 ≤ Gp z := fun z => by
    by_cases hz : z ∈ closedSquare (0 : ℂ) 1
    · rw [hGp, indicator_of_mem hz]
      exact (clockGreen_eq_ofReal hA hν hβ hp hp0 hM hz).1
    · rw [hGp, indicator_of_notMem hz]
  have hGpb : ∀ z, |Gp z| ≤ M * B + M / β := fun z => by
    by_cases hz : z ∈ closedSquare (0 : ℂ) 1
    · rw [hGp, indicator_of_mem hz]
      have h1 := ((hB hp hM z hz).1 β hβ.le).2
      have h2 : |(∫ y, p y ∂ν) / β| ≤ M / β := by
        rw [abs_div, abs_of_pos hβ]
        refine div_le_div_of_nonneg_right ?_ hβ.le
        calc |∫ y, p y ∂ν| ≤ ∫ y, |p y| ∂ν := abs_integral_le_integral_abs
          _ ≤ ∫ _, M ∂ν := integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
              (integrable_const _) (Eventually.of_forall hM)
          _ = M := by simp
      exact (abs_add_le _ _).trans (add_le_add h1 h2)
    · rw [hGp, indicator_of_notMem hz, abs_zero]
      positivity
  have hid := clockResolvent_add_clockResolvent_clockGreen hA hA.hU β hc.le
    (f := fun y => ENNReal.ofReal (p y)) (ENNReal.measurable_ofReal.comp hp) hx
  rw [clockResolvent_congr (f₁ := clockGreen A β fun y => ENNReal.ofReal (p y))
      (f₂ := fun z => ENNReal.ofReal (Gp z)) (fun z hz => by
      rw [(clockGreen_eq_ofReal hA hν hβ hp hp0 hM hz).2, hGp, indicator_of_mem hz]) x,
    (clockGreen_eq_ofReal hA hν hβ hp hp0 hM hx).2,
    clockResolvent_eq_ofReal hA.measurable hβ.le hc hp hp0 hM,
    clockResolvent_eq_ofReal hA.measurable hβ.le hc hGpm hGp0 hGpb,
    ← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_add (resolventReal_nonneg hp0 x)
      (mul_nonneg hc.le (resolventReal_nonneg hGp0 x))] at hid
  exact (ENNReal.ofReal_eq_ofReal_iff (add_nonneg (resolventReal_nonneg hp0 x)
    (mul_nonneg hc.le (resolventReal_nonneg hGp0 x)))
    (clockGreen_eq_ofReal hA hν hβ hp hp0 hM hx).1).1 hid

/-- **The centered identity for `β > 0`**: for bounded measurable `f` of mean zero,
`R^β_c f + c R^β_c (∫ g̃_β(·, y) f(y) ν(dy)) = ∫ g̃_β(·, y) f(y) ν(dy)` on `K₀`. -/
theorem resolventReal_add_resolventReal_discountedGreenPotential (hA : IsUnitSquarePCAF A)
    (hν : IsUpperRegularSpeed (unitSquareRevuzMeasure A)) {β c : ℝ} (hβ : 0 < β) (hc : 0 < c)
    {f : ℂ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M)
    (hf0 : ∫ y, f y ∂unitSquareRevuzMeasure A = 0) {x : ℂ} (hx : x ∈ closedSquare (0 : ℂ) 1) :
    resolventReal A β c f x + c * resolventReal A β c ((closedSquare 0 1).indicator
        (discountedGreenPotential (unitSquareRevuzMeasure A) β f)) x =
      discountedGreenPotential (unitSquareRevuzMeasure A) β f x := by
  set ν := unitSquareRevuzMeasure A with hν_def
  obtain ⟨B, hB0, hB⟩ := hν.exists_potential_bound
  set p : ℂ → ℝ := fun z => max (f z) 0 with hp_def
  set q : ℂ → ℝ := fun z => max (-f z) 0 with hq_def
  have hpm : Measurable p := hf.max measurable_const
  have hqm : Measurable q := hf.neg.max measurable_const
  have hp0 : ∀ z, 0 ≤ p z := fun z => le_max_right _ _
  have hq0 : ∀ z, 0 ≤ q z := fun z => le_max_right _ _
  have hpM : ∀ z, |p z| ≤ M := fun z => by
    rw [abs_of_nonneg (hp0 z)]
    exact max_le ((le_abs_self _).trans (hM z)) ((abs_nonneg _).trans (hM z))
  have hqM : ∀ z, |q z| ≤ M := fun z => by
    rw [abs_of_nonneg (hq0 z)]
    exact max_le ((neg_le_abs _).trans (hM z)) ((abs_nonneg _).trans (hM z))
  have hpq : ∀ z, f z = p z - q z := fun z => by
    simp only [hp_def, hq_def]
    rcases le_total 0 (f z) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hp1 := integrable_of_abs_le (ν := ν) hpm hpM
  have hq1 := integrable_of_abs_le (ν := ν) hqm hqM
  have hmean : ∫ y, p y ∂ν = ∫ y, q y ∂ν := by
    have h : ∫ y, f y ∂ν = ∫ y, p y ∂ν - ∫ y, q y ∂ν := by
      rw [← integral_sub hp1 hq1]
      exact integral_congr_ae (Eventually.of_forall hpq)
    linarith
  have hDsub : ∀ z ∈ closedSquare (0 : ℂ) 1, discountedGreenPotential ν β f z =
      discountedGreenPotential ν β p z - discountedGreenPotential ν β q z := by
    intro z hz
    unfold discountedGreenPotential
    rw [← integral_sub ((hB hpm hpM z hz).1 β hβ.le).1 ((hB hqm hqM z hz).1 β hβ.le).1]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [hpq y]
    ring
  have h1 := resolventReal_add_resolventReal_clockGreen hA hν hβ hc hpm hp0 hpM hx
  have h2 := resolventReal_add_resolventReal_clockGreen hA hν hβ hc hqm hq0 hqM hx
  rw [← hmean] at h2
  have hGb : ∀ (r : ℂ → ℝ), Measurable r → (∀ z, 0 ≤ r z) → (∀ z, |r z| ≤ M) →
      Measurable ((closedSquare 0 1).indicator fun z => discountedGreenPotential ν β r z +
        (∫ y, p y ∂ν) / β) ∧ ∀ z, |(closedSquare 0 1).indicator (fun z =>
          discountedGreenPotential ν β r z + (∫ y, p y ∂ν) / β) z| ≤ M * B + |(∫ y, p y ∂ν) / β| := by
    intro r hr hr0 hrM
    refine ⟨((measurable_discountedGreenPotential β hr).add measurable_const).indicator
      measurableSet_closedSquare_zero_one, fun z => ?_⟩
    by_cases hz : z ∈ closedSquare (0 : ℂ) 1
    · rw [indicator_of_mem hz]
      exact (abs_add_le _ _).trans (add_le_add ((hB hr hrM z hz).1 β hβ.le).2 le_rfl)
    · rw [indicator_of_notMem hz, abs_zero]
      have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
      positivity
  obtain ⟨hGpm, hGpb⟩ := hGb p hpm hp0 hpM
  obtain ⟨hGqm, hGqb⟩ := hGb q hqm hq0 hqM
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hRf : resolventReal A β c f x = resolventReal A β c p x - resolventReal A β c q x := by
    rw [← resolventReal_sub hA.measurable hβ.le hc hpm hqm hpM hqM]
    exact congrArg (fun r => resolventReal A β c r x) (funext hpq)
  have hRG : resolventReal A β c ((closedSquare 0 1).indicator
      (discountedGreenPotential ν β f)) x =
      resolventReal A β c ((closedSquare 0 1).indicator fun z =>
        discountedGreenPotential ν β p z + (∫ y, p y ∂ν) / β) x -
      resolventReal A β c ((closedSquare 0 1).indicator fun z =>
        discountedGreenPotential ν β q z + (∫ y, p y ∂ν) / β) x := by
    rw [← resolventReal_sub hA.measurable hβ.le hc hGpm hGqm hGpb hGqb]
    refine resolventReal_congr (fun z hz => ?_) x
    rw [indicator_of_mem hz, indicator_of_mem hz, indicator_of_mem hz, hDsub z hz]
    ring
  rw [hRf, hRG, hDsub x hx]
  linarith

/-- **The centered resolvent identity**: for bounded measurable `f` of mean zero, `c > 0` and
`x ∈ K₀`, `R_c f(x) + c R_c (V f)(x) = V f(x)`, with `V f(z) = ∫ g(z, y) f(y) ν(dy)` on `K₀`. -/
theorem resolventReal_add_resolventReal_greenPotential (hA : IsUnitSquarePCAF A)
    (hν : IsUpperRegularSpeed (unitSquareRevuzMeasure A)) {c : ℝ} (hc : 0 < c)
    {f : ℂ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ z, |f z| ≤ M)
    (hf0 : ∫ y, f y ∂unitSquareRevuzMeasure A = 0) {x : ℂ} (hx : x ∈ closedSquare (0 : ℂ) 1) :
    resolventReal A 0 c f x + c * resolventReal A 0 c ((closedSquare 0 1).indicator
        (centeredGreenPotential (unitSquareRevuzMeasure A) f)) x =
      centeredGreenPotential (unitSquareRevuzMeasure A) f x := by
  set ν := unitSquareRevuzMeasure A with hν_def
  obtain ⟨B, hB0, hB⟩ := hν.exists_potential_bound
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hid : ∀ n : ℕ, resolventReal A (1 / (n + 1)) c f x + c * resolventReal A (1 / (n + 1)) c
      ((closedSquare 0 1).indicator (discountedGreenPotential ν (1 / (n + 1)) f)) x =
      discountedGreenPotential ν (1 / (n + 1)) f x := fun n =>
    resolventReal_add_resolventReal_discountedGreenPotential hA hν (by positivity) hc hf hM hf0 hx
  have hbd : ∀ (n : ℕ) (z : ℂ), |(closedSquare 0 1).indicator
      (discountedGreenPotential ν (1 / (n + 1)) f) z| ≤ M * B := by
    intro n z
    by_cases hz : z ∈ closedSquare (0 : ℂ) 1
    · rw [indicator_of_mem hz]
      exact ((hB hf hM z hz).1 _ (by positivity)).2
    · rw [indicator_of_notMem hz, abs_zero]
      positivity
  have hl1 := tendsto_resolventReal hA.measurable hc (h := fun _ => f) (fun _ => hf)
    (fun _ => hM) (fun z _ => tendsto_const_nhds) x
  have hl2 := tendsto_resolventReal hA.measurable hc
    (h := fun n => (closedSquare 0 1).indicator (discountedGreenPotential ν (1 / (n + 1)) f))
    (h₀ := (closedSquare 0 1).indicator (centeredGreenPotential ν f))
    (fun n => (measurable_discountedGreenPotential _ hf).indicator
      measurableSet_closedSquare_zero_one) hbd
    (fun z hz => by
      simp only [indicator_of_mem hz]
      exact (hB hf hM z hz).2.2.2) x
  have hl3 := (hB hf hM x hx).2.2.2
  have hlim := hl1.add (hl2.const_mul c)
  exact tendsto_nhds_unique (hlim.congr hid) hl3

end Identity

end HarmonicBalls
