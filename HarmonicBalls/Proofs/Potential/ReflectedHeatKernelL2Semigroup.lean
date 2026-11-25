import HarmonicBalls.Proofs.Potential.HeatKernelL2Operator
import HarmonicBalls.Proofs.Potential.ReflectedHeatKernelChapmanKolmogorov
import HarmonicBalls.FirstPass.Cited.Section2PositivityImproving

/-!
# The transition semigroup of the time change on `L²(ν)`

Let `A` be a positive continuous additive functional of reflected Brownian motion in the unit
square `K₀` (`IsUnitSquarePCAF A`), `ν` a finite measure carried by `K₀` that charges every
relative ball of `K₀` and has no atoms in `K₀`, and `p` a heat kernel of the time change by `A`
with respect to `ν` that is jointly continuous on `(0, ∞) × K₀ × K₀`. The operators
`T_t f(x) = ∫_{K₀} p(t, x, y) f(y) dν(y)` for `t > 0`, and `T_0 = id`
(`heatKernelL2Semigroup ν p`), are the transition operators of the time-changed process on
`L²(ν)` (Fukushima–Oshima–Takeda (2011), Section 6.2). This module proves:

* the semigroup law, from the Chapman–Kolmogorov identity (`IsLBMHeatKernel.chapmanKolmogorov`);
* positivity, the sub-Markov property and, when `p` is symmetric, symmetry and contraction (the
  rows of `p` have mass `1`, so the columns of a symmetric `p` have mass `1`, and Schur's test
  applies);
* strong continuity, when the clock is positive at positive times from `ν`-almost every start: the
  right inverse of the clock tends to `0`, so `T_t g → g` almost everywhere for bounded continuous
  `g`, in `L²(ν)` by dominated convergence, and for every `f ∈ L²(ν)` by density of the bounded
  continuous functions and contraction;
* hence `IsSymmetricMarkovSemigroup ν (heatKernelL2Semigroup ν p)`
  (`isSymmetricMarkovSemigroup_heatKernelL2Semigroup`), the hypothesis of the cited
  Keller–Lenz–Vogt–Wojciechowski Theorem A.2 (`klvwPositivityImprovingCited`);
* and, by that theorem, an irreducible semigroup has a strictly positive kernel
  (`pos_of_isIrreducibleSemigroup`): `p(t, x, y) = ∫ p(t/3, x, z) (T_{t/3} p(t/3, ·, y))(z) dν(z)`
  by the Chapman–Kolmogorov identity, and `T_{t/3}` is positivity improving.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess Metric
open scoped ENNReal NNReal InnerProductSpace BoundedContinuousFunction

namespace HarmonicBalls

open scoped Classical in
/-- The transition semigroup on `L²(ν)` of a kernel `p` on `K₀ = closedSquare 0 1`: the identity at
time `0` and the kernel operator of `p t` at `t > 0`. -/
noncomputable def heatKernelL2Semigroup (ν : Measure ℂ) [IsFiniteMeasure ν] (p : ℝ → ℂ → ℂ → ℝ)
    (t : ℝ≥0) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  if t = 0 then ContinuousLinearMap.id ℝ (Lp ℝ 2 ν) else kernelL2Operator ν (closedSquare 0 1) (p t)

theorem heatKernelL2Semigroup_zero (ν : Measure ℂ) [IsFiniteMeasure ν] (p : ℝ → ℂ → ℂ → ℝ) :
    heatKernelL2Semigroup ν p 0 = ContinuousLinearMap.id ℝ (Lp ℝ 2 ν) := by
  simp [heatKernelL2Semigroup]

theorem heatKernelL2Semigroup_of_ne_zero (ν : Measure ℂ) [IsFiniteMeasure ν]
    (p : ℝ → ℂ → ℂ → ℝ) {t : ℝ≥0} (ht : t ≠ 0) :
    heatKernelL2Semigroup ν p t = kernelL2Operator ν (closedSquare 0 1) (p t) := by
  simp [heatKernelL2Semigroup, ht]

section Kernel

variable {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {ν : Measure ℂ} [IsFiniteMeasure ν]
  {p : ℝ → ℂ → ℂ → ℝ}

omit [IsFiniteMeasure ν] in
/-- The kernel at a positive time is kernel data on `K₀`. -/
theorem isL2KernelData_of_continuousOn (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1)) {t : ℝ} (ht : 0 < t) :
    IsL2KernelData ν (closedSquare 0 1) (p t) :=
  ⟨isCompact_closedSquare 0 1, hνK,
    hpc.comp (by fun_prop : Continuous fun q : ℂ × ℂ => (t, q.1, q.2)).continuousOn
      fun q hq => ⟨ht, hq.1, hq.2⟩⟩

omit [IsFiniteMeasure ν] in
/-- **The rows of a heat kernel have mass one.** -/
theorem IsLBMHeatKernel.setIntegral_eq_one
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1)) {t : ℝ} (ht : 0 < t) {x : ℂ}
    (hx : x ∈ closedSquare 0 1) :
    ∫ y in closedSquare 0 1, p t x y ∂ν = 1 := by
  have hd := isL2KernelData_of_continuousOn hνK hpc ht
  obtain ⟨h0, hS⟩ := hp t ht x hx
  have h := hS univ MeasurableSet.univ
  rw [univ_inter, show {b : ContinuousPath ℂ | liouvilleBrownianPath ((fun _ b t => (A t b : ℝ)) x)
      b t.toNNReal ∈ univ} = univ from eq_univ_of_forall fun b => mem_univ _, measure_univ] at h
  rw [integral_eq_lintegral_of_nonneg_ae, ← h, ENNReal.toReal_one]
  · filter_upwards [ae_restrict_mem hd.measurableSet] with y hy using h0 y hy
  · exact (hd.continuousOn_right hx).aestronglyMeasurable hd.measurableSet

end Kernel

section Semigroup

variable {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {ν : Measure ℂ} [IsFiniteMeasure ν]
  {p : ℝ → ℂ → ℂ → ℝ}

/-- **The semigroup law**, from the Chapman–Kolmogorov identity. -/
theorem heatKernelL2Semigroup_add (hA : IsUnitSquarePCAF A) (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hsupp : ∀ y ∈ closedSquare 0 1, ∀ r : ℝ, 0 < r → 0 < ν (ball y r ∩ closedSquare 0 1))
    (hatom : ∀ x ∈ closedSquare 0 1, ν {x} = 0)
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1)) (s t : ℝ≥0) :
    heatKernelL2Semigroup ν p (s + t) =
      (heatKernelL2Semigroup ν p s).comp (heatKernelL2Semigroup ν p t) := by
  rcases eq_or_ne s 0 with rfl | hs
  · rw [zero_add, heatKernelL2Semigroup_zero, ContinuousLinearMap.id_comp]
  rcases eq_or_ne t 0 with rfl | ht
  · rw [add_zero, heatKernelL2Semigroup_zero, ContinuousLinearMap.comp_id]
  have hs' : (0 : ℝ) < s := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hs)
  have ht' : (0 : ℝ) < t := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ht)
  rw [heatKernelL2Semigroup_of_ne_zero _ _ (add_pos (pos_iff_ne_zero.2 hs)
    (pos_iff_ne_zero.2 ht)).ne', heatKernelL2Semigroup_of_ne_zero _ _ hs,
    heatKernelL2Semigroup_of_ne_zero _ _ ht, NNReal.coe_add]
  exact (isL2KernelData_of_continuousOn hνK hpc hs').kernelL2Operator_eq_comp
    (isL2KernelData_of_continuousOn hνK hpc ht') (isL2KernelData_of_continuousOn hνK hpc
      (add_pos hs' ht')) fun x hx y hy => hp.chapmanKolmogorov hA hsupp hatom hpc hs' ht' hx hy

/-- **Symmetry** of the transition operators of a symmetric kernel. -/
theorem heatKernelL2Semigroup_inner_comm (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1))
    (hsym : ∀ t : ℝ, 0 < t → ∀ x ∈ closedSquare 0 1, ∀ y ∈ closedSquare 0 1, p t x y = p t y x)
    (t : ℝ≥0) (f g : Lp ℝ 2 ν) :
    ⟪heatKernelL2Semigroup ν p t f, g⟫_ℝ = ⟪f, heatKernelL2Semigroup ν p t g⟫_ℝ := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [heatKernelL2Semigroup_zero]
  have ht' : (0 : ℝ) < t := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ht)
  rw [heatKernelL2Semigroup_of_ne_zero _ _ ht]
  exact (isL2KernelData_of_continuousOn hνK hpc ht').inner_kernelL2Operator_comm (hsym t ht') f g

/-- **Contraction**: a symmetric heat kernel has rows and columns of mass one. -/
theorem norm_heatKernelL2Semigroup_apply_le
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1))
    (hsym : ∀ t : ℝ, 0 < t → ∀ x ∈ closedSquare 0 1, ∀ y ∈ closedSquare 0 1, p t x y = p t y x)
    (t : ℝ≥0) (f : Lp ℝ 2 ν) : ‖heatKernelL2Semigroup ν p t f‖ ≤ ‖f‖ := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [heatKernelL2Semigroup_zero]
  have ht' : (0 : ℝ) < t := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ht)
  have hd := isL2KernelData_of_continuousOn hνK hpc ht'
  rw [heatKernelL2Semigroup_of_ne_zero _ _ ht]
  refine (hd.norm_kernelL2Operator_apply_le zero_le_one (fun x hx => le_of_eq ?_)
    (fun y hy => le_of_eq ?_) f).trans_eq (one_mul _)
  · exact (setIntegral_congr_fun hd.measurableSet fun y hy =>
      abs_of_nonneg ((hp t ht' x hx).1 y hy)).trans (hp.setIntegral_eq_one hνK hpc ht' hx)
  · refine (setIntegral_congr_fun hd.measurableSet fun x hx => ?_).trans
      (hp.setIntegral_eq_one hνK hpc ht' hy)
    show |p t x y| = p t y x
    rw [abs_of_nonneg ((hp t ht' x hx).1 y hy), hsym t ht' x hx y hy]

theorem ae_nonneg_heatKernelL2Semigroup
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1))
    (t : ℝ≥0) (f : Lp ℝ 2 ν) (hf : 0 ≤ᵐ[ν] (f : ℂ → ℝ)) :
    0 ≤ᵐ[ν] (heatKernelL2Semigroup ν p t f : ℂ → ℝ) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simpa [heatKernelL2Semigroup_zero] using hf
  have ht' : (0 : ℝ) < t := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ht)
  rw [heatKernelL2Semigroup_of_ne_zero _ _ ht]
  exact (isL2KernelData_of_continuousOn hνK hpc ht').ae_nonneg_kernelL2Operator
    (fun x hx y hy => (hp t ht' x hx).1 y hy) hf

theorem ae_heatKernelL2Semigroup_le_one
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1))
    (t : ℝ≥0) (f : Lp ℝ 2 ν) (hf : ∀ᵐ x ∂ν, 0 ≤ (f : ℂ → ℝ) x ∧ (f : ℂ → ℝ) x ≤ 1) :
    ∀ᵐ x ∂ν, (heatKernelL2Semigroup ν p t f : ℂ → ℝ) x ≤ 1 := by
  rcases eq_or_ne t 0 with rfl | ht
  · simpa [heatKernelL2Semigroup_zero] using hf.mono fun x hx => hx.2
  have ht' : (0 : ℝ) < t := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ht)
  rw [heatKernelL2Semigroup_of_ne_zero _ _ ht]
  exact (isL2KernelData_of_continuousOn hνK hpc ht').ae_kernelL2Operator_le_one
    (fun x hx y hy => (hp t ht' x hx).1 y hy)
    (fun x hx => (hp.setIntegral_eq_one hνK hpc ht' hx).le) hf

/-! ### Strong continuity -/

/-- The right inverse of a clock positive at positive times tends to `0` at level `0`. -/
theorem tendsto_pcafClockInverse_zero {b : ContinuousPath ℂ}
    (hpos : ∀ u : ℝ≥0, 0 < u → 0 < A u b) :
    Tendsto (fun t => pcafClockInverse A t b) (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => absurd ha (not_lt.2 zero_le), fun ε hε => ?_⟩
  have h2 := hpos (ε / 2) (half_pos hε)
  filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds h2)] with t ht
  calc pcafClockInverse A t b ≤ ε / 2 :=
        csInf_le (OrderBot.bddBelow _) (show ε / 2 ∈ {s | t < A s b} from ht)
    _ < ε := half_lt_self hε

/-- From a start at which the clock is positive at positive times, the expectations of a bounded
continuous function of the time-changed position converge to its value at the start. -/
theorem tendsto_integral_timeChangeRegularized (hA : IsUnitSquarePCAF A) {x : ℂ}
    (hx : x ∈ closedSquare 0 1)
    (hstart : ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x, ∀ u : ℝ≥0, 0 < u → 0 < A u b)
    (g : ℂ →ᵇ ℝ) :
    Tendsto (fun t : ℝ≥0 => ∫ b, g (unitSquareTimeChangeRegularized A t b)
      ∂reflectedPlanarBrownianMotion 0 1 x) (𝓝[>] 0) (𝓝 (g x)) := by
  have hlim : ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x,
      Tendsto (fun t : ℝ≥0 => g (unitSquareTimeChangeRegularized A t b)) (𝓝[>] 0) (𝓝 (g x)) := by
    filter_upwards [hstart, ae_reflected_eval_zero hx,
      ae_eval_pcafClockInverse_eq_regularized hA hx] with b hb h0 heq
    have h1 : Tendsto (fun t => b (pcafClockInverse A t b)) (𝓝[>] 0) (𝓝 x) := by
      rw [← h0]
      exact (b.continuous.tendsto 0).comp (tendsto_pcafClockInverse_zero hb)
    refine ((g.continuous.tendsto x).comp h1).congr fun t => ?_
    simp only [Function.comp_apply, heq t]
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ => ‖g‖)
    (Eventually.of_forall fun t => (g.continuous.measurable.comp
      (measurable_unitSquareTimeChangeRegularized hA.measurable t)).aestronglyMeasurable)
    (Eventually.of_forall fun t => Eventually.of_forall fun b => g.norm_coe_le_norm _)
    (integrable_const _) hlim
  simpa using h

omit [IsFiniteMeasure ν] in
/-- The kernel operator applied to a bounded continuous function is the expectation of the
function at the time-changed position. -/
theorem kernelTransform_eq_integral_timeChangeRegularized (hA : IsUnitSquarePCAF A)
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1)) {t : ℝ≥0} (ht : 0 < t) {x : ℂ}
    (hx : x ∈ closedSquare 0 1) (g : ℂ →ᵇ ℝ) :
    kernelTransform ν (closedSquare 0 1) (p t) g x =
      ∫ b, g (unitSquareTimeChangeRegularized A t b) ∂reflectedPlanarBrownianMotion 0 1 x := by
  have ht' : (0 : ℝ) < t := NNReal.coe_pos.2 ht
  have hd := isL2KernelData_of_continuousOn hνK hpc ht'
  have hRm := measurable_unitSquareTimeChangeRegularized hA.measurable t
  have hlaw : (reflectedPlanarBrownianMotion 0 1 x).map (unitSquareTimeChangeRegularized A t) =
      (ν.restrict (closedSquare 0 1)).withDensity fun w => ((p t x w).toNNReal : ℝ≥0∞) := by
    ext S hS
    rw [Measure.map_apply hRm hS, withDensity_apply _ hS, Measure.restrict_restrict hS]
    have h := hp.reflected_regularized_preimage hA hx ht' hS
    rw [Real.toNNReal_coe] at h
    rw [h]
    rfl
  rw [← integral_map hRm.aemeasurable g.continuous.aestronglyMeasurable, hlaw,
    integral_withDensity_eq_integral_smul₀
      ((hd.continuousOn_right hx).aemeasurable hd.measurableSet).real_toNNReal]
  unfold kernelTransform
  refine setIntegral_congr_fun hd.measurableSet fun y hy => ?_
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ ((hp t ht' x hx).1 y hy)]

end Semigroup

section Continuity

variable {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {ν : Measure ℂ} [IsFiniteMeasure ν]
  {p : ℝ → ℂ → ℂ → ℝ}

omit [IsFiniteMeasure ν] in
/-- The kernel operator applied to a bounded continuous function `g` is bounded by `‖g‖` on
`K₀`. -/
theorem abs_kernelTransform_le_norm (hA : IsUnitSquarePCAF A)
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1)) {t : ℝ≥0} (ht : 0 < t) {x : ℂ}
    (hx : x ∈ closedSquare 0 1) (g : ℂ →ᵇ ℝ) :
    |kernelTransform ν (closedSquare 0 1) (p t) g x| ≤ ‖g‖ := by
  rw [kernelTransform_eq_integral_timeChangeRegularized hA hp hνK hpc ht hx g,
    ← Real.norm_eq_abs]
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
    norm_integral_le_of_norm_le_const (μ := reflectedPlanarBrownianMotion 0 1 x)
      (Eventually.of_forall fun b => g.norm_coe_le_norm (unitSquareTimeChangeRegularized A t b))

omit [IsFiniteMeasure ν] in
/-- For `ν`-almost every start, `T_t g → g` as `t ↓ 0`, for bounded continuous `g`. -/
theorem ae_tendsto_kernelTransform (hA : IsUnitSquarePCAF A)
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1))
    (hstart : ∀ᵐ x ∂ν, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x, ∀ u : ℝ≥0, 0 < u → 0 < A u b)
    (g : ℂ →ᵇ ℝ) :
    ∀ᵐ x ∂ν, Tendsto (fun t : ℝ≥0 => kernelTransform ν (closedSquare 0 1) (p t) g x) (𝓝[>] 0)
      (𝓝 (g x)) := by
  have hmem : ∀ᵐ x ∂ν, x ∈ closedSquare 0 1 := by
    rw [ae_iff]
    exact hνK
  filter_upwards [hstart, hmem] with x hx hxK
  refine (tendsto_integral_timeChangeRegularized hA hxK hx g).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (kernelTransform_eq_integral_timeChangeRegularized hA hp hνK hpc ht hxK g).symm

/-- **Strong continuity at `0` on bounded continuous functions.** -/
theorem tendsto_norm_heatKernelL2Semigroup_toLp_sub (hA : IsUnitSquarePCAF A)
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1))
    (hstart : ∀ᵐ x ∂ν, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x, ∀ u : ℝ≥0, 0 < u → 0 < A u b)
    (g : ℂ →ᵇ ℝ) :
    Tendsto (fun t => ‖heatKernelL2Semigroup ν p t (BoundedContinuousFunction.toLp (E := ℝ) 2 ν ℝ g) -
      BoundedContinuousFunction.toLp (E := ℝ) 2 ν ℝ g‖) (𝓝[>] 0) (𝓝 0) := by
  set G := BoundedContinuousFunction.toLp (E := ℝ) 2 ν ℝ g with hG
  have hGc : (G : ℂ → ℝ) =ᵐ[ν] g := BoundedContinuousFunction.coeFn_toLp (p := 2) (μ := ν) (𝕜 := ℝ) g
  have hmem : ∀ᵐ x ∂ν, x ∈ closedSquare 0 1 := by
    rw [ae_iff]
    exact hνK
  have hgi : Integrable (g : ℂ → ℝ) (ν.restrict (closedSquare 0 1)) := g.integrable (ν.restrict (closedSquare 0 1))
  have hsq : Tendsto (fun t : ℝ≥0 =>
      ∫ x, (kernelTransform ν (closedSquare 0 1) (p t) g x - g x) ^ 2 ∂ν) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (fun _ => (2 * ‖g‖) ^ 2)
      (F := fun (t : ℝ≥0) x => (kernelTransform ν (closedSquare 0 1) (p t) g x - g x) ^ 2)
      (f := fun _ => 0) (l := 𝓝[>] (0 : ℝ≥0)) (μ := ν) ?_ ?_ (integrable_const _) ?_
    · simpa using h
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (((isL2KernelData_of_continuousOn hνK hpc (NNReal.coe_pos.2 ht)).aestronglyMeasurable_kernelTransform
        hgi).sub g.continuous.aestronglyMeasurable).pow 2
    · filter_upwards [self_mem_nhdsWithin] with t ht
      filter_upwards [hmem] with x hx
      rw [Real.norm_eq_abs, abs_pow]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      calc |kernelTransform ν (closedSquare 0 1) (p t) g x - g x|
          ≤ |kernelTransform ν (closedSquare 0 1) (p t) g x| + |g x| := abs_sub _ _
        _ ≤ ‖g‖ + ‖g‖ := add_le_add (abs_kernelTransform_le_norm hA hp hνK hpc ht hx g)
            (by rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm x)
        _ = 2 * ‖g‖ := by ring
    · filter_upwards [ae_tendsto_kernelTransform hA hp hνK hpc hstart g] with x hx
      simpa using (hx.sub_const (g x)).pow 2
  have heq : ∀ t : ℝ≥0, 0 < t → ‖heatKernelL2Semigroup ν p t G - G‖ =
      Real.sqrt (∫ x, (kernelTransform ν (closedSquare 0 1) (p t) g x - g x) ^ 2 ∂ν) := by
    intro t ht
    rw [← Real.sqrt_sq (norm_nonneg _), l2_norm_sq_eq_integral_sq]
    congr 1
    have hd := isL2KernelData_of_continuousOn hνK hpc (NNReal.coe_pos.2 ht)
    refine integral_congr_ae ?_
    rw [heatKernelL2Semigroup_of_ne_zero _ _ ht.ne']
    filter_upwards [Lp.coeFn_sub (kernelL2Operator ν (closedSquare 0 1) (p t) G) G,
      hd.coeFn_kernelL2Operator G, hGc] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, kernelTransform_congr_ae hGc]
  have h2 := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (heq t ht).symm

/-- **Strong continuity at `0`.** -/
theorem tendsto_heatKernelL2Semigroup_zero (hA : IsUnitSquarePCAF A)
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1))
    (hsym : ∀ t : ℝ, 0 < t → ∀ x ∈ closedSquare 0 1, ∀ y ∈ closedSquare 0 1, p t x y = p t y x)
    (hstart : ∀ᵐ x ∂ν, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x, ∀ u : ℝ≥0, 0 < u → 0 < A u b)
    (f : Lp ℝ 2 ν) : Tendsto (fun t => heatKernelL2Semigroup ν p t f) (𝓝 0) (𝓝 f) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨g, hg⟩ := Metric.denseRange_iff.1
    (BoundedContinuousFunction.toLp_denseRange (E := ℝ) (μ := ν) (𝕜 := ℝ) (p := 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)) f (ε / 3) hε3
  set G := BoundedContinuousFunction.toLp (E := ℝ) 2 ν ℝ g with hG
  have hev := (Metric.tendsto_nhds.1
    (tendsto_norm_heatKernelL2Semigroup_toLp_sub hA hp hνK hpc hstart g)) (ε / 3) hε3
  rw [eventually_nhdsWithin_iff] at hev
  filter_upwards [hev] with t ht
  rcases eq_or_ne t 0 with rfl | ht0
  · rw [heatKernelL2Semigroup_zero, ContinuousLinearMap.id_apply, dist_self]
    exact hε
  have h1 := ht (pos_iff_ne_zero.2 ht0)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at h1
  have hc := norm_heatKernelL2Semigroup_apply_le hp hνK hpc hsym t (f - G)
  rw [dist_eq_norm] at hg ⊢
  calc ‖heatKernelL2Semigroup ν p t f - f‖
      = ‖heatKernelL2Semigroup ν p t (f - G) + (heatKernelL2Semigroup ν p t G - G) + (G - f)‖ := by
        rw [map_sub]
        congr 1
        abel
    _ ≤ ‖heatKernelL2Semigroup ν p t (f - G)‖ + ‖heatKernelL2Semigroup ν p t G - G‖ + ‖G - f‖ :=
        norm_add₃_le
    _ < ε := by
        rw [norm_sub_rev G f]
        linarith

/-- **Strong continuity.** -/
theorem continuous_heatKernelL2Semigroup (hA : IsUnitSquarePCAF A)
    (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hsupp : ∀ y ∈ closedSquare 0 1, ∀ r : ℝ, 0 < r → 0 < ν (ball y r ∩ closedSquare 0 1))
    (hatom : ∀ x ∈ closedSquare 0 1, ν {x} = 0)
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1))
    (hsym : ∀ t : ℝ, 0 < t → ∀ x ∈ closedSquare 0 1, ∀ y ∈ closedSquare 0 1, p t x y = p t y x)
    (hstart : ∀ᵐ x ∂ν, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x, ∀ u : ℝ≥0, 0 < u → 0 < A u b)
    (f : Lp ℝ 2 ν) : Continuous fun t => heatKernelL2Semigroup ν p t f := by
  have hadd := heatKernelL2Semigroup_add hA hνK hsupp hatom hp hpc
  have hle := norm_heatKernelL2Semigroup_apply_le hp hνK hpc hsym
  have h0 := tendsto_heatKernelL2Semigroup_zero hA hp hνK hpc hsym hstart f
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hev := Metric.tendsto_nhds.1 h0 ε hε
  have hsub1 : Tendsto (fun s : ℝ≥0 => s - t₀) (𝓝 t₀) (𝓝 0) := by
    have h : Tendsto (fun s : ℝ≥0 => s - t₀) (𝓝 t₀) (𝓝 (t₀ - t₀)) :=
      (continuous_id.sub continuous_const).tendsto t₀
    rwa [tsub_self] at h
  have hsub2 : Tendsto (fun s : ℝ≥0 => t₀ - s) (𝓝 t₀) (𝓝 0) := by
    have h : Tendsto (fun s : ℝ≥0 => t₀ - s) (𝓝 t₀) (𝓝 (t₀ - t₀)) :=
      (continuous_const.sub continuous_id).tendsto t₀
    rwa [tsub_self] at h
  filter_upwards [hsub1 hev, hsub2 hev] with s h1 h2
  rcases le_total t₀ s with hts | hst
  · have hs : s = t₀ + (s - t₀) := (add_tsub_cancel_of_le hts).symm
    rw [hs, hadd, ContinuousLinearMap.comp_apply, dist_eq_norm, ← map_sub]
    exact (hle t₀ _).trans_lt (by rw [← dist_eq_norm]; exact h1)
  · have ht : t₀ = s + (t₀ - s) := (add_tsub_cancel_of_le hst).symm
    rw [ht, hadd, ContinuousLinearMap.comp_apply, dist_eq_norm, ← map_sub]
    refine (hle s _).trans_lt ?_
    rw [← dist_eq_norm, dist_comm]
    exact h2

/-- **The transition operators of the time change form a strongly continuous semigroup of
symmetric sub-Markov contractions on `L²(ν)`** when the kernel is symmetric and the clock is
positive at positive times from `ν`-almost every start. -/
theorem isSymmetricMarkovSemigroup_heatKernelL2Semigroup (hA : IsUnitSquarePCAF A)
    (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hsupp : ∀ y ∈ closedSquare 0 1, ∀ r : ℝ, 0 < r → 0 < ν (ball y r ∩ closedSquare 0 1))
    (hatom : ∀ x ∈ closedSquare 0 1, ν {x} = 0)
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1))
    (hsym : ∀ t : ℝ, 0 < t → ∀ x ∈ closedSquare 0 1, ∀ y ∈ closedSquare 0 1, p t x y = p t y x)
    (hstart : ∀ᵐ x ∂ν, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x, ∀ u : ℝ≥0, 0 < u → 0 < A u b) :
    IsSymmetricMarkovSemigroup ν (heatKernelL2Semigroup ν p) where
  map_zero := heatKernelL2Semigroup_zero ν p
  map_add := heatKernelL2Semigroup_add hA hνK hsupp hatom hp hpc
  continuous := continuous_heatKernelL2Semigroup hA hνK hsupp hatom hp hpc hsym hstart
  symm := heatKernelL2Semigroup_inner_comm hνK hpc hsym
  norm_le := norm_heatKernelL2Semigroup_apply_le hp hνK hpc hsym
  nonneg := ae_nonneg_heatKernelL2Semigroup hp hνK hpc
  le_one := ae_heatKernelL2Semigroup_le_one hp hνK hpc

end Continuity

section Positivity

variable {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {ν : Measure ℂ} [IsFiniteMeasure ν]
  {p : ℝ → ℂ → ℂ → ℝ}

/-- **An irreducible transition semigroup has a strictly positive kernel.** Under the hypotheses of
`isSymmetricMarkovSemigroup_heatKernelL2Semigroup`, if the semigroup is irreducible
(`IsIrreducibleSemigroup`, [KLVW] Definition A.1), the cited [KLVW] Theorem A.2 makes `T_{t/3}`
positivity improving, and `p(t, x, y) = ∫ p(t/3, x, z) (T_{t/3} p(t/3, ·, y))(z) dν(z) > 0` by the
Chapman–Kolmogorov identity. -/
theorem pos_of_isIrreducibleSemigroup (hKLVW : klvwPositivityImprovingCited)
    (hA : IsUnitSquarePCAF A) (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hsupp : ∀ y ∈ closedSquare 0 1, ∀ r : ℝ, 0 < r → 0 < ν (ball y r ∩ closedSquare 0 1))
    (hatom : ∀ x ∈ closedSquare 0 1, ν {x} = 0)
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1))
    (hsym : ∀ t : ℝ, 0 < t → ∀ x ∈ closedSquare 0 1, ∀ y ∈ closedSquare 0 1, p t x y = p t y x)
    (hstart : ∀ᵐ x ∂ν, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x, ∀ u : ℝ≥0, 0 < u → 0 < A u b)
    (hI : IsIrreducibleSemigroup ν (heatKernelL2Semigroup ν p)) {t : ℝ} (ht : 0 < t) {x₀ : ℂ}
    (hx₀ : x₀ ∈ closedSquare 0 1) {y₀ : ℂ} (hy₀ : y₀ ∈ closedSquare 0 1) : 0 < p t x₀ y₀ := by
  have hsm := isSymmetricMarkovSemigroup_heatKernelL2Semigroup hA hνK hsupp hatom hp hpc hsym
    hstart
  have hPI := (hKLVW ℂ ν (heatKernelL2Semigroup ν p) hsm).1.1 hI
  set τ : ℝ := t / 3 with hτ_def
  have hτ : 0 < τ := by positivity
  have hτ' : 0 < τ.toNNReal := Real.toNNReal_pos.2 hτ
  have hττ : ((τ.toNNReal : ℝ≥0) : ℝ) = τ := Real.coe_toNNReal _ hτ.le
  have hd := isL2KernelData_of_continuousOn hνK hpc hτ
  have hKm := hd.measurableSet
  -- the column `w ↦ p(τ, w, y₀)` as an element of `L²(ν)`
  have hhc : ContinuousOn (fun w => p τ w y₀) (closedSquare 0 1) := hd.continuousOn_left hy₀
  obtain ⟨C, -, hC⟩ := hd.exists_bound
  have hhm : MemLp (fun w => p τ w y₀) 2 ν := by
    refine MemLp.of_bound ?_ C ?_
    · have h := hhc.aestronglyMeasurable (μ := ν) hKm
      rwa [hd.restrict_eq] at h
    · filter_upwards [hd.ae_mem] with w hw
      rw [Real.norm_eq_abs]
      exact hC w hw y₀ hy₀
  set H := hhm.toLp _ with hH_def
  have hHc : (H : ℂ → ℝ) =ᵐ[ν] fun w => p τ w y₀ := hhm.coeFn_toLp
  have hH0 : 0 ≤ᵐ[ν] (H : ℂ → ℝ) := by
    filter_upwards [hHc, hd.ae_mem] with w h1 hw
    rw [h1]
    exact (hp τ hτ w hw).1 y₀ hy₀
  have hmass : ∫ w in closedSquare 0 1, p τ w y₀ ∂ν = 1 :=
    (setIntegral_congr_fun hKm fun w hw => hsym τ hτ w hw y₀ hy₀).trans
      (hp.setIntegral_eq_one hνK hpc hτ hy₀)
  have hHH : 0 < ⟪H, H⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq]
    refine pow_pos (norm_pos_iff.2 fun h0 => ?_) 2
    have h1 : (fun w => p τ w y₀) =ᵐ[ν] 0 := by
      have h2 := Lp.coeFn_zero (E := ℝ) (p := 2) (μ := ν)
      rw [← h0] at h2
      exact hHc.symm.trans h2
    have h3 : ∫ w in closedSquare 0 1, p τ w y₀ ∂ν = 0 := by
      rw [integral_congr_ae (ae_restrict_of_ae h1)]
      simp
    rw [hmass] at h3
    exact one_ne_zero h3
  have hpos := hPI τ.toNNReal hτ' H hH0 hHH
  -- `T_τ H = p(2τ, ·, y₀)` on `K₀`
  have hT : ∀ᵐ z ∂ν, z ∈ closedSquare 0 1 →
      (heatKernelL2Semigroup ν p τ.toNNReal H : ℂ → ℝ) z = p (τ + τ) z y₀ := by
    rw [heatKernelL2Semigroup_of_ne_zero _ _ hτ'.ne', hττ]
    filter_upwards [hd.coeFn_kernelL2Operator H] with z h1 hz
    rw [h1, kernelTransform_congr_ae hHc, hp.chapmanKolmogorov hA hsupp hatom hpc hτ hτ hz hy₀]
    rfl
  have ht3 : t = τ + (τ + τ) := by
    rw [hτ_def]
    ring
  rw [ht3, hp.chapmanKolmogorov hA hsupp hatom hpc hτ (add_pos hτ hτ) hx₀ hy₀]
  have hd2 := isL2KernelData_of_continuousOn hνK hpc (add_pos hτ hτ)
  have hint : Integrable (fun z => p τ x₀ z * p (τ + τ) z y₀) (ν.restrict (closedSquare 0 1)) :=
    hd.integrable_mul hx₀ ((hd2.continuousOn_left hy₀).integrableOn_compact
      (isCompact_closedSquare 0 1))
  have hnn : 0 ≤ᵐ[ν.restrict (closedSquare 0 1)] fun z => p τ x₀ z * p (τ + τ) z y₀ := by
    filter_upwards [ae_restrict_mem hKm] with z hz
    exact mul_nonneg ((hp τ hτ x₀ hx₀).1 z hz) ((hp (τ + τ) (add_pos hτ hτ) z hz).1 y₀ hy₀)
  rw [integral_pos_iff_support_of_nonneg_ae hnn hint]
  have hg0 : 0 ≤ᵐ[ν.restrict (closedSquare 0 1)] fun z => p τ x₀ z := by
    filter_upwards [ae_restrict_mem hKm] with z hz
    exact (hp τ hτ x₀ hx₀).1 z hz
  have hgsupp : 0 < ν.restrict (closedSquare 0 1) (Function.support fun z => p τ x₀ z) := by
    rw [← integral_pos_iff_support_of_nonneg_ae hg0 (hd.integrable_right hx₀),
      hp.setIntegral_eq_one hνK hpc hτ hx₀]
    exact one_pos
  refine hgsupp.trans_le (measure_mono_ae ?_)
  filter_upwards [ae_restrict_of_ae hpos, ae_restrict_of_ae hT, ae_restrict_mem hKm]
    with z h1 h2 hz hzs
  rw [h2 hz] at h1
  exact mul_ne_zero hzs h1.ne'

end Positivity

end HarmonicBalls
