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

/-- The kernel at a positive time is kernel data on `K₀`. -/
theorem isL2KernelData_of_continuousOn (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1)) {t : ℝ} (ht : 0 < t) :
    IsL2KernelData ν (closedSquare 0 1) (p t) :=
  ⟨isCompact_closedSquare 0 1, hνK,
    hpc.comp (by fun_prop : Continuous fun q : ℂ × ℂ => (t, q.1, q.2)).continuousOn
      fun q hq => ⟨ht, hq.1, hq.2⟩⟩

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

end HarmonicBalls
