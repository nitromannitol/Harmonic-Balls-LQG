import HarmonicBalls.Proofs.Potential.ReflectedTimeChangeSemigroup
import HarmonicBalls.Proofs.Potential.ReflectedHeatKernelUniqueness

/-!
# The Chapman–Kolmogorov identity for continuous heat kernels of a time change

Let `A` be a positive continuous additive functional of reflected Brownian motion in the unit
square `K₀` (`IsUnitSquarePCAF A`), `ν` a finite measure that charges every relative ball of `K₀`
and has no atoms in `K₀`, and `p` a heat kernel of the time change by `A` with respect to `ν`
(`IsLBMHeatKernel`) that is jointly continuous on `(0, ∞) × K₀ × K₀`. Then:

* the clock is almost surely unbounded from every start `x ∈ K₀`
  (`ae_tendsto_atTop_of_isLBMHeatKernel`): on `{A_∞ ≤ t}` the right inverse `τ_t` is `0`, so the
  time-changed point at time `t` is the start `x`, an event of probability
  `∫_{{x}} p(t, x, ·) dν = 0`;
* the Chapman–Kolmogorov identity holds everywhere (`IsLBMHeatKernel.chapmanKolmogorov`):
  `p(s + t, x, y) = ∫_{K₀} p(s, x, z) p(t, z, y) dν(z)` for `s, t > 0` and `x, y ∈ K₀`.

The identity holds `ν`-almost everywhere in `y` by the semigroup property of the time change
(`reflected_eval_pcafClockInverse_add_mem`; Fukushima–Oshima–Takeda (2011), Section 6.2) and
Tonelli's theorem, and then everywhere by continuity and full support
(`eqOn_of_forall_setLIntegral_eq`). [Kig19, Theorem 13.1] (J. Kigami, Mem. Amer. Math. Soc.
259(1250), 2019) gives the jointly continuous kernel but does not state the semigroup identity; the
passage from almost every `y` to every `y` uses only the continuity of the kernel on `K₀` and the
full support of `ν`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess Metric
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- Reflected Brownian motion in the unit square started in `K₀` starts at its start. -/
theorem ae_reflected_eval_zero {x : ℂ} (hx : x ∈ closedSquare 0 1) :
    ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x, b 0 = x := by
  have hclosed : IsClosed {b : ContinuousPath ℂ | b 0 = x} :=
    isClosed_eq (continuous_eval_const 0) continuous_const
  rw [reflectedPlanarBrownianMotion, Kernel.map_apply _ (measurable_comp_squareFoldCM 0 1),
    ae_map_iff (measurable_comp_squareFoldCM 0 1).aemeasurable hclosed.measurableSet]
  filter_upwards [ae_planarBrownianMotion_eval_zero x] with ω hω
  show squareFold 0 1 (ω 0) = x
  rw [hω, squareFold_of_mem 0 one_pos hx]

/-- The time-changed point `liouvilleBrownianPath` of the clock `t ↦ A t b` is `b (τ_u b)`. -/
theorem liouvilleBrownianPath_coe_eq (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0)
    (b : ContinuousPath ℂ) (u : ℝ≥0) :
    liouvilleBrownianPath (fun b t => (A t b : ℝ)) b u = b (pcafClockInverse A u b) := by
  show b (clockInverse (fun t => (A t b : ℝ)) u) = _
  rw [clockInverse_coe_eq_pcafClockInverse]

/-- A heat kernel of the time change, in terms of the regularized time-changed position. -/
theorem IsLBMHeatKernel.reflected_regularized_preimage {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {ν : Measure ℂ} {p : ℝ → ℂ → ℂ → ℝ}
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    {z : ℂ} (hz : z ∈ closedSquare 0 1) {τ : ℝ} (hτ : 0 < τ) {S : Set ℂ} (hS : MeasurableSet S) :
    reflectedPlanarBrownianMotion 0 1 z (unitSquareTimeChangeRegularized A τ.toNNReal ⁻¹' S) =
      ∫⁻ w in S ∩ closedSquare 0 1, ENNReal.ofReal (p τ z w) ∂ν := by
  rw [← reflected_eval_pcafClockInverse_mem hA hz, ← (hp τ hτ z hz).2 S hS]
  congr 1

/-- **The clock of a time change with a heat kernel is unbounded.** If the time change of
reflected Brownian motion by `A` has a heat kernel with respect to `ν` and `ν {x} = 0`, the clock
tends to `∞` almost surely from `x ∈ K₀`: on `{A_∞ ≤ t}`, `τ_t = 0` and the time-changed point at
time `t` is the start. -/
theorem ae_tendsto_atTop_of_isLBMHeatKernel {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {ν : Measure ℂ} {p : ℝ → ℂ → ℂ → ℝ}
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    {x : ℂ} (hx : x ∈ closedSquare 0 1) (hνx : ν {x} = 0) :
    ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x, Tendsto (fun t => A t b) atTop atTop := by
  have hbound : ∀ n : ℕ, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x,
      ∃ s, ((n : ℝ≥0) + 1) < A s b := by
    intro n
    have hτ : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h := (hp ((n : ℝ) + 1) hτ x hx).2 {x} (measurableSet_singleton x)
    have h0 : ∫⁻ y in {x} ∩ closedSquare 0 1, ENNReal.ofReal (p ((n : ℝ) + 1) x y) ∂ν = 0 :=
      setLIntegral_measure_zero _ _ (measure_mono_null inter_subset_left hνx)
    rw [h0] at h
    have hr : ((n : ℝ) + 1).toNNReal = (n : ℝ≥0) + 1 := by
      apply NNReal.eq
      rw [Real.coe_toNNReal _ hτ.le]
      simp
    rw [ae_iff]
    refine measure_mono_null (fun b hb => ?_) (measure_union_null h (ae_iff.1
      (ae_reflected_eval_zero hx)))
    by_cases h0b : b 0 = x
    · left
      have hle : ∀ s, A s b ≤ (n : ℝ≥0) + 1 := fun s => not_lt.1 fun hs => hb ⟨s, hs⟩
      have hempty : {s | (n : ℝ≥0) + 1 < A s b} = ∅ :=
        eq_empty_of_forall_notMem fun s hs => absurd hs (not_lt.2 (hle s))
      show liouvilleBrownianPath (fun b t => (A t b : ℝ)) b ((n : ℝ) + 1).toNNReal ∈ ({x} : Set ℂ)
      rw [liouvilleBrownianPath_coe_eq, hr]
      unfold pcafClockInverse
      rw [hempty, NNReal.sInf_empty, h0b]
      exact mem_singleton x
    · right
      exact h0b
  filter_upwards [ae_all_iff.2 hbound, hA.path x hx] with b hb hpath
  refine tendsto_atTop_atTop_of_monotone hpath.2.2 fun c => ?_
  obtain ⟨n, hn⟩ := exists_nat_ge c
  obtain ⟨s, hs⟩ := hb n
  exact ⟨s, hn.trans (le_self_add.trans hs.le)⟩

/-- **The Chapman–Kolmogorov identity, integrated form.** For `x ∈ K₀` with an unbounded clock,
`s, t > 0` and Borel `S`,
`∫_{S ∩ K₀} p(s + t, x, ·) dν = ∫_{S ∩ K₀} (∫_{K₀} p(s, x, z) p(t, z, ·) dν(z)) dν`. -/
theorem IsLBMHeatKernel.setLIntegral_add {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {ν : Measure ℂ} [IsFiniteMeasure ν] {p : ℝ → ℂ → ℂ → ℝ}
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1))
    {x : ℂ} (hx : x ∈ closedSquare 0 1)
    (hU : ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x, Tendsto (fun t => A t b) atTop atTop)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {S : Set ℂ} (hS : MeasurableSet S) :
    ∫⁻ w in S ∩ closedSquare 0 1, ENNReal.ofReal (p (s + t) x w) ∂ν =
      ∫⁻ w in S ∩ closedSquare 0 1,
        ENNReal.ofReal (∫ z in closedSquare 0 1, p s x z * p t z w ∂ν) ∂ν := by
  set K := closedSquare 0 1 with hK
  have hKc : IsCompact K := isCompact_closedSquare 0 1
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hx0 := (hp s hs x hx).1
  have hcx : ∀ τ : ℝ, 0 < τ → ∀ z ∈ K, ContinuousOn (fun w => p τ z w) K := fun τ hτ z hz =>
    hpc.comp (by fun_prop : Continuous fun w : ℂ => (τ, z, w)).continuousOn
      (fun w hw => ⟨hτ, hz, hw⟩)
  have hcy : ∀ τ : ℝ, 0 < τ → ∀ w ∈ K, ContinuousOn (fun z => p τ z w) K := fun τ hτ w hw =>
    hpc.comp (by fun_prop : Continuous fun z : ℂ => (τ, z, w)).continuousOn
      (fun z hz => ⟨hτ, hz, hw⟩)
  have hc2 : ∀ τ : ℝ, 0 < τ → ContinuousOn (fun q : ℂ × ℂ => p τ q.1 q.2) (K ×ˢ K) :=
    fun τ hτ => hpc.comp (by fun_prop : Continuous fun q : ℂ × ℂ => (τ, q.1, q.2)).continuousOn
      (fun q hq => ⟨hτ, hq.1, hq.2⟩)
  set v := s.toNNReal with hv
  set u := t.toNNReal with hu
  have hst : (s + t).toNNReal = v + u := Real.toNNReal_add hs.le ht.le
  have hEm : MeasurableSet (unitSquareTimeChangeRegularized A u ⁻¹' S) :=
    measurable_unitSquareTimeChangeRegularized hA.measurable u hS
  have hvm : Measurable (unitSquareTimeChangeRegularized A v) :=
    measurable_unitSquareTimeChangeRegularized hA.measurable v
  -- the semigroup property
  have h1 : ∫⁻ w in S ∩ K, ENNReal.ofReal (p (s + t) x w) ∂ν =
      ∫⁻ ω, reflectedPlanarBrownianMotion 0 1 (unitSquareTimeChangeRegularized A v ω)
          (unitSquareTimeChangeRegularized A u ⁻¹' S) ∂reflectedPlanarBrownianMotion 0 1 x := by
    rw [← hp.reflected_regularized_preimage hA hx (add_pos hs ht) hS,
      ← reflected_eval_pcafClockInverse_mem hA hx, hst,
      reflected_eval_pcafClockInverse_add_mem hA hx hU v u hS]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_eval_pcafClockInverse_eq_regularized hA hx] with ω h
    rw [h v]
  -- the law of the time-changed point at time `s`
  have hρm : AEMeasurable (fun w => ENNReal.ofReal (p s x w)) (ν.restrict K) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hcx s hs x hx).aemeasurable hKm)
  have hlaw : (reflectedPlanarBrownianMotion 0 1 x).map (unitSquareTimeChangeRegularized A v) =
      (ν.restrict K).withDensity fun w => ENNReal.ofReal (p s x w) := by
    ext S' hS'
    rw [Measure.map_apply hvm hS', withDensity_apply _ hS', Measure.restrict_restrict hS',
      hp.reflected_regularized_preimage hA hx hs hS']
  have hhm : Measurable fun y =>
      reflectedPlanarBrownianMotion 0 1 y (unitSquareTimeChangeRegularized A u ⁻¹' S) :=
    Kernel.measurable_coe _ hEm
  rw [h1, ← lintegral_map hhm hvm, hlaw,
    lintegral_withDensity_eq_lintegral_mul₀ hρm hhm.aemeasurable]
  -- the kernel at time `t` from the time-changed point, and Tonelli
  have h2 : ∫⁻ w, ((fun w => ENNReal.ofReal (p s x w)) * fun y =>
        reflectedPlanarBrownianMotion 0 1 y (unitSquareTimeChangeRegularized A u ⁻¹' S)) w
          ∂ν.restrict K =
      ∫⁻ w in K, ∫⁻ y in S ∩ K, ENNReal.ofReal (p s x w) * ENNReal.ofReal (p t w y) ∂ν ∂ν := by
    refine setLIntegral_congr_fun hKm fun w hw => ?_
    simp only [Pi.mul_apply]
    rw [hp.reflected_regularized_preimage hA hw ht hS,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hjoint : AEMeasurable (Function.uncurry fun w y =>
      ENNReal.ofReal (p s x w) * ENNReal.ofReal (p t w y))
        ((ν.restrict K).prod (ν.restrict (S ∩ K))) := by
    have hG : AEMeasurable (fun q : ℂ × ℂ => ENNReal.ofReal (p t q.1 q.2))
        ((ν.restrict K).prod (ν.restrict (S ∩ K))) := by
      rw [Measure.prod_restrict]
      exact ENNReal.measurable_ofReal.comp_aemeasurable
        (((hc2 t ht).mono (prod_mono subset_rfl inter_subset_right)).aemeasurable
          (hKm.prod (hS.inter hKm)))
    exact (hρm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul hG
  refine h2.trans ((lintegral_lintegral_swap hjoint).trans ?_)
  refine setLIntegral_congr_fun (hS.inter hKm) fun y hy => ?_
  have hcy' : ContinuousOn (fun z => p s x z * p t z y) K :=
    (hcx s hs x hx).mul (hcy t ht y hy.2)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcy'
  have hint : Integrable (fun z => p s x z * p t z y) (ν.restrict K) := by
    refine Integrable.of_bound (hcy'.aestronglyMeasurable hKm) C ?_
    filter_upwards [ae_restrict_mem hKm] with z hz using hC z hz
  have hnn : 0 ≤ᵐ[ν.restrict K] fun z => p s x z * p t z y := by
    filter_upwards [ae_restrict_mem hKm] with z hz
    exact mul_nonneg (hx0 z hz) ((hp t ht z hz).1 y hy.2)
  rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
  refine setLIntegral_congr_fun hKm fun z hz => ?_
  exact (ENNReal.ofReal_mul (hx0 z hz)).symm

/-- **The Chapman–Kolmogorov identity for jointly continuous heat kernels of a time change.** Let
`ν` be a finite measure charging every relative ball of `K₀` and without atoms in `K₀`, and `p` a
heat kernel of the time change of reflected Brownian motion by `A` with respect to `ν`, jointly
continuous on `(0, ∞) × K₀ × K₀`. For `s, t > 0` and `x, y ∈ K₀`,
`p(s + t, x, y) = ∫_{K₀} p(s, x, z) p(t, z, y) dν(z)`. -/
theorem IsLBMHeatKernel.chapmanKolmogorov {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hsupp : ∀ y ∈ closedSquare 0 1, ∀ r : ℝ, 0 < r → 0 < ν (ball y r ∩ closedSquare 0 1))
    (hatom : ∀ x ∈ closedSquare 0 1, ν {x} = 0) {p : ℝ → ℂ → ℂ → ℝ}
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {x : ℂ} (hx : x ∈ closedSquare 0 1) {y : ℂ}
    (hy : y ∈ closedSquare 0 1) :
    p (s + t) x y = ∫ z in closedSquare 0 1, p s x z * p t z y ∂ν := by
  set K := closedSquare 0 1 with hK
  have hKc : IsCompact K := isCompact_closedSquare 0 1
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hU := ae_tendsto_atTop_of_isLBMHeatKernel hA hp hx (hatom x hx)
  have hx0 := (hp s hs x hx).1
  have hcx : ∀ τ : ℝ, 0 < τ → ∀ z ∈ K, ContinuousOn (fun w => p τ z w) K := fun τ hτ z hz =>
    hpc.comp (by fun_prop : Continuous fun w : ℂ => (τ, z, w)).continuousOn
      (fun w hw => ⟨hτ, hz, hw⟩)
  have hcy : ∀ τ : ℝ, 0 < τ → ∀ w ∈ K, ContinuousOn (fun z => p τ z w) K := fun τ hτ w hw =>
    hpc.comp (by fun_prop : Continuous fun z : ℂ => (τ, z, w)).continuousOn
      (fun z hz => ⟨hτ, hz, hw⟩)
  have hc2 : ContinuousOn (fun q : ℂ × ℂ => p s x q.1 * p t q.1 q.2) (K ×ˢ K) :=
    ((hcx s hs x hx).comp continuousOn_fst fun q hq => hq.1).mul
      (hpc.comp (by fun_prop : Continuous fun q : ℂ × ℂ => (t, q.1, q.2)).continuousOn
        (fun q hq => ⟨ht, hq.1, hq.2⟩))
  obtain ⟨C, hC⟩ := (hKc.prod hKc).exists_bound_of_continuousOn hc2
  have hgc : ContinuousOn (fun w => ∫ z in K, p s x z * p t z w ∂ν) K := by
    refine continuousOn_of_dominated (bound := fun _ => C) (fun w hw => ?_) (fun w hw => ?_)
      (integrable_const C) ?_
    · exact ((hcx s hs x hx).mul (hcy t ht w hw)).aestronglyMeasurable hKm
    · filter_upwards [ae_restrict_mem hKm] with z hz using hC (z, w) ⟨hz, hw⟩
    · filter_upwards [ae_restrict_mem hKm] with z hz
      exact continuousOn_const.mul (hcx t ht z hz)
  exact eqOn_of_forall_setLIntegral_eq (f := fun w => p (s + t) x w)
    (g := fun w => ∫ z in K, p s x z * p t z w ∂ν) hKm hsupp
    (hp (s + t) (add_pos hs ht) x hx).1
    (fun w hw => setIntegral_nonneg hKm fun z hz => mul_nonneg (hx0 z hz) ((hp t ht z hz).1 w hw))
    (hcx (s + t) (add_pos hs ht) x hx) hgc
    (fun S hS => hp.setLIntegral_add hA hpc hx hU hs ht hS) hy

end HarmonicBalls
