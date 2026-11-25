import HarmonicBalls.Proofs.Potential.ReflectedEigenHeatKernel
import HarmonicBalls.Proofs.Potential.ReflectedLBMHeatKernelProposition

/-!
# Proposition 2.6 with no cited input

The two instances of cited theorems that the proof of Proposition 2.6 uses are proved:

* **the instance of Kigami's Theorem 13.1** (`kigamiLQGInstanceStmt`): almost surely, for every
  square and every additive functional `A` of reflected Brownian motion in `K₀` with Revuz measure
  the normalized LQG measure `ν`, the time change by `A` has, from every start of `K₀`, a heat kernel
  with respect to `ν` that is jointly continuous on `(0, ∞) × K₀ × K₀`. The kernel is
  `p(t, x, y) = 1 + ∑ e^{-t/μ_i} ϕ_i(x) ϕ_i(y)`, from an eigenbasis `(μ_i, ϕ_i)` of the centered
  Green operator of the square on `L²(ν)` (`isLBMHeatKernel_eigenKernel`);
* **the instance of [KLVW] Theorem A.2** (`klvwHeatKernelInstanceStmt`): the transition semigroup
  of every jointly continuous heat kernel of such a time change is positivity improving at every
  `t > 0`, since the kernel equals the eigenfunction kernel, which is strictly positive on
  `(0, ∞) × K₀ × K₀` (`eigenKernel_pos`).

So Proposition 2.6 holds with no hypothesis (`reflectedLBMHeatKernelStmt_holds`).

Kigami's Theorem 13.1 is stated for the time change of the reflected process with generator `Δ`,
whose kernel is `p(t/2, x, y)` in the normalization of reflected Brownian motion used here; and the
instance used here quantifies over every additive functional with the given Revuz measure and over
every start of `K₀`, which the expansion above gives directly. The instance of [KLVW] Theorem A.2
is the finite-measure specialization of the cited theorem.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess
open scoped ENNReal NNReal InnerProductSpace

universe u

namespace HarmonicBalls

/-- **The instance of [KLVW] Theorem A.2 used for Proposition 2.6**, proved. -/
theorem klvwHeatKernelInstanceStmt : KLVWHeatKernelInstanceStmt := by
  intro A ν _ p hA hRev hprob hup hνK hsupp _ hp hpc _ _ _ t ht f hf0 hff
  subst hRev
  have hν : IsUpperRegularSpeed (unitSquareRevuzMeasure A) := ⟨hνK, hup⟩
  obtain ⟨E⟩ := hν.nonempty_greenEigenData
  have hKm : MeasurableSet (closedSquare (0 : ℂ) 1) := measurableSet_closedSquare_zero_one
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  -- the kernel is the eigenfunction kernel, hence strictly positive on `K₀ × K₀`
  have hpos : ∀ x ∈ closedSquare (0 : ℂ) 1, ∀ y ∈ closedSquare (0 : ℂ) 1, 0 < p t x y := by
    intro x hx y hy
    rw [IsLBMHeatKernel.eq_of_continuousOn hKm hsupp hp (isLBMHeatKernel_eigenKernel E hA hsupp)
      hpc E.continuousOn_eigenKernel ht' hx hy]
    exact eigenKernel_pos E hA hsupp ht' hx hy
  -- `f` is integrable and not almost everywhere zero
  have hfi : Integrable (f : ℂ → ℝ) (unitSquareRevuzMeasure A) :=
    (Lp.memLp f).integrable (by norm_num)
  have hfne : unitSquareRevuzMeasure A (Function.support (f : ℂ → ℝ)) ≠ 0 := by
    intro h0
    have hae : (f : ℂ → ℝ) =ᵐ[unitSquareRevuzMeasure A] 0 := by
      rw [EventuallyEq, ae_iff]
      exact h0
    have hf : f = 0 := (Lp.eq_zero_iff_ae_eq_zero).2 hae
    rw [hf, inner_zero_left] at hff
    exact lt_irrefl _ hff
  have hd := isL2KernelData_of_continuousOn hνK hpc ht'
  rw [heatKernelL2Semigroup_of_ne_zero _ _ ht.ne']
  filter_upwards [hd.coeFn_kernelL2Operator f, hν.ae_mem] with x hx hxK
  rw [hx]
  show 0 < ∫ y in closedSquare 0 1, p t x y * f y ∂unitSquareRevuzMeasure A
  have hpy : ContinuousOn (fun y => p t x y) (closedSquare 0 1) :=
    hpc.comp (by fun_prop : Continuous fun y : ℂ => ((t : ℝ), x, y)).continuousOn
      fun y hy => ⟨ht', hxK, hy⟩
  obtain ⟨C, hC⟩ := (isCompact_closedSquare 0 1).exists_bound_of_continuousOn hpy
  have hint : Integrable (fun y => p t x y * f y)
      ((unitSquareRevuzMeasure A).restrict (closedSquare 0 1)) := by
    refine Integrable.mono' (hfi.norm.const_mul C).integrableOn
      ((hpy.aestronglyMeasurable hKm).mul (Lp.aestronglyMeasurable f).restrict) ?_
    filter_upwards [ae_restrict_mem hKm] with y hy
    show ‖p t x y * f y‖ ≤ C * ‖f y‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC y hy) (norm_nonneg _)
  have hnn : 0 ≤ᵐ[(unitSquareRevuzMeasure A).restrict (closedSquare 0 1)]
      fun y => p t x y * f y := by
    filter_upwards [ae_restrict_mem hKm, ae_restrict_of_ae hf0] with y hy hfy
    exact mul_nonneg (hpos x hxK y hy).le hfy
  rw [integral_pos_iff_support_of_nonneg_ae hnn hint, Measure.restrict_apply' hKm]
  refine lt_of_lt_of_le ?_ (measure_mono (show Function.support (f : ℂ → ℝ) ∩ closedSquare 0 1 ⊆
    Function.support (fun y => p t x y * f y) ∩ closedSquare 0 1 from fun y hy => ⟨?_, hy.2⟩))
  · rw [measure_inter_conull hνK]
    exact pos_iff_ne_zero.2 hfne
  · exact mul_ne_zero (hpos x hxK y hy.2).ne' hy.1

/-- **The instance of Kigami's Theorem 13.1 used for Proposition 2.6**, proved. -/
theorem kigamiLQGInstanceStmt : KigamiLQGInstanceStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hh hμ
  filter_upwards [ae_forall_closedSquare_kigamiVolumeBounds hγ hγ2 hα hh hμ,
    ae_forall_closedSquare_unitSquareNormalizedMeasure_ball_inter_pos hγ hγ2 hα hh hμ]
    with ω hω hpω
  intro a L hL A hA hRev
  obtain ⟨hprob, hcarried, c₁, c₂, α₁, α₂, -, hc₂, -, hα₂, -, hb⟩ := hω a L hL
  have hsupp := hpω a L hL
  rw [← hRev] at hprob hcarried hb hsupp ⊢
  have := hprob
  have hup := exists_closedBall_le_of_ball_le hc₂ hα₂ fun x hx r hr hr1 => (hb x hx r hr hr1).2
  have hν : IsUpperRegularSpeed (unitSquareRevuzMeasure A) := ⟨hcarried, hup⟩
  obtain ⟨E⟩ := hν.nonempty_greenEigenData
  exact ⟨E.eigenKernel, isLBMHeatKernel_eigenKernel E hA hsupp, E.continuousOn_eigenKernel⟩

/-- **Proposition 2.6** (prop:lbm-continuity), with no cited input: for every axis-parallel
closed square `K` and LQG clocks `F` of reflected Brownian motion in `K` from every start, almost
surely the reflected Liouville Brownian motion in `K` has a heat kernel with respect to `μ_h` that
is jointly continuous and strictly positive on `(0, ∞) × K × K`. -/
theorem reflectedLBMHeatKernelStmt_holds : ReflectedLBMHeatKernelStmt.{u} :=
  reflectedLBMHeatKernelStmt_of_instances kigamiLQGInstanceStmt klvwHeatKernelInstanceStmt

end HarmonicBalls
