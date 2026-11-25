import HarmonicBalls.Proofs.Potential.ReflectedEigenTransition

/-!
# The eigenfunction kernel against bounded continuous functions

Let `A`, `ν` and the eigenbasis `(1, φ_i)` be as in `ReflectedEigenTransition.lean`, and
`p(t, x, y) = 1 + ∑_i e^{-λ_i t} ϕ_i(x) ϕ_i(y)` the eigenfunction kernel. For every bounded
continuous `ψ`, `x ∈ K₀` and `v > 0`,
`E_x ψ(Y_v) = ∫ p(v, x, y) ψ(y) ν(dy)` (`timeChangeTransition_eq_integral_eigenKernel`):

* the identity holds for the finite combinations `ψ_F = ∑_{o ∈ F} ⟪b_o, ψ⟫ b_o` of the basis
  functions `b_o ∈ {1, ϕ_i}`, since `P_v b_o = e^{-λ_o v} b_o` and `∫ p(v, x, y) b_o(y) ν(dy) =
  e^{-λ_o v} b_o(x)`;
* the errors on `[d, e] ⊂ (0, ∞)` are controlled by the `L²(ν)` norm of `ψ - ψ_F`: on the side of
  the process by `∫_d^e P_w |h|(x) dw ≤ e^e R_1 |h|(x) ≤ e^e (2B + 1) ‖h‖₂`
  (`resolventReal_abs_le`, from the centered resolvent identity), on the side of the kernel by
  its bound on `[d, e] × K₀ × K₀`; and `ψ_F → ψ` in `L²(ν)` since `(1, φ_i)` is a Hilbert basis;
* so the integrals over every `[d, e]` agree, and both sides are right-continuous in `v`
  (the kernel side is continuous), hence agree at every `v > 0` (fundamental theorem of calculus).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess
open scoped ENNReal NNReal InnerProductSpace BoundedContinuousFunction

namespace HarmonicBalls

variable {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}

theorem abs_resolventReal_le (hA : ∀ t, Measurable (A t)) {β c : ℝ} (hβ : 0 ≤ β) (hc : 0 < c)
    {h : ℂ → ℝ} (hh : Measurable h) {M : ℝ} (hM : ∀ z, |h z| ≤ M) (x : ℂ) :
    |resolventReal A β c h x| ≤ M / c := by
  unfold resolventReal
  calc |∫ b, (∫ u in Ioi (0 : ℝ), resolventIntegrand A β c h (b, u))
        ∂reflectedPlanarBrownianMotion 0 1 x|
      ≤ ∫ b, |∫ u in Ioi (0 : ℝ), resolventIntegrand A β c h (b, u)|
          ∂reflectedPlanarBrownianMotion 0 1 x := abs_integral_le_integral_abs
    _ ≤ ∫ _, M / c ∂reflectedPlanarBrownianMotion 0 1 x :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
          (Eventually.of_forall fun b => (integrable_resolventIntegrand hA hβ hc hh hM b).2)
    _ = M / c := by simp

/-- `∫ |h| ≤ (∫ h²)^{1/2}` for bounded measurable `h` and a probability measure. -/
theorem integral_abs_le_sqrt_integral_sq {ν : Measure ℂ} [IsProbabilityMeasure ν] {h : ℂ → ℝ}
    (hh : Measurable h) {M : ℝ} (hM : ∀ z, |h z| ≤ M) :
    ∫ y, |h y| ∂ν ≤ Real.sqrt (∫ y, h y ^ 2 ∂ν) := by
  have hi : Integrable h ν := integrable_of_abs_le hh hM
  have hi2 : Integrable (fun y => h y ^ 2) ν := Integrable.of_bound
    (hh.pow_const 2).aestronglyMeasurable (M ^ 2) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hM y) 2)
  set m := ∫ y, |h y| ∂ν with hm
  have hvar : ∫ y, (|h y| - m) ^ 2 ∂ν = (∫ y, h y ^ 2 ∂ν) - m ^ 2 := by
    have e : (fun y => (|h y| - m) ^ 2) = fun y => h y ^ 2 - 2 * m * |h y| + m ^ 2 := by
      funext y
      rw [sub_sq, sq_abs]
      ring
    have i1 : Integrable (fun y => h y ^ 2 - 2 * m * |h y|) ν := hi2.sub (hi.abs.const_mul _)
    rw [e, integral_add i1 (integrable_const _),
      integral_sub hi2 (hi.abs.const_mul _), integral_const_mul, integral_const, smul_eq_mul,
      probReal_univ, one_mul]
    ring
  have h0 : 0 ≤ ∫ y, (|h y| - m) ^ 2 ∂ν := integral_nonneg fun _ => sq_nonneg _
  exact Real.le_sqrt_of_sq_le (by linarith)

section Eigen

variable [IsProbabilityMeasure (unitSquareRevuzMeasure A)]
  {hν : IsUpperRegularSpeed (unitSquareRevuzMeasure A)} (E : GreenEigenData hν)

/-- **The resolvent of `|h|`**: `R_c |h|(x) ≤ (2B + 1/c) (∫ h² dν)^{1/2}` on `K₀`, where `B`
bounds the rows of `G`. -/
theorem resolventReal_abs_le (hA : IsUnitSquarePCAF A) {c : ℝ} (hc : 0 < c) {h : ℂ → ℝ}
    (hh : Measurable h) {M : ℝ} (hM : ∀ z, |h z| ≤ M) {x : ℂ} (hx : x ∈ closedSquare (0 : ℂ) 1)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ z ∈ closedSquare (0 : ℂ) 1, ‖centeredGreenRow hν z‖ ≤ B) :
    resolventReal A 0 c (fun z => |h z|) x ≤
      (2 * B + 1 / c) * Real.sqrt (∫ y, h y ^ 2 ∂unitSquareRevuzMeasure A) := by
  set ν := unitSquareRevuzMeasure A with hν_def
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hah : Measurable fun z => |h z| := hh.abs
  have hi : Integrable h ν := integrable_of_abs_le hh hM
  have hi2 : Integrable (fun y => h y ^ 2) ν := Integrable.of_bound (hh.pow_const 2).aestronglyMeasurable
    (M ^ 2) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hM y) 2)
  set m := ∫ y, |h y| ∂ν with hm
  have hm0 : 0 ≤ m := integral_nonneg fun _ => abs_nonneg _
  have hmM : m ≤ M := by
    calc m ≤ ∫ _, M ∂ν := integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (integrable_const _) (Eventually.of_forall hM)
      _ = M := by simp
  set f : ℂ → ℝ := fun z => |h z| - m with hf
  have hfm : Measurable f := hah.sub_const _
  have hfM : ∀ z, |f z| ≤ 2 * M := fun z => by
    simp only [hf]
    rw [abs_le]
    constructor <;> linarith [abs_nonneg (h z), hM z]
  have hf0 : ∫ y, f y ∂ν = 0 := by
    simp only [hf]
    rw [integral_sub hi.abs (integrable_const _), integral_const, smul_eq_mul, probReal_univ,
      one_mul, sub_self]
  -- the variance identity
  have hvar : ∫ y, f y ^ 2 ∂ν = (∫ y, h y ^ 2 ∂ν) - m ^ 2 := by
    have e : (fun y => f y ^ 2) = fun y => h y ^ 2 - 2 * m * |h y| + m ^ 2 := by
      funext y
      simp only [hf]
      rw [sub_sq, sq_abs]
      ring
    have i1 : Integrable (fun y => h y ^ 2 - 2 * m * |h y|) ν := hi2.sub (hi.abs.const_mul _)
    rw [e, integral_add i1 (integrable_const _),
      integral_sub hi2 (hi.abs.const_mul _), integral_const_mul, integral_const, smul_eq_mul,
      probReal_univ, one_mul]
    ring
  have hf2nn : 0 ≤ ∫ y, f y ^ 2 ∂ν := integral_nonneg fun _ => sq_nonneg _
  have hmsq : m ≤ Real.sqrt (∫ y, h y ^ 2 ∂ν) := Real.le_sqrt_of_sq_le (by linarith)
  have hfsq : Real.sqrt (∫ y, f y ^ 2 ∂ν) ≤ Real.sqrt (∫ y, h y ^ 2 ∂ν) :=
    Real.sqrt_le_sqrt (by linarith [sq_nonneg m])
  -- the Lp element of `f`
  have hfL : MemLp f 2 ν := memLp_of_bounded (μ := ν) (a := -(2 * M)) (b := 2 * M)
    (Eventually.of_forall fun z => abs_le.1 (hfM z)) hfm.aestronglyMeasurable 2
  set fL := hfL.toLp f with hfL_def
  have hnorm : ‖fL‖ = Real.sqrt (∫ y, f y ^ 2 ∂ν) := by
    rw [← Real.sqrt_sq (norm_nonneg fL), norm_sq_toLp_eq]
  have hmean : ⟪oneLp ν, fL⟫_ℝ = 0 := by
    rw [inner_oneLp_left, integral_congr_ae hfL.coeFn_toLp, hf0]
  have hQ : meanZeroProj ν fL = fL := meanZeroProj_of_inner_eq_zero hmean
  -- the identity for `f`
  have hid := resolventReal_add_resolventReal_greenPotential hA hν hc hfm hfM hf0 hx
  set k := ⟪greenOperator hν (oneLp ν), fL⟫_ℝ with hk
  set Gf : ℂ → ℝ := rowEval (centeredGreenRow hν) fL with hGf
  have hGfm : Measurable Gf := by
    classical
    have h := (continuousOn_rowEval hν.isRowFamily_centeredGreenRow fL)
    have h' : Gf = (closedSquare 0 1).piecewise Gf 0 := by
      funext z
      by_cases hz : z ∈ closedSquare (0 : ℂ) 1
      · simp [hz]
      · simp [hz, hGf, rowEval]
    rw [h']
    exact h.measurable_piecewise continuousOn_const measurableSet_closedSquare_zero_one
  have hGfb : ∀ z, |Gf z| ≤ B * ‖fL‖ := fun z =>
    abs_rowEval_le hB0 hB fL z
  have hVG : ∀ z ∈ closedSquare (0 : ℂ) 1, centeredGreenPotential ν f z = Gf z + k := by
    intro z hz
    have h1 : Gf z = ⟪greenRow ν z, fL⟫_ℝ - k := by
      rw [hGf, rowEval_of_mem hz, centeredGreenRow, inner_sub_left, inner_meanZeroProj_comm,
        inner_meanZeroProj_comm, hQ]
    have h2 : ⟪greenRow ν z, fL⟫_ℝ = centeredGreenPotential ν f z := by
      rw [hν.inner_greenRow hz, centeredGreenPotential]
      refine integral_congr_ae ?_
      filter_upwards [hfL.coeFn_toLp] with y hy
      rw [hy]
    rw [h1, h2]
    ring
  have hcongr : resolventReal A 0 c ((closedSquare 0 1).indicator (centeredGreenPotential ν f)) x =
      resolventReal A 0 c (fun z => Gf z + k) x :=
    resolventReal_congr (fun z hz => by rw [indicator_of_mem hz, hVG z hz]) x
  rw [hcongr, resolventReal_add hA.measurable le_rfl hc hGfm measurable_const hGfb
    (fun _ => le_rfl), resolventReal_const hc, hVG x hx] at hid
  have hRf : resolventReal A 0 c f x = Gf x - c * resolventReal A 0 c Gf x := by
    field_simp at hid
    linarith
  have hRG := abs_resolventReal_le hA.measurable le_rfl hc hGfm hGfb x
  have hRfb : |resolventReal A 0 c f x| ≤ 2 * B * ‖fL‖ := by
    rw [hRf]
    calc |Gf x - c * resolventReal A 0 c Gf x| ≤ |Gf x| + c * |resolventReal A 0 c Gf x| := by
          have h := abs_sub (Gf x) (c * resolventReal A 0 c Gf x)
          rwa [abs_mul, abs_of_pos hc] at h
      _ ≤ B * ‖fL‖ + c * (B * ‖fL‖ / c) :=
          add_le_add (hGfb x) (mul_le_mul_of_nonneg_left hRG hc.le)
      _ = 2 * B * ‖fL‖ := by field_simp; ring
  -- back to `|h| = f + m`
  have habs : resolventReal A 0 c (fun z => |h z|) x = resolventReal A 0 c f x + m / c := by
    have e : (fun z => |h z|) = fun z => f z + m := by funext z; simp only [hf]; ring
    rw [e, resolventReal_add hA.measurable le_rfl hc hfm measurable_const hfM (fun _ => le_rfl),
      resolventReal_const hc]
  rw [habs]
  rw [hnorm] at hRfb
  have hsq0 : 0 ≤ Real.sqrt (∫ y, h y ^ 2 ∂ν) := Real.sqrt_nonneg _
  calc resolventReal A 0 c f x + m / c ≤ 2 * B * Real.sqrt (∫ y, f y ^ 2 ∂ν) + m / c := by
        linarith [(abs_le.1 hRfb).2]
    _ ≤ 2 * B * Real.sqrt (∫ y, h y ^ 2 ∂ν) + Real.sqrt (∫ y, h y ^ 2 ∂ν) / c := by
        gcongr
    _ = (2 * B + 1 / c) * Real.sqrt (∫ y, h y ^ 2 ∂ν) := by ring

namespace GreenEigenData

/-- The basis functions `1` and `ϕ_i`. -/
noncomputable def rep : Option E.ι → ℂ → ℝ := fun o => o.elim (fun _ => 1) E.eigenfun

/-- The rates `0` and `λ_i = 1/μ_i`. -/
noncomputable def rate : Option E.ι → ℝ := fun o => o.elim 0 fun i => 1 / E.eig i

theorem measurable_rep (o : Option E.ι) : Measurable (E.rep o) := by
  cases o with
  | none => exact measurable_const
  | some i => exact E.measurable_eigenfun i

theorem exists_abs_rep_le (o : Option E.ι) : ∃ C : ℝ, ∀ z, |E.rep o z| ≤ C := by
  obtain ⟨B, hB0, hB⟩ := hν.isRowFamily_centeredGreenRow.bound
  cases o with
  | none => exact ⟨1, fun _ => by simp [rep]⟩
  | some i => exact ⟨(E.eig i)⁻¹ * B, E.abs_eigenfun_le hB0 hB i⟩

theorem coeFn_basis_eq_rep (o : Option E.ι) :
    (E.basis o : ℂ → ℝ) =ᵐ[unitSquareRevuzMeasure A] E.rep o := by
  cases o with
  | none => rw [E.basis_none]; exact coeFn_oneLp
  | some i => exact E.coeFn_basis_eq_eigenfun i

theorem timeChangeTransition_rep (hA : IsUnitSquarePCAF A) (o : Option E.ι) {x : ℂ}
    (hx : x ∈ closedSquare (0 : ℂ) 1) {u : ℝ} (hu : 0 < u) :
    timeChangeTransition A (E.rep o) u x = Real.exp (-(u * E.rate o)) * E.rep o x := by
  cases o with
  | none => simp [timeChangeTransition, rep, rate]
  | some i =>
    show timeChangeTransition A (E.eigenfun i) u x =
      Real.exp (-(u * (1 / E.eig i))) * E.eigenfun i x
    rw [mul_one_div]
    exact timeChangeTransition_eigenfun E hA i hx hu

theorem integral_eigenKernel_mul_rep {t : ℝ} (ht : 0 < t) {x : ℂ}
    (hx : x ∈ closedSquare (0 : ℂ) 1) (o : Option E.ι) :
    ∫ y, E.eigenKernel t x y * E.rep o y ∂unitSquareRevuzMeasure A =
      Real.exp (-(t * E.rate o)) * E.rep o x := by
  cases o with
  | none =>
    simp only [rep, rate, Option.elim_none, mul_one, mul_zero, neg_zero, Real.exp_zero]
    exact E.integral_eigenKernel ht hx
  | some i =>
    show ∫ y, E.eigenKernel t x y * E.eigenfun i y ∂unitSquareRevuzMeasure A =
      Real.exp (-(t * (1 / E.eig i))) * E.eigenfun i x
    rw [mul_one_div]
    exact E.integral_eigenKernel_mul_eigenfun ht hx i

end GreenEigenData

theorem coeFn_finsetSum_Lp {ν : Measure ℂ} {α : Type*} (F : Finset α) (g : α → Lp ℝ 2 ν) :
    (⇑(∑ o ∈ F, g o) : ℂ → ℝ) =ᵐ[ν] fun y => ∑ o ∈ F, (g o : ℂ → ℝ) y := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (Lp.coeFn_zero _ _ _).trans (Eventually.of_forall fun _ => rfl)
  | insert a F ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (g a) (∑ o ∈ F, g o), ih] with y h1 h2
    rw [h1, Pi.add_apply, h2]

/-- **The kernel represents the transition operators on bounded continuous functions.** -/
theorem timeChangeTransition_eq_integral_eigenKernel (hA : IsUnitSquarePCAF A) (ψ : ℂ →ᵇ ℝ)
    {x : ℂ} (hx : x ∈ closedSquare (0 : ℂ) 1) {v : ℝ} (hv : 0 < v) :
    timeChangeTransition A ψ v x = ∫ y, E.eigenKernel v x y * ψ y ∂unitSquareRevuzMeasure A := by
  set ν := unitSquareRevuzMeasure A with hν_def
  obtain ⟨B, hB0, hB⟩ := hν.isRowFamily_centeredGreenRow.bound
  set D := 24 * B ^ 2 * (∑' i, E.eig i ^ 2) with hD
  have hD0 : 0 ≤ D := by
    rw [hD]
    exact mul_nonneg (by positivity) (tsum_nonneg fun i => sq_nonneg _)
  have hψm : Measurable ψ := ψ.continuous.measurable
  have hψb : ∀ z, |ψ z| ≤ ‖ψ‖ := fun z => by rw [← Real.norm_eq_abs]; exact ψ.norm_coe_le_norm z
  -- the kernel side and its bounds
  set Kf : ℝ → ℝ := fun w => ∫ y, E.eigenKernel w x y * ψ y ∂ν with hKf
  have hpb : ∀ {w : ℝ}, 0 < w → ∀ y, |E.eigenKernel w x y| ≤ 1 + D / w ^ 4 := by
    intro w hw y
    have h := E.abs_eigenKernel_sub_one_le hB0 hB hw x y
    rw [abs_le] at h ⊢
    have : D / w ^ 4 = 24 * B ^ 2 * (∑' i, E.eig i ^ 2) / w ^ 4 := rfl
    constructor <;> linarith [h.1, h.2]
  have hpi : ∀ {w : ℝ}, 0 < w → ∀ {g : ℂ → ℝ}, Measurable g → ∀ {C : ℝ}, (∀ y, |g y| ≤ C) →
      Integrable (fun y => E.eigenKernel w x y * g y) ν := by
    intro w hw g hg C hC
    have hm : AEStronglyMeasurable (fun y => E.eigenKernel w x y * g y) ν := by
      have hrestr : ν.restrict (closedSquare 0 1) = ν :=
        Measure.restrict_eq_self_of_ae_mem hν.ae_mem
      have h1 := (E.continuousOn_eigenKernel_right hw hx).aestronglyMeasurable (μ := ν)
        measurableSet_closedSquare_zero_one
      rw [hrestr] at h1
      exact h1.mul hg.aestronglyMeasurable
    exact Integrable.of_bound hm ((1 + D / w ^ 4) * C) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hpb hw y) (hC y) (abs_nonneg _) (by positivity))
  -- continuity in time of the kernel side
  have hKcont : ∀ {g : ℂ → ℝ}, Measurable g → ∀ {C : ℝ}, (∀ y, |g y| ≤ C) →
      ContinuousOn (fun w => ∫ y, E.eigenKernel w x y * g y ∂ν) (Ioi 0) := by
    intro g hg C hC w₀ hw₀
    have hw₀' : 0 < w₀ := hw₀
    have h2 : 0 < w₀ / 2 := by positivity
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    have hcont : ContinuousOn (fun w => ∫ y, E.eigenKernel w x y * g y ∂ν) (Ioi (w₀ / 2)) := by
      refine continuousOn_of_dominated (bound := fun _ => (1 + D / (w₀ / 2) ^ 4) * C)
        (fun w hw => (hpi (h2.trans hw) hg hC).aestronglyMeasurable) (fun w hw => ?_)
        (integrable_const _) ?_
      · refine Eventually.of_forall fun y => ?_
        have hw' : w₀ / 2 < w := hw
        rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_mul ((hpb (h2.trans hw') y).trans ?_) (hC y) (abs_nonneg _) (by positivity)
        have : D / w ^ 4 ≤ D / (w₀ / 2) ^ 4 :=
          div_le_div_of_nonneg_left hD0 (by positivity) (pow_le_pow_left₀ h2.le hw'.le 4)
        linarith
      · filter_upwards [hν.ae_mem] with y hy
        refine ContinuousOn.mul ?_ continuousOn_const
        exact (E.continuousOn_eigenKernel.comp (f := fun w : ℝ => (w, x, y)) (by fun_prop)
          fun w hw => ⟨h2.trans hw, hx, hy⟩).mono subset_rfl
    exact (hcont.continuousAt
      (isOpen_Ioi.mem_nhds (show w₀ / 2 < w₀ by linarith))).continuousWithinAt
  -- the finite combinations
  set ψL : Lp ℝ 2 ν := BoundedContinuousFunction.toLp (E := ℝ) 2 ν ℝ ψ with hψL
  have hψLc : (ψL : ℂ → ℝ) =ᵐ[ν] ψ := BoundedContinuousFunction.coeFn_toLp (p := 2) (μ := ν)
    (𝕜 := ℝ) ψ
  set c : Option E.ι → ℝ := fun o => ⟪E.basis o, ψL⟫_ℝ with hc
  choose Crep hCrep using fun o => E.exists_abs_rep_le o
  set ψF : Finset (Option E.ι) → ℂ → ℝ := fun F y => ∑ o ∈ F, c o * E.rep o y with hψF
  have hψFm : ∀ F, Measurable (ψF F) := fun F =>
    Finset.measurable_sum F fun o _ => (E.measurable_rep o).const_mul _
  have hψFb : ∀ F z, |ψF F z| ≤ ∑ o ∈ F, |c o| * Crep o := fun F z =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun o _ => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hCrep o z) (abs_nonneg _))
  have hFid : ∀ F, ∀ {w : ℝ}, 0 < w →
      timeChangeTransition A (ψF F) w x = ∫ y, E.eigenKernel w x y * ψF F y ∂ν := by
    intro F w hw
    have h1 : timeChangeTransition A (ψF F) w x =
        ∑ o ∈ F, c o * timeChangeTransition A (E.rep o) w x := by
      unfold timeChangeTransition
      simp only [hψF]
      rw [integral_finsetSum _ fun o _ => ?_]
      · exact Finset.sum_congr rfl fun o _ => integral_const_mul _ _
      · exact Integrable.of_bound ((((E.measurable_rep o).comp (measurable_clockPair
          hA.measurable).snd).comp (measurable_id.prodMk measurable_const)).const_mul (c o)
          |>.aestronglyMeasurable) (|c o| * Crep o) (Eventually.of_forall fun b => by
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul_of_nonneg_left (hCrep o _) (abs_nonneg _))
    have h2 : ∫ y, E.eigenKernel w x y * ψF F y ∂ν =
        ∑ o ∈ F, c o * ∫ y, E.eigenKernel w x y * E.rep o y ∂ν := by
      simp only [hψF, Finset.mul_sum]
      rw [integral_finsetSum _ fun o _ => ?_]
      · refine Finset.sum_congr rfl fun o _ => ?_
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only
        ring
      · exact (hpi hw ((E.measurable_rep o).const_mul (c o)) (C := |c o| * Crep o) fun y => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hCrep o y) (abs_nonneg _))
    rw [h1, h2]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [E.timeChangeTransition_rep hA o hx hw, E.integral_eigenKernel_mul_rep hw hx o]
  -- the `L²` error
  have herr : ∀ F, Real.sqrt (∫ y, (ψ y - ψF F y) ^ 2 ∂ν) =
      ‖ψL - ∑ o ∈ F, c o • E.basis o‖ := by
    intro F
    have hae : (⇑(ψL - ∑ o ∈ F, c o • E.basis o) : ℂ → ℝ) =ᵐ[ν] fun y => ψ y - ψF F y := by
      have hall : ∀ᵐ y ∂ν, ∀ o : Option E.ι, (⇑(c o • E.basis o) : ℂ → ℝ) y = c o * E.rep o y :=
        ae_all_iff.2 fun o => by
          filter_upwards [Lp.coeFn_smul (c o) (E.basis o), E.coeFn_basis_eq_rep o] with y h1 h2
          rw [h1, Pi.smul_apply, h2, smul_eq_mul]
      filter_upwards [Lp.coeFn_sub ψL (∑ o ∈ F, c o • E.basis o), hψLc,
        coeFn_finsetSum_Lp F (fun o => c o • E.basis o), hall] with y h1 h2 h3 h4
      rw [h1, Pi.sub_apply, h2, h3]
      simp only [hψF, h4]
    rw [← Real.sqrt_sq (norm_nonneg _), l2_norm_sq_eq_integral_sq]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    rw [hy]
  have hsum := E.basis.hasSum_repr ψL
  have happrox : ∀ ε > 0, ∃ F, ‖ψL - ∑ o ∈ F, c o • E.basis o‖ < ε := by
    intro ε hε
    obtain ⟨F, hF⟩ := (Metric.tendsto_nhds.1 hsum ε hε).exists
    refine ⟨F, ?_⟩
    rw [dist_eq_norm] at hF
    rw [norm_sub_rev]
    simpa only [HilbertBasis.repr_apply_apply, hc] using hF
  -- the integrals over `[d, e]` agree
  have hTi : ∀ (S : Set ℝ) (g : ℂ → ℝ), Measurable g → ∀ C, (∀ z, |g z| ≤ C) →
      MeasurableSet S → volume S ≠ ⊤ →
      IntegrableOn (fun w => timeChangeTransition A g w x) S := by
    intro S g hg C hC _ hSf
    have : IsFiniteMeasure (volume.restrict S) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hSf.lt_top⟩
    exact Integrable.of_bound
      (measurable_timeChangeTransition hA.measurable hg x).aestronglyMeasurable
      C (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]; exact abs_timeChangeTransition_le hC w x)
  have hint : ∀ d e : ℝ, 0 < d → d ≤ e →
      ∫ w in Ioc d e, timeChangeTransition A ψ w x = ∫ w in Ioc d e, Kf w := by
    intro d e hd hde
    have hIoc : volume (Ioc d e) ≠ ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
    have : IsFiniteMeasure (volume.restrict (Ioc d e)) := ⟨by
      rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hIoc⟩
    have hKi : ∀ g : ℂ → ℝ, Measurable g → ∀ C, (∀ z, |g z| ≤ C) →
        IntegrableOn (fun w => ∫ y, E.eigenKernel w x y * g y ∂ν) (Ioc d e) ∧
        ∀ w ∈ Ioc d e, |∫ y, E.eigenKernel w x y * g y ∂ν| ≤
          (1 + D / d ^ 4) * ∫ y, |g y| ∂ν := by
      intro g hg C hC
      have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
      have hgi : Integrable g ν := integrable_of_abs_le hg hC
      have hbd : ∀ w ∈ Ioc d e, |∫ y, E.eigenKernel w x y * g y ∂ν| ≤
          (1 + D / d ^ 4) * ∫ y, |g y| ∂ν := by
        intro w hw
        have hw0 : 0 < w := hd.trans hw.1
        calc |∫ y, E.eigenKernel w x y * g y ∂ν| ≤ ∫ y, |E.eigenKernel w x y * g y| ∂ν :=
              abs_integral_le_integral_abs
          _ ≤ ∫ y, (1 + D / d ^ 4) * |g y| ∂ν := by
              refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
                (hgi.abs.const_mul _) (Eventually.of_forall fun y => ?_)
              show |E.eigenKernel w x y * g y| ≤ (1 + D / d ^ 4) * |g y|
              rw [abs_mul]
              refine mul_le_mul_of_nonneg_right ((hpb hw0 y).trans ?_) (abs_nonneg _)
              have : D / w ^ 4 ≤ D / d ^ 4 :=
                div_le_div_of_nonneg_left hD0 (by positivity) (pow_le_pow_left₀ hd.le hw.1.le 4)
              linarith
          _ = (1 + D / d ^ 4) * ∫ y, |g y| ∂ν := integral_const_mul _ _
      refine ⟨Integrable.of_bound (((hKcont hg hC).mono fun w hw => hd.trans hw.1).aestronglyMeasurable
        measurableSet_Ioc) ((1 + D / d ^ 4) * ∫ y, |g y| ∂ν) ((ae_restrict_iff' measurableSet_Ioc).2
          (Eventually.of_forall fun w hw => by rw [Real.norm_eq_abs]; exact hbd w hw)), hbd⟩
    refine eq_of_forall_dist_le fun ε hε => ?_
    set Ctot := Real.exp e * (2 * B + 1) + (e - d) * (1 + D / d ^ 4) + 1 with hCtot
    have hCtot0 : 0 < Ctot := by
      have : 0 ≤ e - d := by linarith
      positivity
    obtain ⟨F, hF⟩ := happrox (ε / Ctot) (by positivity)
    set h : ℂ → ℝ := fun y => ψ y - ψF F y with hh
    have hhm : Measurable h := hψm.sub (hψFm F)
    set Mh := ‖ψ‖ + ∑ o ∈ F, |c o| * Crep o with hMh
    have hhb : ∀ z, |h z| ≤ Mh := fun z =>
      (abs_sub _ _).trans (add_le_add (hψb z) (hψFb F z))
    set ρ := Real.sqrt (∫ y, h y ^ 2 ∂ν) with hρ
    have hρF : ρ < ε / Ctot := by rw [hρ, herr F]; exact hF
    have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
    -- the integrands agree with those of `h`
    have hdiff : ∀ w ∈ Ioc d e, timeChangeTransition A ψ w x - Kf w =
        timeChangeTransition A h w x - ∫ y, E.eigenKernel w x y * h y ∂ν := by
      intro w hw
      have hw0 : 0 < w := hd.trans hw.1
      have e1 : timeChangeTransition A h w x =
          timeChangeTransition A ψ w x - timeChangeTransition A (ψF F) w x := by
        unfold timeChangeTransition
        rw [← integral_sub]
        · exact Integrable.of_bound ((hψm.comp ((measurable_clockPair hA.measurable).snd.comp
            (measurable_id.prodMk measurable_const))).aestronglyMeasurable) ‖ψ‖
            (Eventually.of_forall fun b => by rw [Real.norm_eq_abs]; exact hψb _)
        · exact Integrable.of_bound (((hψFm F).comp ((measurable_clockPair
            hA.measurable).snd.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable)
            _ (Eventually.of_forall fun b => by rw [Real.norm_eq_abs]; exact hψFb F _)
      have e2 : ∫ y, E.eigenKernel w x y * h y ∂ν =
          Kf w - ∫ y, E.eigenKernel w x y * ψF F y ∂ν := by
        rw [hKf, ← integral_sub (hpi hw0 hψm hψb) (hpi hw0 (hψFm F) (hψFb F))]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [hh]
        ring
      rw [e1, e2, hFid F hw0]
      ring
    -- the side of the process
    have habsb : ∀ z, |(fun z => |h z|) z| ≤ Mh := fun z => by
      simp only [abs_abs]; exact hhb z
    have hT0 : ∀ w, 0 ≤ timeChangeTransition A (fun z => |h z|) w x := fun w =>
      integral_nonneg fun _ => abs_nonneg _
    have hR := resolventReal_abs_le hA one_pos hhm hhb hx hB0 hB
    rw [resolventReal_eq_setIntegral hA.measurable one_pos hhm.abs habsb x] at hR
    have hRi : IntegrableOn (fun w => Real.exp (-(1 * w)) *
        timeChangeTransition A (fun z => |h z|) w x) (Ioi 0) :=
      ((integrableOn_exp_neg_mul one_pos).mul_const Mh).mono'
        ((Real.continuous_exp.measurable.comp ((measurable_id.const_mul _).neg)).mul
          (measurable_timeChangeTransition hA.measurable hhm.abs x)).aestronglyMeasurable
        (Eventually.of_forall fun w => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_left (abs_timeChangeTransition_le habsb w x)
            (Real.exp_pos _).le)
    have hproc : ∫ w in Ioc d e, |timeChangeTransition A h w x| ≤
        Real.exp e * (2 * B + 1) * ρ := by
      calc ∫ w in Ioc d e, |timeChangeTransition A h w x|
          ≤ ∫ w in Ioc d e, Real.exp e * (Real.exp (-(1 * w)) *
              timeChangeTransition A (fun z => |h z|) w x) := by
            refine setIntegral_mono_on (hTi _ h hhm Mh hhb measurableSet_Ioc hIoc).abs
              ((hRi.mono_set (fun w hw => hd.trans hw.1)).const_mul _) measurableSet_Ioc
              fun w hw => ?_
            have h1 : |timeChangeTransition A h w x| ≤
                timeChangeTransition A (fun z => |h z|) w x := abs_integral_le_integral_abs
            have h2 : 1 ≤ Real.exp e * Real.exp (-(1 * w)) := by
              rw [← Real.exp_add]; exact Real.one_le_exp (by linarith [hw.2])
            calc |timeChangeTransition A h w x| ≤ 1 * timeChangeTransition A (fun z => |h z|) w x :=
                  by rw [one_mul]; exact h1
              _ ≤ Real.exp e * Real.exp (-(1 * w)) * timeChangeTransition A (fun z => |h z|) w x :=
                  mul_le_mul_of_nonneg_right h2 (hT0 w)
              _ = _ := by ring
        _ = Real.exp e * ∫ w in Ioc d e, Real.exp (-(1 * w)) *
              timeChangeTransition A (fun z => |h z|) w x := integral_const_mul _ _
        _ ≤ Real.exp e * ∫ w in Ioi (0 : ℝ), Real.exp (-(1 * w)) *
              timeChangeTransition A (fun z => |h z|) w x := by
            refine mul_le_mul_of_nonneg_left (setIntegral_mono_set hRi
              ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w _ =>
                mul_nonneg (Real.exp_pos _).le (hT0 w)))
              (Eventually.of_forall fun w hw => hd.trans hw.1)) (Real.exp_pos _).le
        _ ≤ Real.exp e * ((2 * B + 1 / 1) * ρ) := mul_le_mul_of_nonneg_left hR (Real.exp_pos _).le
        _ = Real.exp e * (2 * B + 1) * ρ := by ring
    -- the side of the kernel
    obtain ⟨hKhi, hKhb⟩ := hKi h hhm Mh hhb
    have hJ := integral_abs_le_sqrt_integral_sq (ν := ν) hhm hhb
    have hkern : ∫ w in Ioc d e, |∫ y, E.eigenKernel w x y * h y ∂ν| ≤
        (e - d) * (1 + D / d ^ 4) * ρ := by
      calc ∫ w in Ioc d e, |∫ y, E.eigenKernel w x y * h y ∂ν|
          ≤ ∫ _ in Ioc d e, (1 + D / d ^ 4) * ρ := by
            refine setIntegral_mono_on hKhi.abs (integrable_const _) measurableSet_Ioc
              fun w hw => (hKhb w hw).trans (mul_le_mul_of_nonneg_left hJ (by positivity))
        _ = (e - d) * (1 + D / d ^ 4) * ρ := by
            rw [setIntegral_const, Measure.real, Real.volume_Ioc,
              ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
            ring
    -- conclusion
    rw [dist_eq_norm, Real.norm_eq_abs, ← integral_sub
      (hTi _ ψ hψm ‖ψ‖ hψb measurableSet_Ioc hIoc) (hKi ψ hψm ‖ψ‖ hψb).1,
      setIntegral_congr_fun measurableSet_Ioc hdiff]
    calc |∫ w in Ioc d e, (timeChangeTransition A h w x - ∫ y, E.eigenKernel w x y * h y ∂ν)|
        ≤ ∫ w in Ioc d e, |timeChangeTransition A h w x - ∫ y, E.eigenKernel w x y * h y ∂ν| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ w in Ioc d e, (|timeChangeTransition A h w x| +
            |∫ y, E.eigenKernel w x y * h y ∂ν|) :=
          setIntegral_mono_on (((hTi _ h hhm Mh hhb measurableSet_Ioc hIoc).sub hKhi).abs)
            ((hTi _ h hhm Mh hhb measurableSet_Ioc hIoc).abs.add hKhi.abs) measurableSet_Ioc
            fun w _ => abs_sub _ _
      _ = (∫ w in Ioc d e, |timeChangeTransition A h w x|) +
            ∫ w in Ioc d e, |∫ y, E.eigenKernel w x y * h y ∂ν| :=
          integral_add (hTi _ h hhm Mh hhb measurableSet_Ioc hIoc).abs hKhi.abs
      _ ≤ Real.exp e * (2 * B + 1) * ρ + (e - d) * (1 + D / d ^ 4) * ρ := add_le_add hproc hkern
      _ ≤ Ctot * ρ := by
          rw [hCtot]
          nlinarith
      _ ≤ Ctot * (ε / Ctot) := mul_le_mul_of_nonneg_left hρF.le hCtot0.le
      _ = ε := by field_simp
  -- from the intervals to the points: the fundamental theorem of calculus
  have hd : 0 < v / 2 := by positivity
  have hIv : volume (Ioc (v / 2) v) ≠ ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hTm : Measurable fun w => timeChangeTransition A ψ w x :=
    measurable_timeChangeTransition hA.measurable hψm x
  have hKc := hKcont hψm hψb
  have hKv : ContinuousAt Kf v := hKc.continuousAt (isOpen_Ioi.mem_nhds hv)
  have h1 : HasDerivWithinAt (fun u => ∫ w in (v / 2)..u, timeChangeTransition A ψ w x)
      (timeChangeTransition A ψ v x) (Ici v) v := by
    refine intervalIntegral.integral_hasDerivWithinAt_right ?_
      hTm.stronglyMeasurable.stronglyMeasurableAtFilter
      ((continuousWithinAt_timeChangeTransition hA hψm ψ.continuous.continuousOn hψb hx v).mono
        Ioi_subset_Ici_self)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact hTi _ ψ hψm ‖ψ‖ hψb measurableSet_Ioc hIv
  have h2 : HasDerivWithinAt (fun u => ∫ w in (v / 2)..u, Kf w) (Kf v) (Ici v) v := by
    refine intervalIntegral.integral_hasDerivWithinAt_right ?_
      ((hKc.stronglyMeasurableAtFilter isOpen_Ioi v hv).filter_mono nhdsWithin_le_nhds)
      hKv.continuousWithinAt
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact ((hKc.mono fun w hw => hd.trans_le hw.1).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hΦ : EqOn (fun u => ∫ w in (v / 2)..u, timeChangeTransition A ψ w x)
      (fun u => ∫ w in (v / 2)..u, Kf w) (Ici v) := by
    intro u hu
    have hu' : v ≤ u := hu
    simp only
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith)]
    exact hint (v / 2) u hd (by linarith)
  exact UniqueDiffWithinAt.eq_deriv (Ici v) (uniqueDiffWithinAt_Ici v) h1
    (h2.congr hΦ (hΦ (mem_Ici.2 le_rfl)))

end Eigen

end HarmonicBalls
