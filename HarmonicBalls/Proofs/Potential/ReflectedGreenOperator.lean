import HarmonicBalls.Proofs.Potential.ReflectedCenteredGreenKernel

/-!
# The centered Green operator on `L²(ν)`

Let `ν` be a probability measure carried by `K₀ = [0, 1]²`. A family of rows `R : K₀ → L²(ν)`,
continuous and bounded on `K₀` (`IsRowFamily`), defines the operator
`(T f)(x) = ⟪R x, f⟫` (`rowOperator`). It maps `L²(ν)` into the continuous functions on `K₀`, with
`|T f(x)| ≤ B ‖f‖`, and it is compact (`isCompactOperator_rowOperator`): the functions
`x ↦ ⟪R x, f⟫` with `‖f‖ ≤ 1` are uniformly bounded and equicontinuous on the compact set `K₀`,
since `|⟪R x - R x', f⟫| ≤ ‖R x - R x'‖`, so the Arzelà–Ascoli theorem applies.

For `ν` with upper power bounds (`IsUpperRegularSpeed`), the rows `g(x, ·)` of the centered Green
kernel (`greenRow`) give the Green operator `V` (`greenOperator`), symmetric since `g` is
(`inner_greenOperator_comm`, Fubini's theorem). With `Q = I - ⟪1, ·⟫ 1` the projection onto the
functions of mean zero, `G = Q V Q` (`centeredGreenOperator`) is compact and symmetric, `G 1 = 0`,
and `G` is the row operator of the rows `Q g(x, ·) - Q V 1` (`centeredGreenOperator_eq_rowOperator`),
so `G f` has the continuous representative `x ↦ ⟪Q g(x, ·) - Q V 1, f⟫` on `K₀`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal NNReal InnerProductSpace BoundedContinuousFunction

namespace HarmonicBalls

variable {ν : Measure ℂ}

/-! ### The constant function -/

section One

variable [IsProbabilityMeasure ν]

/-- The constant function `1` in `L²(ν)`. -/
noncomputable def oneLp (ν : Measure ℂ) [IsProbabilityMeasure ν] : Lp ℝ 2 ν :=
  (memLp_const (1 : ℝ)).toLp fun _ => (1 : ℝ)

theorem coeFn_oneLp : (oneLp ν : ℂ → ℝ) =ᵐ[ν] fun _ => (1 : ℝ) :=
  (memLp_const _).coeFn_toLp

theorem inner_oneLp_left (f : Lp ℝ 2 ν) : ⟪oneLp ν, f⟫_ℝ = ∫ x, (f : ℂ → ℝ) x ∂ν := by
  rw [l2_inner_eq_integral_mul]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_oneLp (ν := ν)] with x hx
  rw [hx, one_mul]

theorem inner_oneLp_oneLp : ⟪oneLp ν, oneLp ν⟫_ℝ = 1 := by
  rw [inner_oneLp_left, integral_congr_ae (coeFn_oneLp (ν := ν))]
  simp

/-- The projection `Q = I - ⟪1, ·⟫ 1` onto the functions of mean zero. -/
noncomputable def meanZeroProj (ν : Measure ℂ) [IsProbabilityMeasure ν] :
    Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  ContinuousLinearMap.id ℝ _ - (innerSL ℝ (oneLp ν)).smulRight (oneLp ν)

theorem meanZeroProj_apply (f : Lp ℝ 2 ν) :
    meanZeroProj ν f = f - ⟪oneLp ν, f⟫_ℝ • oneLp ν := rfl

theorem inner_meanZeroProj_comm (f h : Lp ℝ 2 ν) :
    ⟪meanZeroProj ν f, h⟫_ℝ = ⟪f, meanZeroProj ν h⟫_ℝ := by
  rw [meanZeroProj_apply, meanZeroProj_apply, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm (oneLp ν) f]
  ring

theorem inner_oneLp_meanZeroProj (f : Lp ℝ 2 ν) : ⟪oneLp ν, meanZeroProj ν f⟫_ℝ = 0 := by
  rw [meanZeroProj_apply, inner_sub_right, real_inner_smul_right, inner_oneLp_oneLp, mul_one,
    sub_self]

theorem meanZeroProj_oneLp : meanZeroProj ν (oneLp ν) = 0 := by
  rw [meanZeroProj_apply, inner_oneLp_oneLp, one_smul, sub_self]

theorem meanZeroProj_of_inner_eq_zero {f : Lp ℝ 2 ν} (hf : ⟪oneLp ν, f⟫_ℝ = 0) :
    meanZeroProj ν f = f := by
  rw [meanZeroProj_apply, hf, zero_smul, sub_zero]

end One

/-! ### Row operators -/

/-- A family of rows: continuous on `K₀` into `L²(ν)` and bounded there, with `ν` carried by
`K₀`. -/
structure IsRowFamily (ν : Measure ℂ) (R : ℂ → Lp ℝ 2 ν) : Prop where
  carried : ν (closedSquare 0 1)ᶜ = 0
  cont : ContinuousOn R (closedSquare 0 1)
  bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ closedSquare (0 : ℂ) 1, ‖R x‖ ≤ B

/-- The function `x ↦ ⟪R x, f⟫` on `K₀`, extended by `0`. -/
noncomputable def rowEval (R : ℂ → Lp ℝ 2 ν) (f : Lp ℝ 2 ν) (x : ℂ) : ℝ :=
  (closedSquare 0 1).indicator (fun x => ⟪R x, f⟫_ℝ) x

section Rows

variable {R : ℂ → Lp ℝ 2 ν}

theorem rowEval_of_mem {f : Lp ℝ 2 ν} {x : ℂ} (hx : x ∈ closedSquare (0 : ℂ) 1) :
    rowEval R f x = ⟪R x, f⟫_ℝ :=
  indicator_of_mem hx _

theorem rowEval_add (f g : Lp ℝ 2 ν) (x : ℂ) :
    rowEval R (f + g) x = rowEval R f x + rowEval R g x := by
  by_cases hx : x ∈ closedSquare (0 : ℂ) 1
  · rw [rowEval_of_mem hx, rowEval_of_mem hx, rowEval_of_mem hx, inner_add_right]
  · simp [rowEval, hx]

theorem rowEval_smul (c : ℝ) (f : Lp ℝ 2 ν) (x : ℂ) :
    rowEval R (c • f) x = c * rowEval R f x := by
  by_cases hx : x ∈ closedSquare (0 : ℂ) 1
  · rw [rowEval_of_mem hx, rowEval_of_mem hx, real_inner_smul_right]
  · simp [rowEval, hx]

theorem IsRowFamily.ae_mem (hR : IsRowFamily ν R) : ∀ᵐ x ∂ν, x ∈ closedSquare (0 : ℂ) 1 :=
  ae_iff.2 hR.carried

theorem IsRowFamily.restrict_eq (hR : IsRowFamily ν R) : ν.restrict (closedSquare 0 1) = ν :=
  Measure.restrict_eq_self_of_ae_mem hR.ae_mem

theorem continuousOn_rowEval (hR : IsRowFamily ν R) (f : Lp ℝ 2 ν) :
    ContinuousOn (rowEval R f) (closedSquare 0 1) :=
  (hR.cont.inner continuousOn_const).congr fun _ hx => rowEval_of_mem hx

theorem aestronglyMeasurable_rowEval (hR : IsRowFamily ν R) (f : Lp ℝ 2 ν) :
    AEStronglyMeasurable (rowEval R f) ν := by
  have h := (continuousOn_rowEval hR f).aestronglyMeasurable (μ := ν)
    measurableSet_closedSquare_zero_one
  rwa [hR.restrict_eq] at h

theorem abs_rowEval_le {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x ∈ closedSquare (0 : ℂ) 1, ‖R x‖ ≤ B)
    (f : Lp ℝ 2 ν) (x : ℂ) : |rowEval R f x| ≤ B * ‖f‖ := by
  by_cases hx : x ∈ closedSquare (0 : ℂ) 1
  · rw [rowEval_of_mem hx]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hB x hx) (norm_nonneg _))
  · rw [rowEval, indicator_of_notMem hx, abs_zero]
    exact mul_nonneg hB0 (norm_nonneg _)

variable [IsProbabilityMeasure ν]

theorem memLp_rowEval (hR : IsRowFamily ν R) (f : Lp ℝ 2 ν) : MemLp (rowEval R f) 2 ν := by
  obtain ⟨B, hB0, hB⟩ := hR.bound
  exact memLp_of_bounded (μ := ν) (a := -(B * ‖f‖)) (b := B * ‖f‖)
    (Eventually.of_forall fun x => abs_le.1 (abs_rowEval_le hB0 hB f x))
    (aestronglyMeasurable_rowEval hR f) 2

theorem norm_toLp_rowEval_le (hR : IsRowFamily ν R) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ closedSquare (0 : ℂ) 1, ‖R x‖ ≤ B) (f : Lp ℝ 2 ν) :
    ‖(memLp_rowEval hR f).toLp (rowEval R f)‖ ≤ B * ‖f‖ := by
  refine norm_le_of_norm_sq_le (mul_nonneg hB0 (norm_nonneg _)) ?_
  rw [norm_sq_toLp_eq]
  calc ∫ y, rowEval R f y ^ 2 ∂ν ≤ ∫ _, (B * ‖f‖) ^ 2 ∂ν :=
        integral_mono_ae (memLp_rowEval hR f).integrable_sq (integrable_const _)
          (Eventually.of_forall fun y => by
            have h := abs_le.1 (abs_rowEval_le hB0 hB f y)
            exact sq_le_sq' h.1 h.2)
    _ = (B * ‖f‖) ^ 2 := by simp

/-- The row operator `(T f)(x) = ⟪R x, f⟫`. -/
noncomputable def rowOperator (hR : IsRowFamily ν R) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun f => (memLp_rowEval hR f).toLp (rowEval R f)
      map_add' := fun f g => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => rowEval_add f g x)
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => by
          rw [rowEval_smul, Pi.smul_apply, smul_eq_mul]) }
    (by
      obtain ⟨B, hB0, hB⟩ := hR.bound
      exact ⟨B, fun f => norm_toLp_rowEval_le hR hB0 hB f⟩)

theorem rowOperator_apply (hR : IsRowFamily ν R) (f : Lp ℝ 2 ν) :
    rowOperator hR f = (memLp_rowEval hR f).toLp (rowEval R f) := rfl

theorem coeFn_rowOperator (hR : IsRowFamily ν R) (f : Lp ℝ 2 ν) :
    (rowOperator hR f : ℂ → ℝ) =ᵐ[ν] rowEval R f := by
  rw [rowOperator_apply]
  exact (memLp_rowEval hR f).coeFn_toLp

theorem inner_rowOperator_left (hR : IsRowFamily ν R) (f h : Lp ℝ 2 ν) :
    ⟪rowOperator hR f, h⟫_ℝ = ∫ x, ⟪R x, f⟫_ℝ * (h : ℂ → ℝ) x ∂ν := by
  rw [l2_inner_eq_integral_mul]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_rowOperator hR f, hR.ae_mem] with x hx hxK
  rw [hx, rowEval_of_mem hxK]

/-- **Row operators are compact** (Arzelà–Ascoli). -/
theorem isCompactOperator_rowOperator (hR : IsRowFamily ν R) :
    IsCompactOperator (rowOperator hR) := by
  classical
  set K := closedSquare (0 : ℂ) 1 with hK
  have : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_closedSquare 0 1)
  obtain ⟨B, hB0, hB⟩ := hR.bound
  have hRc : Continuous (K.domRestrict R) := hR.cont.domRestrict
  -- evaluation into the bounded continuous functions on `K`
  let E : Lp ℝ 2 ν → (K →ᵇ ℝ) := fun f =>
    BoundedContinuousFunction.mkOfCompact ⟨fun z => ⟪R z, f⟫_ℝ, hRc.inner continuous_const⟩
  -- extension back to `L²(ν)`
  let ext : (K →ᵇ ℝ) → ℂ → ℝ := fun u z => if h : z ∈ K then u ⟨z, h⟩ else 0
  have hext_cont : ∀ u, ContinuousOn (ext u) K := by
    intro u
    rw [continuousOn_iff_continuous_domRestrict]
    convert u.continuous using 1
    funext z
    show ext u z = u z
    simp [ext, z.2]
  have hext_le : ∀ u z, |ext u z| ≤ ‖u‖ := by
    intro u z
    by_cases h : z ∈ K
    · have he : ext u z = u ⟨z, h⟩ := by simp [ext, h]
      rw [he, ← Real.norm_eq_abs]
      exact u.norm_coe_le_norm _
    · have he : ext u z = 0 := by simp [ext, h]
      rw [he, abs_zero]
      exact norm_nonneg _
  have hext_mem : ∀ u, MemLp (ext u) 2 ν := by
    intro u
    refine memLp_of_bounded (μ := ν) (a := -‖u‖) (b := ‖u‖)
      (Eventually.of_forall fun z => abs_le.1 (hext_le u z)) ?_ 2
    have h := (hext_cont u).aestronglyMeasurable measurableSet_closedSquare_zero_one (μ := ν)
    rwa [hR.restrict_eq] at h
  let J : (K →ᵇ ℝ) → Lp ℝ 2 ν := fun u => (hext_mem u).toLp (ext u)
  have hJ : Continuous J := by
    refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun u v => ?_)
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, ← MemLp.toLp_sub]
    refine norm_le_of_norm_sq_le (norm_nonneg _) ?_
    rw [norm_sq_toLp_eq]
    calc ∫ y, (ext u - ext v) y ^ 2 ∂ν ≤ ∫ _, ‖u - v‖ ^ 2 ∂ν := by
          refine integral_mono_ae ((hext_mem u).sub (hext_mem v)).integrable_sq
            (integrable_const _) (Eventually.of_forall fun y => ?_)
          show (ext u - ext v) y ^ 2 ≤ ‖u - v‖ ^ 2
          have he : (ext u - ext v) y = ext (u - v) y := by
            by_cases h : y ∈ K <;> simp [ext, h]
          rw [he]
          have h := abs_le.1 (hext_le (u - v) y)
          exact sq_le_sq' h.1 h.2
      _ = ‖u - v‖ ^ 2 := by simp
  have hJE : ∀ f, J (E f) = rowOperator hR f := by
    intro f
    rw [rowOperator_apply]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun z => ?_)
    by_cases h : z ∈ K
    · rw [rowEval_of_mem h]
      simp only [ext, h, dite_true]
      rfl
    · rw [rowEval, indicator_of_notMem h]
      simp [ext, h]
  -- Arzelà–Ascoli
  set A := E '' closedBall (0 : Lp ℝ 2 ν) 1 with hA
  have hAc : IsCompact (closure A) := by
    refine BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℝ) B) (isCompact_closedBall _ _)
      A ?_ ?_
    · intro u z hu
      obtain ⟨f, hf, rfl⟩ := hu
      rw [mem_closedBall, dist_zero_right]
      have hf' : ‖f‖ ≤ 1 := by simpa using hf
      calc ‖(E f) z‖ = |⟪R z, f⟫_ℝ| := rfl
        _ ≤ ‖R z‖ * ‖f‖ := abs_real_inner_le_norm _ _
        _ ≤ B * 1 := mul_le_mul (hB z z.2) hf' (norm_nonneg _) hB0
        _ = B := mul_one B
    · intro z₀
      rw [Metric.equicontinuousAt_iff_right]
      intro ε hε
      have hcz : ∀ᶠ z in 𝓝 z₀, dist (K.domRestrict R z₀) (K.domRestrict R z) < ε :=
        (hRc.tendsto z₀).eventually (Metric.ball_mem_nhds _ hε) |>.mono fun z hz => by
          rw [dist_comm]; exact hz
      filter_upwards [hcz] with z hz
      rintro ⟨_, ⟨f, hf, rfl⟩⟩
      have hf' : ‖f‖ ≤ 1 := by simpa using hf
      show dist ⟪R z₀, f⟫_ℝ ⟪R z, f⟫_ℝ < ε
      rw [Real.dist_eq, ← inner_sub_left]
      calc |⟪R z₀ - R z, f⟫_ℝ| ≤ ‖R z₀ - R z‖ * ‖f‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖R z₀ - R z‖ * 1 := mul_le_mul_of_nonneg_left hf' (norm_nonneg _)
        _ < ε := by rw [mul_one, ← dist_eq_norm]; exact hz
  refine ⟨J '' closure A, hAc.image hJ, ?_⟩
  refine Filter.mem_of_superset (closedBall_mem_nhds (0 : Lp ℝ 2 ν) one_pos) fun f hf => ?_
  exact ⟨E f, subset_closure ⟨f, hf, rfl⟩, hJE f⟩

end Rows

/-! ### The Green operator -/

section Green

variable [IsProbabilityMeasure ν]

theorem IsUpperRegularSpeed.isRowFamily_greenRow (hν : IsUpperRegularSpeed ν) :
    IsRowFamily ν (greenRow ν) :=
  ⟨hν.carried, hν.continuousOn_greenRow, hν.exists_norm_greenRow_le⟩

/-- The Green operator `V f(x) = ∫ g(x, y) f(y) ν(dy)`. -/
noncomputable def greenOperator (hν : IsUpperRegularSpeed ν) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  rowOperator hν.isRowFamily_greenRow

theorem IsUpperRegularSpeed.inner_greenRow (hν : IsUpperRegularSpeed ν) {x : ℂ}
    (hx : x ∈ closedSquare (0 : ℂ) 1) (f : Lp ℝ 2 ν) :
    ⟪greenRow ν x, f⟫_ℝ = ∫ y, centeredGreenKernel x y * (f : ℂ → ℝ) y ∂ν := by
  rw [l2_inner_eq_integral_mul]
  refine integral_congr_ae ?_
  filter_upwards [hν.coeFn_greenRow hx] with y hy
  rw [hy]

/-- **Symmetry of the Green operator** (Fubini's theorem and `g(x, y) = g(y, x)`). -/
theorem inner_greenOperator_comm (hν : IsUpperRegularSpeed ν) (f h : Lp ℝ 2 ν) :
    ⟪greenOperator hν f, h⟫_ℝ = ⟪f, greenOperator hν h⟫_ℝ := by
  obtain ⟨B₀, hB₀, hB⟩ := hν.exists_memLp_centeredGreenKernel
  have hKae := hν.ae_mem
  -- the integrand on the product
  set F : ℂ → ℂ → ℝ := fun x y => centeredGreenKernel x y * (f : ℂ → ℝ) y * (h : ℂ → ℝ) x
    with hF
  have hFm : AEStronglyMeasurable (Function.uncurry F) (ν.prod ν) :=
    ((measurable_centeredGreenKernel_uncurry.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f).comp_snd).mul (Lp.aestronglyMeasurable h).comp_fst)
  have hrow : ∀ x ∈ closedSquare (0 : ℂ) 1, ∀ u : Lp ℝ 2 ν,
      Integrable (fun y => centeredGreenKernel x y * (u : ℂ → ℝ) y) ν ∧
        ∫ y, |centeredGreenKernel x y * (u : ℂ → ℝ) y| ∂ν ≤ (B₀ + ‖u‖ ^ 2) / 2 := by
    intro x hx u
    have hg := (hB x hx).1
    have hu2 : Integrable (fun y => (u : ℂ → ℝ) y ^ 2) ν := (Lp.memLp u).integrable_sq
    have hab : ∀ a b : ℝ, |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := fun a b => by
      rw [abs_mul]
      nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]
    have hi : Integrable (fun y => centeredGreenKernel x y * (u : ℂ → ℝ) y) ν := by
      refine ((hg.integrable_sq.add hu2).div_const 2).mono'
        ((measurable_centeredGreenKernel x).aestronglyMeasurable.mul (Lp.aestronglyMeasurable u))
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, Pi.add_apply]
      exact hab _ _
    refine ⟨hi, ?_⟩
    calc ∫ y, |centeredGreenKernel x y * (u : ℂ → ℝ) y| ∂ν
        ≤ ∫ y, (centeredGreenKernel x y ^ 2 + (u : ℂ → ℝ) y ^ 2) / 2 ∂ν := by
          refine integral_mono_ae hi.abs ((hg.integrable_sq.add hu2).div_const 2)
            (Eventually.of_forall fun y => ?_)
          exact hab _ _
      _ = ((∫ y, centeredGreenKernel x y ^ 2 ∂ν) + ‖u‖ ^ 2) / 2 := by
          rw [integral_div, integral_add hg.integrable_sq hu2, ← l2_norm_sq_eq_integral_sq]
      _ ≤ (B₀ + ‖u‖ ^ 2) / 2 := by linarith [(hB x hx).2]
  have hint : Integrable (Function.uncurry F) (ν.prod ν) := by
    refine (integrable_prod_iff hFm).2 ⟨?_, ?_⟩
    · filter_upwards [hKae] with x hx
      exact ((hrow x hx f).1.mul_const ((h : ℂ → ℝ) x))
    · have hb : Integrable (fun x => (B₀ + ‖f‖ ^ 2) / 2 * |(h : ℂ → ℝ) x|) ν :=
        ((Lp.memLp h).integrable one_le_two).abs.const_mul _
      refine hb.mono' hFm.norm.integral_prod_right' ?_
      filter_upwards [hKae] with x hx
      simp only [Function.uncurry_apply_pair, hF, norm_mul, Real.norm_eq_abs]
      rw [abs_of_nonneg (integral_nonneg fun _ => by positivity), integral_mul_const]
      have := (hrow x hx f).2
      simp only [abs_mul] at this
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hswap := integral_integral_swap hint
  rw [greenOperator, inner_rowOperator_left, real_inner_comm (rowOperator hν.isRowFamily_greenRow h) f,
    inner_rowOperator_left]
  calc ∫ x, ⟪greenRow ν x, f⟫_ℝ * (h : ℂ → ℝ) x ∂ν = ∫ x, ∫ y, F x y ∂ν ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [hKae] with x hx
        rw [hν.inner_greenRow hx, ← integral_mul_const]
    _ = ∫ y, ∫ x, F x y ∂ν ∂ν := hswap
    _ = ∫ y, ⟪greenRow ν y, h⟫_ℝ * (f : ℂ → ℝ) y ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [hKae] with y hy
        rw [hν.inner_greenRow hy, ← integral_mul_const]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [hF, centeredGreenKernel_comm x y]
        ring

/-- The centered Green operator `G = Q V Q`. -/
noncomputable def centeredGreenOperator (hν : IsUpperRegularSpeed ν) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  meanZeroProj ν ∘L greenOperator hν ∘L meanZeroProj ν

theorem inner_centeredGreenOperator_comm (hν : IsUpperRegularSpeed ν) (f h : Lp ℝ 2 ν) :
    ⟪centeredGreenOperator hν f, h⟫_ℝ = ⟪f, centeredGreenOperator hν h⟫_ℝ := by
  simp only [centeredGreenOperator, ContinuousLinearMap.comp_apply]
  rw [inner_meanZeroProj_comm, inner_greenOperator_comm, inner_meanZeroProj_comm]

theorem centeredGreenOperator_oneLp (hν : IsUpperRegularSpeed ν) :
    centeredGreenOperator hν (oneLp ν) = 0 := by
  simp [centeredGreenOperator, meanZeroProj_oneLp]

theorem inner_oneLp_centeredGreenOperator (hν : IsUpperRegularSpeed ν) (f : Lp ℝ 2 ν) :
    ⟪oneLp ν, centeredGreenOperator hν f⟫_ℝ = 0 := by
  simp only [centeredGreenOperator, ContinuousLinearMap.comp_apply]
  exact inner_oneLp_meanZeroProj _

/-- The rows of the centered Green operator: `Q g(x, ·) - Q V 1`. -/
noncomputable def centeredGreenRow (hν : IsUpperRegularSpeed ν) (x : ℂ) : Lp ℝ 2 ν :=
  meanZeroProj ν (greenRow ν x) - meanZeroProj ν (greenOperator hν (oneLp ν))

theorem IsUpperRegularSpeed.isRowFamily_centeredGreenRow (hν : IsUpperRegularSpeed ν) :
    IsRowFamily ν (centeredGreenRow hν) := by
  obtain ⟨B, hB0, hB⟩ := hν.exists_norm_greenRow_le
  refine ⟨hν.carried, ((meanZeroProj ν).continuous.comp_continuousOn hν.continuousOn_greenRow).sub
    continuousOn_const, ⟨‖meanZeroProj ν‖ * B + ‖meanZeroProj ν (greenOperator hν (oneLp ν))‖,
      by positivity, fun x hx => ?_⟩⟩
  unfold centeredGreenRow
  have h1 := ((meanZeroProj ν).le_opNorm (greenRow ν x)).trans
    (mul_le_mul_of_nonneg_left (hB x hx) (norm_nonneg _))
  linarith [norm_sub_le (meanZeroProj ν (greenRow ν x))
    (meanZeroProj ν (greenOperator hν (oneLp ν)))]

/-- **`G` is the row operator of its rows**: `(G f)(x) = ⟪Q g(x, ·) - Q V 1, f⟫` on `K₀`. -/
theorem centeredGreenOperator_eq_rowOperator (hν : IsUpperRegularSpeed ν) :
    centeredGreenOperator hν = rowOperator hν.isRowFamily_centeredGreenRow := by
  ext1 f
  have hR := hν.isRowFamily_greenRow
  refine Lp.ext_iff.2 ?_
  have h1 := coeFn_rowOperator hν.isRowFamily_centeredGreenRow f
  have h2 := coeFn_rowOperator hR (meanZeroProj ν f)
  have h3 := Lp.coeFn_sub (greenOperator hν (meanZeroProj ν f))
    (⟪oneLp ν, greenOperator hν (meanZeroProj ν f)⟫_ℝ • oneLp ν)
  have h4 := Lp.coeFn_smul ⟪oneLp ν, greenOperator hν (meanZeroProj ν f)⟫_ℝ (oneLp ν)
  have h2' : (greenOperator hν (meanZeroProj ν f) : ℂ → ℝ) =ᵐ[ν]
      rowEval (greenRow ν) (meanZeroProj ν f) := h2
  have hG : centeredGreenOperator hν f = greenOperator hν (meanZeroProj ν f) -
      ⟪oneLp ν, greenOperator hν (meanZeroProj ν f)⟫_ℝ • oneLp ν := by
    rw [centeredGreenOperator, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      meanZeroProj_apply (greenOperator hν (meanZeroProj ν f))]
  rw [hG]
  filter_upwards [h1, h2', h3, h4, coeFn_oneLp (ν := ν), hR.ae_mem] with x h1 h2 h3 h4 h5 hx
  rw [h3, Pi.sub_apply, h4, Pi.smul_apply, h5, h1, h2, rowEval_of_mem hx, rowEval_of_mem hx,
    centeredGreenRow, inner_sub_left, inner_meanZeroProj_comm, inner_meanZeroProj_comm,
    inner_greenOperator_comm hν (oneLp ν), smul_eq_mul, mul_one]

end Green

end HarmonicBalls
