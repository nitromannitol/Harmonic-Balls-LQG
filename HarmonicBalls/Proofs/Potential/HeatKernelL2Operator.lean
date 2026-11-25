import Mathlib

/-!
# Integral operators with continuous kernels on `L²`

Let `ν` be a finite measure on `ℂ` carried by a compact set `K`, and `k` a function jointly
continuous on `K × K` (`IsL2KernelData ν K k`). The integral transform
`(T f)(x) = ∫_K k(x, y) f(y) dν(y)` (`kernelTransform`) maps `L²(ν)` to continuous functions on
`K`, and defines a bounded operator `kernelL2Operator ν K k` on `L²(ν)`. This module records the
properties of such operators used for the transition semigroup of a time-changed process:

* Schur's test: if `∫_K |k(x, ·)| dν ≤ R` for `x ∈ K` and `∫_K |k(·, y)| dν ≤ R` for `y ∈ K`, the
  operator norm is at most `R` (`IsL2KernelData.norm_kernelL2Operator_apply_le`), by the
  Cauchy–Schwarz inequality for the weights `|k(x, ·)|` and Tonelli's theorem;
* a symmetric kernel gives a symmetric operator (`IsL2KernelData.inner_kernelL2Operator_comm`);
* a kernel `k₃(x, y) = ∫_K k₁(x, z) k₂(z, y) dν(z)` gives the composed operator
  (`IsL2KernelData.kernelL2Operator_eq_comp`), by Fubini's theorem;
* a nonnegative kernel preserves positivity, and maps `0 ≤ f ≤ 1` to `T f ≤ 1` when its rows
  have mass at most `1` (`IsL2KernelData.ae_nonneg_kernelL2Operator`,
  `IsL2KernelData.ae_kernelL2Operator_le_one`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace

namespace HarmonicBalls

/-- The integral transform `x ↦ ∫_K k(x, y) f(y) dν(y)`. -/
noncomputable def kernelTransform (ν : Measure ℂ) (K : Set ℂ) (k : ℂ → ℂ → ℝ) (f : ℂ → ℝ)
    (x : ℂ) : ℝ :=
  ∫ y in K, k x y * f y ∂ν

/-- The integral transform depends on `f` only up to `ν`-null sets. -/
theorem kernelTransform_congr_ae {ν : Measure ℂ} {K : Set ℂ} {k : ℂ → ℂ → ℝ} {f g : ℂ → ℝ}
    (hfg : f =ᵐ[ν] g) : kernelTransform ν K k f = kernelTransform ν K k g := by
  funext x
  unfold kernelTransform
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hfg] with y hy
  rw [hy]

theorem kernelTransform_const_smul {ν : Measure ℂ} {K : Set ℂ} {k : ℂ → ℂ → ℝ} (c : ℝ)
    (f : ℂ → ℝ) (x : ℂ) :
    kernelTransform ν K k (c • f) x = c * kernelTransform ν K k f x := by
  unfold kernelTransform
  rw [← integral_const_mul]
  congr 1
  ext y
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Data of a kernel operator on `L²(ν)`: `ν` is carried by the compact set `K` and `k` is jointly
continuous on `K × K`. -/
structure IsL2KernelData (ν : Measure ℂ) (K : Set ℂ) (k : ℂ → ℂ → ℝ) : Prop where
  /-- The set `K` is compact. -/
  isCompact : IsCompact K
  /-- The measure `ν` is carried by `K`. -/
  carried : ν Kᶜ = 0
  /-- The kernel is jointly continuous on `K × K`. -/
  continuousOn : ContinuousOn (fun q : ℂ × ℂ => k q.1 q.2) (K ×ˢ K)

namespace IsL2KernelData

variable {ν : Measure ℂ} {K : Set ℂ} {k : ℂ → ℂ → ℝ}

theorem measurableSet (hd : IsL2KernelData ν K k) : MeasurableSet K :=
  hd.isCompact.isClosed.measurableSet

theorem ae_mem (hd : IsL2KernelData ν K k) : ∀ᵐ x ∂ν, x ∈ K := by
  rw [ae_iff]
  exact hd.carried

theorem restrict_eq (hd : IsL2KernelData ν K k) : ν.restrict K = ν :=
  Measure.restrict_eq_self_of_ae_mem hd.ae_mem

theorem setIntegral_eq (hd : IsL2KernelData ν K k) (g : ℂ → ℝ) :
    ∫ x in K, g x ∂ν = ∫ x, g x ∂ν := by
  rw [hd.restrict_eq]

theorem exists_bound (hd : IsL2KernelData ν K k) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ y ∈ K, |k x y| ≤ C := by
  obtain ⟨C, hC⟩ := (hd.isCompact.prod hd.isCompact).exists_bound_of_continuousOn hd.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx y hy => ?_⟩
  have h := hC (x, y) ⟨hx, hy⟩
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

/-- The kernel with absolute values. -/
theorem abs (hd : IsL2KernelData ν K k) : IsL2KernelData ν K fun x y => |k x y| :=
  ⟨hd.isCompact, hd.carried, hd.continuousOn.abs⟩

/-- The transposed kernel. -/
theorem swap (hd : IsL2KernelData ν K k) : IsL2KernelData ν K fun x y => k y x :=
  ⟨hd.isCompact, hd.carried, hd.continuousOn.comp continuous_swap.continuousOn
    fun _ hq => ⟨hq.2, hq.1⟩⟩

theorem continuousOn_right (hd : IsL2KernelData ν K k) {x : ℂ} (hx : x ∈ K) :
    ContinuousOn (k x) K :=
  hd.continuousOn.comp (by fun_prop : Continuous fun y : ℂ => (x, y)).continuousOn
    fun y hy => ⟨hx, hy⟩

theorem continuousOn_left (hd : IsL2KernelData ν K k) {y : ℂ} (hy : y ∈ K) :
    ContinuousOn (fun x => k x y) K :=
  hd.continuousOn.comp (by fun_prop : Continuous fun x : ℂ => (x, y)).continuousOn
    fun x hx => ⟨hx, hy⟩

theorem integrable_mul (hd : IsL2KernelData ν K k) {x : ℂ} (hx : x ∈ K) {f : ℂ → ℝ}
    (hf : Integrable f (ν.restrict K)) : Integrable (fun y => k x y * f y) (ν.restrict K) := by
  obtain ⟨C, -, hC⟩ := hd.exists_bound
  refine hf.bdd_mul ((hd.continuousOn_right hx).aestronglyMeasurable hd.measurableSet) (c := C) ?_
  filter_upwards [ae_restrict_mem hd.measurableSet] with y hy
  rw [Real.norm_eq_abs]
  exact hC x hx y hy

theorem integrable_right [IsFiniteMeasure ν] (hd : IsL2KernelData ν K k) {x : ℂ} (hx : x ∈ K) :
    Integrable (k x) (ν.restrict K) := by
  simpa using hd.integrable_mul hx (integrable_const (1 : ℝ))

/-- The integral transform of an integrable function is continuous on `K`. -/
theorem continuousOn_kernelTransform (hd : IsL2KernelData ν K k) {f : ℂ → ℝ}
    (hf : Integrable f (ν.restrict K)) : ContinuousOn (kernelTransform ν K k f) K := by
  obtain ⟨C, -, hC⟩ := hd.exists_bound
  show ContinuousOn (fun x => ∫ y in K, k x y * f y ∂ν) K
  refine continuousOn_of_dominated (bound := fun y => C * |f y|)
    (fun x hx => (hd.integrable_mul hx hf).aestronglyMeasurable) (fun x hx => ?_)
    (hf.abs.const_mul C) ?_
  · filter_upwards [ae_restrict_mem hd.measurableSet] with y hy
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC x hx y hy) (abs_nonneg _)
  · filter_upwards [ae_restrict_mem hd.measurableSet] with y hy
    exact (hd.continuousOn_left hy).mul continuousOn_const

theorem abs_kernelTransform_le (hd : IsL2KernelData ν K k) {C : ℝ}
    (hC : ∀ x ∈ K, ∀ y ∈ K, |k x y| ≤ C) {x : ℂ} (hx : x ∈ K) {f : ℂ → ℝ}
    (hf : Integrable f (ν.restrict K)) :
    |kernelTransform ν K k f x| ≤ C * ∫ y in K, |f y| ∂ν := by
  unfold kernelTransform
  refine abs_integral_le_integral_abs.trans ?_
  rw [← integral_const_mul]
  refine integral_mono_ae (hd.integrable_mul hx hf).abs (hf.abs.const_mul C) ?_
  filter_upwards [ae_restrict_mem hd.measurableSet] with y hy
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hC x hx y hy) (abs_nonneg _)

theorem aestronglyMeasurable_kernelTransform (hd : IsL2KernelData ν K k) {f : ℂ → ℝ}
    (hf : Integrable f (ν.restrict K)) : AEStronglyMeasurable (kernelTransform ν K k f) ν := by
  have h := (hd.continuousOn_kernelTransform hf).aestronglyMeasurable (μ := ν) hd.measurableSet
  rwa [hd.restrict_eq] at h

theorem integrable_kernelTransform [IsFiniteMeasure ν] (hd : IsL2KernelData ν K k) {f : ℂ → ℝ}
    (hf : Integrable f (ν.restrict K)) : Integrable (kernelTransform ν K k f) ν := by
  obtain ⟨C, -, hC⟩ := hd.exists_bound
  refine Integrable.of_bound (hd.aestronglyMeasurable_kernelTransform hf)
    (C * ∫ y in K, |f y| ∂ν) ?_
  filter_upwards [hd.ae_mem] with x hx
  rw [Real.norm_eq_abs]
  exact hd.abs_kernelTransform_le hC hx hf

theorem memLp_kernelTransform [IsFiniteMeasure ν] (hd : IsL2KernelData ν K k) {f : ℂ → ℝ}
    (hf : MemLp f 2 ν) : MemLp (kernelTransform ν K k f) 2 ν := by
  have hfi : Integrable f (ν.restrict K) := (hf.integrable one_le_two).integrableOn
  obtain ⟨C, -, hC⟩ := hd.exists_bound
  refine MemLp.of_bound (hd.aestronglyMeasurable_kernelTransform hfi)
    (C * ∫ y in K, |f y| ∂ν) ?_
  filter_upwards [hd.ae_mem] with x hx
  rw [Real.norm_eq_abs]
  exact hd.abs_kernelTransform_le hC hx hfi

theorem kernelTransform_add (hd : IsL2KernelData ν K k) {x : ℂ} (hx : x ∈ K) {f g : ℂ → ℝ}
    (hf : Integrable f (ν.restrict K)) (hg : Integrable g (ν.restrict K)) :
    kernelTransform ν K k (f + g) x = kernelTransform ν K k f x + kernelTransform ν K k g x := by
  unfold kernelTransform
  simp only [Pi.add_apply, mul_add]
  exact integral_add (hd.integrable_mul hx hf) (hd.integrable_mul hx hg)

/-! ### Schur's test -/

/-- **Schur's test.** If the rows and the columns of `|k|` have mass at most `R` on `K`, then
`∫ (T f)² dν ≤ R² ∫ f² dν`. -/
theorem integral_sq_kernelTransform_le [IsFiniteMeasure ν] (hd : IsL2KernelData ν K k) {R : ℝ}
    (hR : 0 ≤ R) (hrow : ∀ x ∈ K, ∫ y in K, |k x y| ∂ν ≤ R)
    (hcol : ∀ y ∈ K, ∫ x in K, |k x y| ∂ν ≤ R) {f : ℂ → ℝ} (hf : MemLp f 2 ν) :
    ∫ x, kernelTransform ν K k f x ^ 2 ∂ν ≤ R * R * ∫ x, f x ^ 2 ∂ν := by
  have hKm := hd.measurableSet
  have hfi : Integrable f (ν.restrict K) := (hf.integrable one_le_two).integrableOn
  have hf2 : Integrable (fun y => f y ^ 2) (ν.restrict K) := hf.integrable_sq.integrableOn
  have hdA := hd.abs
  -- the Cauchy–Schwarz inequality for the weights `|k(x, ·)|`
  have hcs : ∀ x ∈ K, kernelTransform ν K k f x ^ 2 ≤
      R * kernelTransform ν K (fun x y => |k x y|) (fun y => f y ^ 2) x := by
    intro x hx
    have hia : Integrable (fun y => |k x y|) (ν.restrict K) := hdA.integrable_right hx
    have hib : Integrable (fun y => |k x y| * |f y|) (ν.restrict K) :=
      hdA.integrable_mul hx hfi.abs
    have hid : Integrable (fun y => |k x y| * f y ^ 2) (ν.restrict K) := hdA.integrable_mul hx hf2
    have h1 : |kernelTransform ν K k f x| ≤ ∫ y in K, |k x y| * |f y| ∂ν := by
      unfold kernelTransform
      refine abs_integral_le_integral_abs.trans (le_of_eq ?_)
      congr 1
      ext y
      rw [abs_mul]
    have key : ∀ c : ℝ, 0 ≤ (∫ y in K, |k x y| ∂ν) * (c * c) +
        (-2 * ∫ y in K, |k x y| * |f y| ∂ν) * c + ∫ y in K, |k x y| * f y ^ 2 ∂ν := by
      intro c
      have e1 : ∫ y in K, |k x y| * (|f y| - c) ^ 2 ∂ν =
          ∫ y in K, (|k x y| * f y ^ 2 - 2 * c * (|k x y| * |f y|) + c * c * |k x y|) ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only
        rw [← sq_abs (f y)]
        ring
      have e2 : ∫ y in K, (|k x y| * f y ^ 2 - 2 * c * (|k x y| * |f y|) + c * c * |k x y|) ∂ν =
          (∫ y in K, |k x y| * f y ^ 2 ∂ν) - 2 * c * (∫ y in K, |k x y| * |f y| ∂ν) +
            c * c * ∫ y in K, |k x y| ∂ν := by
        have i1 : Integrable (fun y => |k x y| * f y ^ 2 - 2 * c * (|k x y| * |f y|))
            (ν.restrict K) := hid.sub (hib.const_mul (2 * c))
        rw [integral_add i1 (hia.const_mul (c * c)), integral_sub hid (hib.const_mul (2 * c)),
          integral_const_mul, integral_const_mul]
      have hnn : 0 ≤ ∫ y in K, |k x y| * (|f y| - c) ^ 2 ∂ν :=
        setIntegral_nonneg hKm fun y _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
      rw [e1, e2] at hnn
      linarith
    have hdisc := discrim_le_zero key
    unfold discrim at hdisc
    have ha : ∫ y in K, |k x y| ∂ν ≤ R := hrow x hx
    have hd0 : 0 ≤ ∫ y in K, |k x y| * f y ^ 2 ∂ν :=
      setIntegral_nonneg hKm fun y _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
    have hb2 : (∫ y in K, |k x y| * |f y| ∂ν) ^ 2 ≤
        (∫ y in K, |k x y| ∂ν) * ∫ y in K, |k x y| * f y ^ 2 ∂ν := by nlinarith
    calc kernelTransform ν K k f x ^ 2 = |kernelTransform ν K k f x| ^ 2 := (sq_abs _).symm
      _ ≤ (∫ y in K, |k x y| * |f y| ∂ν) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ ≤ (∫ y in K, |k x y| ∂ν) * ∫ y in K, |k x y| * f y ^ 2 ∂ν := hb2
      _ ≤ R * kernelTransform ν K (fun x y => |k x y|) (fun y => f y ^ 2) x :=
        mul_le_mul_of_nonneg_right ha hd0
  -- integrate and exchange the integrals
  obtain ⟨C, -, hC⟩ := hd.exists_bound
  have hmem : ∀ᵐ z ∂((ν.restrict K).prod (ν.restrict K)), z ∈ K ×ˢ K := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (hKm.prod hKm)
  have hprod : Integrable (Function.uncurry fun x y => |k x y| * f y ^ 2)
      ((ν.restrict K).prod (ν.restrict K)) := by
    have hm : AEStronglyMeasurable (fun z : ℂ × ℂ => |k z.1 z.2|)
        ((ν.restrict K).prod (ν.restrict K)) := by
      rw [Measure.prod_restrict]
      exact hd.continuousOn.abs.aestronglyMeasurable (hKm.prod hKm)
    have h := (hf2.comp_snd (ν.restrict K)).bdd_mul hm (c := C) (by
      filter_upwards [hmem] with z hz
      rw [Real.norm_eq_abs, abs_abs]
      exact hC z.1 hz.1 z.2 hz.2)
    exact h
  have hcolm : ∀ y ∈ K, (∫ x in K, |k x y| ∂ν) * f y ^ 2 ≤ R * f y ^ 2 := fun y hy =>
    mul_le_mul_of_nonneg_right (hcol y hy) (sq_nonneg _)
  calc ∫ x, kernelTransform ν K k f x ^ 2 ∂ν
      ≤ ∫ x, R * kernelTransform ν K (fun x y => |k x y|) (fun y => f y ^ 2) x ∂ν := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
          ((hdA.integrable_kernelTransform hf2).const_mul R) ?_
        filter_upwards [hd.ae_mem] with x hx using hcs x hx
    _ = R * ∫ x in K, ∫ y in K, |k x y| * f y ^ 2 ∂ν ∂ν := by
        rw [integral_const_mul, ← hd.setIntegral_eq]
        rfl
    _ = R * ∫ y in K, ∫ x in K, |k x y| * f y ^ 2 ∂ν ∂ν := by
        rw [integral_integral_swap hprod]
    _ = R * ∫ y in K, (∫ x in K, |k x y| ∂ν) * f y ^ 2 ∂ν := by
        simp_rw [integral_mul_const]
    _ ≤ R * ∫ y in K, R * f y ^ 2 ∂ν := by
        refine mul_le_mul_of_nonneg_left ?_ hR
        refine integral_mono_of_nonneg ?_ (hf2.const_mul R) ?_
        · filter_upwards [ae_restrict_mem hKm] with y hy
          exact mul_nonneg (setIntegral_nonneg hKm fun x _ => abs_nonneg _) (sq_nonneg _)
        · filter_upwards [ae_restrict_mem hKm] with y hy using hcolm y hy
    _ = R * R * ∫ x, f x ^ 2 ∂ν := by
        rw [integral_const_mul, hd.setIntegral_eq, mul_assoc]

end IsL2KernelData

/-- In `L²` of a real measure, `‖g‖² = ∫ g²`. -/
theorem l2_norm_sq_eq_integral_sq {ν : Measure ℂ} (g : Lp ℝ 2 ν) :
    ‖g‖ ^ 2 = ∫ x, (g : ℂ → ℝ) x ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Real.inner_apply, sq]

/-- In `L²` of a real measure, `⟪u, v⟫ = ∫ u v`. -/
theorem l2_inner_eq_integral_mul {ν : Measure ℂ} (u v : Lp ℝ 2 ν) :
    ⟪u, v⟫_ℝ = ∫ x, (u : ℂ → ℝ) x * (v : ℂ → ℝ) x ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Real.inner_apply]

namespace IsL2KernelData

variable {ν : Measure ℂ} [IsFiniteMeasure ν] {K : Set ℂ} {k : ℂ → ℂ → ℝ}

/-- The integral transform as a linear map of `L²(ν)`. -/
noncomputable def kernelL2LinearMap (hd : IsL2KernelData ν K k) : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 ν where
  toFun f := (hd.memLp_kernelTransform (Lp.memLp f)).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    have hfi : Integrable (f : ℂ → ℝ) (ν.restrict K) :=
      ((Lp.memLp f).integrable one_le_two).integrableOn
    have hgi : Integrable (g : ℂ → ℝ) (ν.restrict K) :=
      ((Lp.memLp g).integrable one_le_two).integrableOn
    filter_upwards [hd.ae_mem] with x hx
    rw [kernelTransform_congr_ae (Lp.coeFn_add f g), Pi.add_apply]
    exact hd.kernelTransform_add hx hfi hgi
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (Eventually.of_forall fun x => ?_)
    rw [kernelTransform_congr_ae (Lp.coeFn_smul c f), Pi.smul_apply, smul_eq_mul]
    exact kernelTransform_const_smul c _ x

/-- The bound `C ν(K)` of the rows and columns of `|k|`, for the bound `C` of `|k|` on `K × K`. -/
noncomputable def opBound (hd : IsL2KernelData ν K k) : ℝ :=
  Classical.choose hd.exists_bound * ν.real K

omit [IsFiniteMeasure ν] in
theorem opBound_nonneg (hd : IsL2KernelData ν K k) : 0 ≤ hd.opBound :=
  mul_nonneg (Classical.choose_spec hd.exists_bound).1 measureReal_nonneg

theorem row_le_opBound (hd : IsL2KernelData ν K k) :
    ∀ x ∈ K, ∫ y in K, |k x y| ∂ν ≤ hd.opBound := by
  intro x hx
  have hC := (Classical.choose_spec hd.exists_bound).2
  calc ∫ y in K, |k x y| ∂ν ≤ ∫ _ in K, Classical.choose hd.exists_bound ∂ν :=
        setIntegral_mono_on (hd.abs.integrable_right hx) (integrable_const _) hd.measurableSet
          fun y hy => hC x hx y hy
    _ = hd.opBound := by rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl

theorem col_le_opBound (hd : IsL2KernelData ν K k) :
    ∀ y ∈ K, ∫ x in K, |k x y| ∂ν ≤ hd.opBound := by
  intro y hy
  have hC := (Classical.choose_spec hd.exists_bound).2
  calc ∫ x in K, |k x y| ∂ν ≤ ∫ _ in K, Classical.choose hd.exists_bound ∂ν :=
        setIntegral_mono_on (hd.swap.abs.integrable_right hy) (integrable_const _) hd.measurableSet
          fun x hx => hC x hx y hy
    _ = hd.opBound := by rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl

/-- Schur's test for the operator on `L²(ν)`. -/
theorem norm_toLp_kernelTransform_le (hd : IsL2KernelData ν K k) {R : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ x ∈ K, ∫ y in K, |k x y| ∂ν ≤ R) (hcol : ∀ y ∈ K, ∫ x in K, |k x y| ∂ν ≤ R)
    (f : Lp ℝ 2 ν) : ‖(hd.memLp_kernelTransform (Lp.memLp f)).toLp _‖ ≤ R * ‖f‖ := by
  have h := hd.integral_sq_kernelTransform_le hR hrow hcol (Lp.memLp f)
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg _)) two_ne_zero,
    mul_pow, l2_norm_sq_eq_integral_sq, l2_norm_sq_eq_integral_sq]
  have hc : ∫ x, ((hd.memLp_kernelTransform (Lp.memLp f)).toLp _ : ℂ → ℝ) x ^ 2 ∂ν =
      ∫ x, kernelTransform ν K k f x ^ 2 ∂ν :=
    integral_congr_ae ((MemLp.coeFn_toLp (hd.memLp_kernelTransform (Lp.memLp f))).mono
      fun x hx => by simp only [hx])
  rw [hc, sq R]
  exact h

end IsL2KernelData

open scoped Classical in
/-- The integral operator `f ↦ ∫_K k(·, y) f(y) dν(y)` of `k` on `L²(ν)`, for kernel data
`IsL2KernelData ν K k`, and `0` otherwise. -/
noncomputable def kernelL2Operator (ν : Measure ℂ) [IsFiniteMeasure ν] (K : Set ℂ)
    (k : ℂ → ℂ → ℝ) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  if hd : IsL2KernelData ν K k then
    hd.kernelL2LinearMap.mkContinuous hd.opBound fun f =>
      hd.norm_toLp_kernelTransform_le hd.opBound_nonneg hd.row_le_opBound hd.col_le_opBound f
  else 0

namespace IsL2KernelData

variable {ν : Measure ℂ} [IsFiniteMeasure ν] {K : Set ℂ} {k : ℂ → ℂ → ℝ}

theorem kernelL2Operator_apply (hd : IsL2KernelData ν K k) (f : Lp ℝ 2 ν) :
    kernelL2Operator ν K k f = (hd.memLp_kernelTransform (Lp.memLp f)).toLp _ := by
  unfold kernelL2Operator
  split_ifs
  rfl

/-- The operator is the integral transform, almost everywhere. -/
theorem coeFn_kernelL2Operator (hd : IsL2KernelData ν K k) (f : Lp ℝ 2 ν) :
    (kernelL2Operator ν K k f : ℂ → ℝ) =ᵐ[ν] kernelTransform ν K k f := by
  rw [hd.kernelL2Operator_apply f]
  exact MemLp.coeFn_toLp _

/-- **Schur's test** for `kernelL2Operator`. -/
theorem norm_kernelL2Operator_apply_le (hd : IsL2KernelData ν K k) {R : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ x ∈ K, ∫ y in K, |k x y| ∂ν ≤ R) (hcol : ∀ y ∈ K, ∫ x in K, |k x y| ∂ν ≤ R)
    (f : Lp ℝ 2 ν) : ‖kernelL2Operator ν K k f‖ ≤ R * ‖f‖ := by
  rw [hd.kernelL2Operator_apply f]
  exact hd.norm_toLp_kernelTransform_le hR hrow hcol f

theorem integrable_coe (f : Lp ℝ 2 ν) : Integrable (f : ℂ → ℝ) (ν.restrict K) :=
  ((Lp.memLp f).integrable one_le_two).integrableOn

/-- **A symmetric kernel gives a symmetric operator.** -/
theorem inner_kernelL2Operator_comm (hd : IsL2KernelData ν K k)
    (hsym : ∀ x ∈ K, ∀ y ∈ K, k x y = k y x) (f g : Lp ℝ 2 ν) :
    ⟪kernelL2Operator ν K k f, g⟫_ℝ = ⟪f, kernelL2Operator ν K k g⟫_ℝ := by
  have hKm := hd.measurableSet
  obtain ⟨C, -, hC⟩ := hd.exists_bound
  have hfi := integrable_coe (K := K) f
  have hgi := integrable_coe (K := K) g
  have hmem : ∀ᵐ z ∂((ν.restrict K).prod (ν.restrict K)), z ∈ K ×ˢ K := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (hKm.prod hKm)
  have hprod : Integrable (Function.uncurry fun x y => k x y * (f : ℂ → ℝ) y * (g : ℂ → ℝ) x)
      ((ν.restrict K).prod (ν.restrict K)) := by
    have hm : AEStronglyMeasurable (fun z : ℂ × ℂ => k z.1 z.2)
        ((ν.restrict K).prod (ν.restrict K)) := by
      rw [Measure.prod_restrict]
      exact hd.continuousOn.aestronglyMeasurable (hKm.prod hKm)
    have h := (hgi.mul_prod hfi).bdd_mul hm (c := C) (by
      filter_upwards [hmem] with z hz
      rw [Real.norm_eq_abs]
      exact hC z.1 hz.1 z.2 hz.2)
    refine h.congr (Eventually.of_forall fun z => ?_)
    show k z.1 z.2 * ((g : ℂ → ℝ) z.1 * (f : ℂ → ℝ) z.2) =
      k z.1 z.2 * (f : ℂ → ℝ) z.2 * (g : ℂ → ℝ) z.1
    ring
  have hL : ∫ x, (kernelL2Operator ν K k f : ℂ → ℝ) x * (g : ℂ → ℝ) x ∂ν =
      ∫ x in K, ∫ y in K, k x y * (f : ℂ → ℝ) y * (g : ℂ → ℝ) x ∂ν ∂ν := by
    rw [← hd.setIntegral_eq]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (hd.coeFn_kernelL2Operator f)] with x hx
    rw [hx, kernelTransform, ← integral_mul_const]
  have hR : ∫ y, (f : ℂ → ℝ) y * (kernelL2Operator ν K k g : ℂ → ℝ) y ∂ν =
      ∫ y in K, ∫ x in K, k x y * (f : ℂ → ℝ) y * (g : ℂ → ℝ) x ∂ν ∂ν := by
    rw [← hd.setIntegral_eq]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (hd.coeFn_kernelL2Operator g), ae_restrict_mem hKm]
      with y hy hyK
    rw [hy, kernelTransform, ← integral_const_mul]
    refine setIntegral_congr_fun hKm fun x hx => ?_
    rw [hsym y hyK x hx]
    ring
  rw [l2_inner_eq_integral_mul, l2_inner_eq_integral_mul, hL, hR]
  exact integral_integral_swap hprod

/-- **Composition.** If `k₃(x, y) = ∫_K k₁(x, z) k₂(z, y) dν(z)` on `K × K`, the operator of `k₃`
is the composition of the operators of `k₁` and `k₂`. -/
theorem kernelL2Operator_eq_comp {k₁ k₂ k₃ : ℂ → ℂ → ℝ} (hd₁ : IsL2KernelData ν K k₁)
    (hd₂ : IsL2KernelData ν K k₂) (hd₃ : IsL2KernelData ν K k₃)
    (hck : ∀ x ∈ K, ∀ y ∈ K, k₃ x y = ∫ z in K, k₁ x z * k₂ z y ∂ν) :
    kernelL2Operator ν K k₃ = (kernelL2Operator ν K k₁).comp (kernelL2Operator ν K k₂) := by
  have hKm := hd₁.measurableSet
  obtain ⟨C₁, -, hC₁⟩ := hd₁.exists_bound
  obtain ⟨C₂, hC₂0, hC₂⟩ := hd₂.exists_bound
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  rw [ContinuousLinearMap.comp_apply]
  filter_upwards [hd₃.coeFn_kernelL2Operator f,
    hd₁.coeFn_kernelL2Operator (kernelL2Operator ν K k₂ f), hd₁.ae_mem] with x h3 h1 hx
  rw [h3, h1, kernelTransform_congr_ae (hd₂.coeFn_kernelL2Operator f)]
  unfold kernelTransform
  have hfi := integrable_coe (K := K) f
  have hmem : ∀ᵐ z ∂((ν.restrict K).prod (ν.restrict K)), z ∈ K ×ˢ K := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (hKm.prod hKm)
  have hprod : Integrable (Function.uncurry fun z y => k₁ x z * k₂ z y * (f : ℂ → ℝ) y)
      ((ν.restrict K).prod (ν.restrict K)) := by
    have hc : ContinuousOn (fun q : ℂ × ℂ => k₁ x q.1 * k₂ q.1 q.2) (K ×ˢ K) :=
      ((hd₁.continuousOn_right hx).comp continuousOn_fst fun q hq => hq.1).mul hd₂.continuousOn
    have hm : AEStronglyMeasurable (fun q : ℂ × ℂ => k₁ x q.1 * k₂ q.1 q.2)
        ((ν.restrict K).prod (ν.restrict K)) := by
      rw [Measure.prod_restrict]
      exact hc.aestronglyMeasurable (hKm.prod hKm)
    exact (hfi.comp_snd (ν.restrict K)).bdd_mul hm (c := C₁ * C₂) (by
      filter_upwards [hmem] with q hq
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hC₁ x hx q.1 hq.1) (hC₂ q.1 hq.1 q.2 hq.2) (abs_nonneg _)
        ((abs_nonneg _).trans (hC₁ x hx q.1 hq.1)))
  calc ∫ y in K, k₃ x y * (f : ℂ → ℝ) y ∂ν
      = ∫ y in K, ∫ z in K, k₁ x z * k₂ z y * (f : ℂ → ℝ) y ∂ν ∂ν := by
        refine setIntegral_congr_fun hKm fun y hy => ?_
        rw [hck x hx y hy, ← integral_mul_const]
    _ = ∫ z in K, ∫ y in K, k₁ x z * k₂ z y * (f : ℂ → ℝ) y ∂ν ∂ν :=
        (integral_integral_swap hprod).symm
    _ = ∫ z in K, k₁ x z * ∫ y in K, k₂ z y * (f : ℂ → ℝ) y ∂ν ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only
        rw [← integral_const_mul]
        congr 1
        ext y
        ring

/-- A nonnegative kernel preserves positivity. -/
theorem ae_nonneg_kernelL2Operator (hd : IsL2KernelData ν K k)
    (hk0 : ∀ x ∈ K, ∀ y ∈ K, 0 ≤ k x y) {f : Lp ℝ 2 ν} (hf : 0 ≤ᵐ[ν] (f : ℂ → ℝ)) :
    0 ≤ᵐ[ν] (kernelL2Operator ν K k f : ℂ → ℝ) := by
  filter_upwards [hd.coeFn_kernelL2Operator f, hd.ae_mem] with x h hx
  rw [h, Pi.zero_apply]
  unfold kernelTransform
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_restrict_mem hd.measurableSet, ae_restrict_of_ae hf] with y hy hfy
  exact mul_nonneg (hk0 x hx y hy) hfy

/-- A nonnegative kernel whose rows have mass at most `1` maps `0 ≤ f ≤ 1` to `T f ≤ 1`. -/
theorem ae_kernelL2Operator_le_one (hd : IsL2KernelData ν K k)
    (hk0 : ∀ x ∈ K, ∀ y ∈ K, 0 ≤ k x y) (hrow : ∀ x ∈ K, ∫ y in K, k x y ∂ν ≤ 1)
    {f : Lp ℝ 2 ν} (hf : ∀ᵐ x ∂ν, 0 ≤ (f : ℂ → ℝ) x ∧ (f : ℂ → ℝ) x ≤ 1) :
    ∀ᵐ x ∂ν, (kernelL2Operator ν K k f : ℂ → ℝ) x ≤ 1 := by
  filter_upwards [hd.coeFn_kernelL2Operator f, hd.ae_mem] with x h hx
  rw [h]
  unfold kernelTransform
  refine le_trans ?_ (hrow x hx)
  refine integral_mono_ae (hd.integrable_mul hx (integrable_coe f)) (hd.integrable_right hx) ?_
  filter_upwards [ae_restrict_mem hd.measurableSet, ae_restrict_of_ae hf] with y hy hfy
  exact mul_le_of_le_one_right (hk0 x hx y hy) hfy.2

end IsL2KernelData

end HarmonicBalls
