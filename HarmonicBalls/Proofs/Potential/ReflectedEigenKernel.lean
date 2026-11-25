import HarmonicBalls.Proofs.Potential.ReflectedGreenSpectral

/-!
# The eigenfunction kernel of the centered Green operator

Let `ν` be a probability measure carried by `K₀` with upper power bounds, and fix an eigenbasis of
the centered Green operator `G` (`GreenEigenData`): a Hilbert basis `1, φ_i` of `L²(ν)` with
`G φ_i = μ_i φ_i`, `μ_i > 0`. Write `λ_i = 1/μ_i`.

* The continuous representatives `ϕ_i = μ_i⁻¹ ⟪Q g(x, ·) - Q V 1, φ_i⟫` on `K₀` (`eigenfun`)
  satisfy `φ_i = ϕ_i` `ν`-a.e. (`coeFn_basis_eq_eigenfun`); by Bessel's inequality
  `∑_i μ_i² ϕ_i(x)² ≤ B²` for `x ∈ K₀`, so `|ϕ_i| ≤ B λ_i` and `∑_i μ_i² ≤ B²`
  (`summable_eig_sq`).
* The kernel `p(t, x, y) = 1 + ∑_i e^{-λ_i t} ϕ_i(x) ϕ_i(y)` (`eigenKernel`) converges uniformly
  on `[ε, ∞) × K₀ × K₀` (its terms are at most `24 B² μ_i² / ε⁴`, since `e^{-s} ≤ 24 / s⁴`), so it
  is jointly continuous on `(0, ∞) × K₀ × K₀` (`continuousOn_eigenKernel`), and by orthonormality
  `∫ p(t, x, y) ν(dy) = 1` and `∫ p(t, x, y) ϕ_j(y) ν(dy) = e^{-λ_j t} ϕ_j(x)`
  (`integral_eigenKernel_mul_eigenfun`).
-/

open MeasureTheory Set Filter Topology Module Metric
open scoped ENNReal NNReal InnerProductSpace

namespace HarmonicBalls

variable {ν : Measure ℂ} [IsProbabilityMeasure ν]

/-- An eigenbasis of the centered Green operator. -/
structure GreenEigenData (hν : IsUpperRegularSpeed ν) where
  ι : Type
  countable : Countable ι
  basis : HilbertBasis (Option ι) ℝ (Lp ℝ 2 ν)
  eig : ι → ℝ
  basis_none : basis none = oneLp ν
  eig_pos : ∀ i, 0 < eig i
  apply_basis : ∀ i, centeredGreenOperator hν (basis (some i)) = eig i • basis (some i)

theorem IsUpperRegularSpeed.nonempty_greenEigenData (hν : IsUpperRegularSpeed ν) :
    Nonempty (GreenEigenData hν) := by
  obtain ⟨ι, hι, b, μ, h1, h2⟩ := hν.exists_greenEigenbasis
  exact ⟨⟨ι, hι, b, μ, h1, fun i => (h2 i).1, fun i => (h2 i).2⟩⟩

namespace GreenEigenData

variable {hν : IsUpperRegularSpeed ν} (E : GreenEigenData hν)

instance : Countable E.ι := E.countable

/-- The coefficient `a_i(x) = ⟪Q g(x, ·) - Q V 1, φ_i⟫` on `K₀`, extended by `0`. -/
noncomputable def coeff (i : E.ι) (x : ℂ) : ℝ :=
  rowEval (centeredGreenRow hν) (E.basis (some i)) x

/-- The continuous representative `ϕ_i = μ_i⁻¹ a_i` of the eigenvector `φ_i`. -/
noncomputable def eigenfun (i : E.ι) (x : ℂ) : ℝ := (E.eig i)⁻¹ * E.coeff i x

theorem orthonormal_basis_some : Orthonormal ℝ fun i : E.ι => E.basis (some i) :=
  E.basis.orthonormal.comp _ (Option.some_injective _)

theorem norm_basis_some (i : E.ι) : ‖E.basis (some i)‖ = 1 := E.orthonormal_basis_some.1 i

theorem inner_oneLp_basis_some (i : E.ι) : ⟪oneLp ν, E.basis (some i)⟫_ℝ = 0 := by
  rw [← E.basis_none]
  exact E.basis.orthonormal.2 (Option.some_ne_none i).symm

theorem continuousOn_coeff (i : E.ι) : ContinuousOn (E.coeff i) (closedSquare 0 1) :=
  continuousOn_rowEval hν.isRowFamily_centeredGreenRow _

theorem continuousOn_eigenfun (i : E.ι) : ContinuousOn (E.eigenfun i) (closedSquare 0 1) :=
  continuousOn_const.mul (E.continuousOn_coeff i)

theorem eigenfun_of_notMem (i : E.ι) {x : ℂ} (hx : x ∉ closedSquare (0 : ℂ) 1) :
    E.eigenfun i x = 0 := by
  simp [eigenfun, coeff, rowEval, hx]

theorem measurable_eigenfun (i : E.ι) : Measurable (E.eigenfun i) := by
  classical
  have h : E.eigenfun i = (closedSquare 0 1).piecewise (E.eigenfun i) 0 := by
    funext x
    by_cases hx : x ∈ closedSquare (0 : ℂ) 1
    · simp [hx]
    · simp [hx, E.eigenfun_of_notMem i hx]
  rw [h]
  exact (E.continuousOn_eigenfun i).measurable_piecewise continuousOn_const
    measurableSet_closedSquare_zero_one

theorem coeff_eq (i : E.ι) {x : ℂ} (hx : x ∈ closedSquare (0 : ℂ) 1) :
    E.coeff i x = ⟪E.basis (some i), centeredGreenRow hν x⟫_ℝ := by
  rw [coeff, rowEval_of_mem hx, real_inner_comm]

/-- `φ_i = ϕ_i` almost everywhere. -/
theorem coeFn_basis_eq_eigenfun (i : E.ι) :
    (E.basis (some i) : ℂ → ℝ) =ᵐ[ν] E.eigenfun i := by
  have h1 := coeFn_rowOperator hν.isRowFamily_centeredGreenRow (E.basis (some i))
  rw [← centeredGreenOperator_eq_rowOperator, E.apply_basis i] at h1
  have h2 := Lp.coeFn_smul (E.eig i) (E.basis (some i))
  have hne := (E.eig_pos i).ne'
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx2, Pi.smul_apply, smul_eq_mul] at hx1
  unfold eigenfun coeff
  rw [← hx1, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- The bound `B` of the rows of `G`. -/
theorem exists_rowBound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ closedSquare (0 : ℂ) 1,
    ‖centeredGreenRow hν x‖ ≤ B :=
  hν.isRowFamily_centeredGreenRow.bound

/-- **Bessel's inequality for the coefficients**: `∑_i a_i(x)² ≤ ‖Q g(x, ·) - Q V 1‖²`. -/
theorem summable_coeff_sq {x : ℂ} (hx : x ∈ closedSquare (0 : ℂ) 1) :
    Summable (fun i => E.coeff i x ^ 2) ∧
      ∑' i, E.coeff i x ^ 2 ≤ ‖centeredGreenRow hν x‖ ^ 2 := by
  have hs := E.orthonormal_basis_some.inner_products_summable (x := centeredGreenRow hν x)
  have hle := E.orthonormal_basis_some.tsum_inner_products_le (x := centeredGreenRow hν x)
  have e : (fun i => ‖⟪E.basis (some i), centeredGreenRow hν x⟫_ℝ‖ ^ 2) =
      fun i => E.coeff i x ^ 2 := by
    funext i
    rw [E.coeff_eq i hx, Real.norm_eq_abs, sq_abs]
  rw [e] at hs hle
  exact ⟨hs, hle⟩

theorem abs_coeff_le (i : E.ι) {x : ℂ} (hx : x ∈ closedSquare (0 : ℂ) 1) :
    |E.coeff i x| ≤ ‖centeredGreenRow hν x‖ := by
  rw [E.coeff_eq i hx]
  exact (abs_real_inner_le_norm _ _).trans (by rw [E.norm_basis_some, one_mul])

theorem abs_coeff_le' {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ closedSquare (0 : ℂ) 1, ‖centeredGreenRow hν x‖ ≤ B) (i : E.ι) (x : ℂ) :
    |E.coeff i x| ≤ B := by
  by_cases hx : x ∈ closedSquare (0 : ℂ) 1
  · exact (E.abs_coeff_le i hx).trans (hB x hx)
  · simp [coeff, rowEval, hx, hB0]

theorem coeff_eq_mul_eigenfun (i : E.ι) (x : ℂ) : E.coeff i x = E.eig i * E.eigenfun i x := by
  unfold eigenfun
  rw [← mul_assoc, mul_inv_cancel₀ (E.eig_pos i).ne', one_mul]

open Classical in
/-- `∫ ϕ_i ϕ_j dν = δ_{ij}` and `∫ ϕ_i dν = 0`. -/
theorem integral_eigenfun_mul (i j : E.ι) :
    ∫ y, E.eigenfun i y * E.eigenfun j y ∂ν = if i = j then 1 else 0 := by
  classical
  have h := (orthonormal_iff_ite.1 E.orthonormal_basis_some) i j
  rw [l2_inner_eq_integral_mul] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [E.coeFn_basis_eq_eigenfun i, E.coeFn_basis_eq_eigenfun j] with y hi hj
  rw [hi, hj]

theorem integral_eigenfun (i : E.ι) : ∫ y, E.eigenfun i y ∂ν = 0 := by
  have h := E.inner_oneLp_basis_some i
  rw [inner_oneLp_left] at h
  rw [← h]
  exact integral_congr_ae (E.coeFn_basis_eq_eigenfun i).symm

theorem integral_coeff_sq (i : E.ι) : ∫ y, E.coeff i y ^ 2 ∂ν = E.eig i ^ 2 := by
  have h := E.integral_eigenfun_mul i i
  rw [ite_eq_left rfl] at h
  calc ∫ y, E.coeff i y ^ 2 ∂ν = ∫ y, E.eig i ^ 2 * (E.eigenfun i y * E.eigenfun i y) ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [E.coeff_eq_mul_eigenfun]
        ring
    _ = E.eig i ^ 2 := by rw [integral_const_mul, h, mul_one]

/-- **`∑_i μ_i² ≤ B²`.** -/
theorem summable_eig_sq {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ closedSquare (0 : ℂ) 1, ‖centeredGreenRow hν x‖ ≤ B) :
    Summable (fun i => E.eig i ^ 2) ∧ ∑' i, E.eig i ^ 2 ≤ B ^ 2 := by
  have hsum : ∀ F : Finset E.ι, ∑ i ∈ F, E.eig i ^ 2 ≤ B ^ 2 := by
    intro F
    have hint : ∀ i, Integrable (fun y => E.coeff i y ^ 2) ν := fun i =>
      Integrable.of_bound ((measurable_eigenfun E i).const_mul (E.eig i) |>.pow_const 2
        |>.aestronglyMeasurable |>.congr (Eventually.of_forall fun y => by
          simp only [E.coeff_eq_mul_eigenfun])) (B ^ 2)
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (E.abs_coeff_le' hB0 hB i y) 2)
    calc ∑ i ∈ F, E.eig i ^ 2 = ∫ y, ∑ i ∈ F, E.coeff i y ^ 2 ∂ν := by
          rw [integral_finsetSum _ fun i _ => hint i]
          exact Finset.sum_congr rfl fun i _ => (E.integral_coeff_sq i).symm
      _ ≤ ∫ _, B ^ 2 ∂ν := by
          refine integral_mono_ae (integrable_finsetSum _ fun i _ => hint i) (integrable_const _) ?_
          filter_upwards [hν.ae_mem] with y hy
          refine le_trans ?_ ((E.summable_coeff_sq hy).2.trans (pow_le_pow_left₀ (norm_nonneg _)
            (hB y hy) 2))
          exact (E.summable_coeff_sq hy).1.sum_le_tsum F fun i _ => sq_nonneg _
      _ = B ^ 2 := by simp
  have hs : Summable (fun i => E.eig i ^ 2) :=
    summable_of_sum_le (fun i => sq_nonneg _) hsum
  exact ⟨hs, hs.tsum_le_of_sum_le hsum⟩

/-! ### The kernel -/

/-- `e^{-s} ≤ 24 / s⁴` for `s > 0`. -/
theorem exp_neg_le_div_pow_four {s : ℝ} (hs : 0 < s) : Real.exp (-s) ≤ 24 / s ^ 4 := by
  have h := Real.pow_div_factorial_le_exp s hs.le 4
  rw [show (Nat.factorial 4 : ℝ) = 24 by norm_num [Nat.factorial]] at h
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  have : s ^ 4 ≤ 24 * Real.exp s := by
    have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 24)).1 h
    linarith
  linarith

/-- The eigenfunction kernel `p(t, x, y) = 1 + ∑_i e^{-t/μ_i} ϕ_i(x) ϕ_i(y)`. -/
noncomputable def eigenKernel (t : ℝ) (x y : ℂ) : ℝ :=
  1 + ∑' i, Real.exp (-(t / E.eig i)) * (E.eigenfun i x * E.eigenfun i y)

/-- **The bound of the terms**: `|e^{-t/μ_i} ϕ_i(x) ϕ_i(y)| ≤ 24 B² μ_i² / t⁴` for `t > 0`. -/
theorem abs_term_le {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ closedSquare (0 : ℂ) 1, ‖centeredGreenRow hν x‖ ≤ B) (i : E.ι) {t : ℝ}
    (ht : 0 < t) (x y : ℂ) :
    |Real.exp (-(t / E.eig i)) * (E.eigenfun i x * E.eigenfun i y)| ≤
      24 * B ^ 2 * E.eig i ^ 2 / t ^ 4 := by
  have hμ := E.eig_pos i
  have he := exp_neg_le_div_pow_four (div_pos ht hμ)
  have hx := E.abs_coeff_le' hB0 hB i x
  have hy := E.abs_coeff_le' hB0 hB i y
  unfold eigenfun
  rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hμ)]
  have hxy : |E.coeff i x| * |E.coeff i y| ≤ B ^ 2 := by
    rw [sq]; exact mul_le_mul hx hy (abs_nonneg _) hB0
  calc Real.exp (-(t / E.eig i)) * ((E.eig i)⁻¹ * |E.coeff i x| * ((E.eig i)⁻¹ * |E.coeff i y|))
      = Real.exp (-(t / E.eig i)) * ((E.eig i)⁻¹ ^ 2 * (|E.coeff i x| * |E.coeff i y|)) := by ring
    _ ≤ 24 / (t / E.eig i) ^ 4 * ((E.eig i)⁻¹ ^ 2 * B ^ 2) := by
        refine mul_le_mul he (mul_le_mul_of_nonneg_left hxy (by positivity)) (by positivity)
          (by positivity)
    _ = 24 * B ^ 2 * E.eig i ^ 2 / t ^ 4 := by
        have hμ0 : E.eig i ≠ 0 := hμ.ne'
        have ht0 : t ≠ 0 := ht.ne'
        field_simp

theorem summable_term {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ closedSquare (0 : ℂ) 1, ‖centeredGreenRow hν x‖ ≤ B) {t : ℝ} (ht : 0 < t)
    (x y : ℂ) :
    Summable fun i => Real.exp (-(t / E.eig i)) * (E.eigenfun i x * E.eigenfun i y) := by
  refine Summable.of_norm_bounded (g := fun i => 24 * B ^ 2 * E.eig i ^ 2 / t ^ 4) ?_ fun i => ?_
  · exact (((E.summable_eig_sq hB0 hB).1.mul_left (24 * B ^ 2)).div_const (t ^ 4)).congr fun i => by ring
  · rw [Real.norm_eq_abs]; exact E.abs_term_le hB0 hB i ht x y

/-- **Joint continuity of the kernel** on `(0, ∞) × K₀ × K₀`. -/
theorem continuousOn_eigenKernel :
    ContinuousOn (fun q : ℝ × ℂ × ℂ => E.eigenKernel q.1 q.2.1 q.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1) := by
  obtain ⟨B, hB0, hB⟩ := hν.isRowFamily_centeredGreenRow.bound
  intro q hq
  have ht0 : 0 < q.1 := hq.1
  have h2 : 0 < q.1 / 2 := by positivity
  set S : Set (ℝ × ℂ × ℂ) := Ici (q.1 / 2) ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1 with hS
  have hcont : ContinuousOn (fun q : ℝ × ℂ × ℂ => E.eigenKernel q.1 q.2.1 q.2.2) S := by
    refine continuousOn_const.add (continuousOn_tsum
      (u := fun i => 24 * B ^ 2 * E.eig i ^ 2 / (q.1 / 2) ^ 4) (fun i => ?_) ?_ ?_)
    · refine ((Real.continuous_exp.comp (continuous_fst.div_const _).neg).continuousOn).mul
        (ContinuousOn.mul ?_ ?_)
      · exact (E.continuousOn_eigenfun i).comp (f := fun q : ℝ × ℂ × ℂ => q.2.1)
          (by fun_prop) fun r hr => hr.2.1
      · exact (E.continuousOn_eigenfun i).comp (f := fun q : ℝ × ℂ × ℂ => q.2.2)
          (by fun_prop) fun r hr => hr.2.2
    · exact (((E.summable_eig_sq hB0 hB).1.mul_left (24 * B ^ 2)).div_const
        ((q.1 / 2) ^ 4)).congr fun i => by ring
    · intro i r hr
      have hr1 : q.1 / 2 ≤ r.1 := hr.1
      rw [Real.norm_eq_abs]
      refine (E.abs_term_le hB0 hB i (by linarith) r.2.1 r.2.2).trans ?_
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ h2.le hr1 4)
  refine (hcont q ⟨?_, hq.2⟩).mono_of_mem_nhdsWithin ?_
  · show q.1 / 2 ≤ q.1
    linarith
  · refine mem_nhdsWithin.2 ⟨Ioi (q.1 / 2) ×ˢ univ, isOpen_Ioi.prod isOpen_univ,
      ⟨show q.1 / 2 < q.1 by linarith, trivial⟩,
      fun r hr => ⟨show q.1 / 2 ≤ r.1 from le_of_lt hr.1.1, hr.2.2⟩⟩

theorem continuousOn_eigenKernel_right {t : ℝ} (ht : 0 < t) {x : ℂ}
    (hx : x ∈ closedSquare (0 : ℂ) 1) : ContinuousOn (E.eigenKernel t x) (closedSquare 0 1) :=
  E.continuousOn_eigenKernel.comp (f := fun y : ℂ => (t, x, y)) (by fun_prop)
    fun y hy => ⟨ht, hx, hy⟩

theorem abs_eigenKernel_sub_one_le {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ closedSquare (0 : ℂ) 1, ‖centeredGreenRow hν x‖ ≤ B) {t : ℝ} (ht : 0 < t)
    (x y : ℂ) :
    |E.eigenKernel t x y - 1| ≤ 24 * B ^ 2 * (∑' i, E.eig i ^ 2) / t ^ 4 := by
  have hs := E.summable_term hB0 hB ht x y
  have hs2 : Summable fun i => 24 * B ^ 2 * E.eig i ^ 2 / t ^ 4 :=
    (((E.summable_eig_sq hB0 hB).1.mul_left (24 * B ^ 2)).div_const (t ^ 4)).congr fun i => by ring
  unfold eigenKernel
  rw [add_sub_cancel_left]
  calc |∑' i, Real.exp (-(t / E.eig i)) * (E.eigenfun i x * E.eigenfun i y)|
      ≤ ∑' i, |Real.exp (-(t / E.eig i)) * (E.eigenfun i x * E.eigenfun i y)| := by
        have := norm_tsum_le_tsum_norm hs.norm
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' i, 24 * B ^ 2 * E.eig i ^ 2 / t ^ 4 :=
        Summable.tsum_le_tsum (fun i => E.abs_term_le hB0 hB i ht x y) hs.abs hs2
    _ = 24 * B ^ 2 * (∑' i, E.eig i ^ 2) / t ^ 4 := by
        rw [tsum_div_const, tsum_mul_left]

theorem integrable_eigenKernel_mul {t : ℝ} (ht : 0 < t) {x : ℂ}
    (hx : x ∈ closedSquare (0 : ℂ) 1) {g : ℂ → ℝ} (hg : ContinuousOn g (closedSquare 0 1))
    {C : ℝ} (hgC : ∀ y, |g y| ≤ C) :
    Integrable (fun y => (E.eigenKernel t x y - 1) * g y) ν ∧
      Integrable (fun y => E.eigenKernel t x y * g y) ν := by
  obtain ⟨B, hB0, hB⟩ := hν.isRowFamily_centeredGreenRow.bound
  have hrestr : ν.restrict (closedSquare 0 1) = ν := Measure.restrict_eq_self_of_ae_mem hν.ae_mem
  have hm : ∀ a : ℝ, AEStronglyMeasurable (fun y => (E.eigenKernel t x y - a) * g y) ν := by
    intro a
    have hc : ContinuousOn (fun y => (E.eigenKernel t x y - a) * g y) (closedSquare 0 1) :=
      ((E.continuousOn_eigenKernel_right ht hx).sub (continuousOn_const (c := a))).mul hg
    have h := hc.aestronglyMeasurable (μ := ν) measurableSet_closedSquare_zero_one
    rwa [hrestr] at h
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hgC 0)
  set D := 24 * B ^ 2 * (∑' i, E.eig i ^ 2) / t ^ 4 with hD
  have h1 : Integrable (fun y => (E.eigenKernel t x y - 1) * g y) ν :=
    Integrable.of_bound (hm 1) (D * C) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (E.abs_eigenKernel_sub_one_le hB0 hB ht x y) (hgC y) (abs_nonneg _)
        (by positivity))
  refine ⟨h1, ?_⟩
  have h2 := (hm 0)
  simp only [sub_zero] at h2
  refine Integrable.of_bound h2 ((D + 1) * C) (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  refine mul_le_mul ?_ (hgC y) (abs_nonneg _) (by positivity)
  have := E.abs_eigenKernel_sub_one_le hB0 hB ht x y
  rw [abs_le] at this ⊢
  constructor <;> linarith [this.1, this.2]

/-- **Orthonormality**: `∫ p(t, x, y) ϕ_j(y) ν(dy) = e^{-λ_j t} ϕ_j(x)` for `t > 0`, `x ∈ K₀`. -/
theorem integral_eigenKernel_mul_eigenfun {t : ℝ} (ht : 0 < t) {x : ℂ}
    (hx : x ∈ closedSquare (0 : ℂ) 1) (j : E.ι) :
    ∫ y, E.eigenKernel t x y * E.eigenfun j y ∂ν = Real.exp (-(t / E.eig j)) * E.eigenfun j x := by
  classical
  obtain ⟨B, hB0, hB⟩ := hν.isRowFamily_centeredGreenRow.bound
  have hj : ∀ y, |E.eigenfun j y| ≤ (E.eig j)⁻¹ * B := fun y => by
    unfold eigenfun
    rw [abs_mul, abs_of_pos (inv_pos.2 (E.eig_pos j))]
    exact mul_le_mul_of_nonneg_left (E.abs_coeff_le' hB0 hB j y) (inv_pos.2 (E.eig_pos j)).le
  have hint := E.integrable_eigenKernel_mul ht hx (E.continuousOn_eigenfun j) hj
  have hϕj : Integrable (E.eigenfun j) ν :=
    Integrable.of_bound (E.measurable_eigenfun j).aestronglyMeasurable _
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hj y)
  set F : E.ι → ℂ → ℝ := fun i y => Real.exp (-(t / E.eig i)) * E.eigenfun i x *
    (E.eigenfun i y * E.eigenfun j y) with hF
  have hϕb : ∀ i y, |E.eigenfun i y| ≤ (E.eig i)⁻¹ * B := fun i y => by
    unfold eigenfun
    rw [abs_mul, abs_of_pos (inv_pos.2 (E.eig_pos i))]
    exact mul_le_mul_of_nonneg_left (E.abs_coeff_le' hB0 hB i y) (inv_pos.2 (E.eig_pos i)).le
  have hFi : ∀ i, Integrable (F i) ν := by
    intro i
    have hm : Measurable fun y => E.eigenfun i y * E.eigenfun j y :=
      (E.measurable_eigenfun i).mul (E.measurable_eigenfun j)
    have hb : Integrable (fun y => E.eigenfun i y * E.eigenfun j y) ν :=
      Integrable.of_bound hm.aestronglyMeasurable ((E.eig i)⁻¹ * B * ((E.eig j)⁻¹ * B))
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hϕb i y) (hϕb j y) (abs_nonneg _)
            (mul_nonneg (inv_pos.2 (E.eig_pos i)).le hB0))
    exact hb.const_mul _
  have hFn : ∀ i y, ‖F i y‖ ≤ 24 * B ^ 2 * E.eig i ^ 2 / t ^ 4 * ((E.eig j)⁻¹ * B) := by
    intro i y
    have h := E.abs_term_le hB0 hB i ht x y
    rw [Real.norm_eq_abs]
    calc |F i y| = |Real.exp (-(t / E.eig i)) * (E.eigenfun i x * E.eigenfun i y)| *
          |E.eigenfun j y| := by
          simp only [hF, abs_mul]; ring
      _ ≤ 24 * B ^ 2 * E.eig i ^ 2 / t ^ 4 * ((E.eig j)⁻¹ * B) :=
          mul_le_mul h (hj y) (abs_nonneg _) (by positivity)
  have hsum : Summable fun i => ∫ y, ‖F i y‖ ∂ν := by
    refine Summable.of_nonneg_of_le (f := fun i => 24 * B ^ 2 * E.eig i ^ 2 / t ^ 4 *
      ((E.eig j)⁻¹ * B)) (fun i => integral_nonneg fun _ => norm_nonneg _)
      (fun i => ?_) ((((E.summable_eig_sq hB0 hB).1.mul_left (24 * B ^ 2)).div_const (t ^ 4)).mul_right
        ((E.eig j)⁻¹ * B))
    calc ∫ y, ‖F i y‖ ∂ν ≤ ∫ _, 24 * B ^ 2 * E.eig i ^ 2 / t ^ 4 * ((E.eig j)⁻¹ * B) ∂ν :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (integrable_const _)
            (Eventually.of_forall fun y => hFn i y)
      _ = _ := by simp
  have htsum := integral_tsum_of_summable_integral_norm hFi hsum
  have hval : ∀ i, ∫ y, F i y ∂ν = if i = j then Real.exp (-(t / E.eig j)) * E.eigenfun j x
      else 0 := by
    intro i
    simp only [hF]
    rw [integral_const_mul, E.integral_eigenfun_mul i j]
    split_ifs with h
    · subst h; ring
    · ring
  have hdecomp : ∀ y, E.eigenKernel t x y * E.eigenfun j y =
      E.eigenfun j y + ∑' i, F i y := by
    intro y
    unfold eigenKernel
    rw [add_mul, one_mul, ← tsum_mul_right]
    congr 1
    refine tsum_congr fun i => ?_
    simp only [hF]
    ring
  have hrest : Integrable (fun y => ∑' i, F i y) ν := by
    refine hint.1.congr (Eventually.of_forall fun y => ?_)
    simp only
    have := hdecomp y
    unfold eigenKernel at this ⊢
    linarith [this]
  rw [integral_congr_ae (Eventually.of_forall hdecomp), integral_add hϕj hrest,
    E.integral_eigenfun j, zero_add, ← htsum, tsum_congr hval, tsum_ite_eq]

theorem integral_eigenKernel {t : ℝ} (ht : 0 < t) {x : ℂ} (hx : x ∈ closedSquare (0 : ℂ) 1) :
    ∫ y, E.eigenKernel t x y ∂ν = 1 := by
  obtain ⟨B, hB0, hB⟩ := hν.isRowFamily_centeredGreenRow.bound
  have hint := E.integrable_eigenKernel_mul ht hx (g := fun _ => 1) continuousOn_const
    (C := 1) (fun _ => by simp)
  have h1 : Integrable (fun y => E.eigenKernel t x y - 1) ν := by
    simpa using hint.1
  have hsum : Summable fun i => ∫ y, ‖Real.exp (-(t / E.eig i)) * (E.eigenfun i x *
      E.eigenfun i y)‖ ∂ν := by
    refine Summable.of_nonneg_of_le (f := fun i => 24 * B ^ 2 * E.eig i ^ 2 / t ^ 4)
      (fun i => integral_nonneg fun _ => norm_nonneg _)
      (fun i => ?_) (((E.summable_eig_sq hB0 hB).1.mul_left (24 * B ^ 2)).div_const (t ^ 4))
    calc ∫ y, ‖Real.exp (-(t / E.eig i)) * (E.eigenfun i x * E.eigenfun i y)‖ ∂ν
        ≤ ∫ _, 24 * B ^ 2 * E.eig i ^ 2 / t ^ 4 ∂ν :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (integrable_const _)
            (Eventually.of_forall fun y => by
              show ‖Real.exp (-(t / E.eig i)) * (E.eigenfun i x * E.eigenfun i y)‖ ≤
                24 * B ^ 2 * E.eig i ^ 2 / t ^ 4
              rw [Real.norm_eq_abs]; exact E.abs_term_le hB0 hB i ht x y)
      _ = _ := by simp
  have hFi : ∀ i, Integrable (fun y => Real.exp (-(t / E.eig i)) * (E.eigenfun i x *
      E.eigenfun i y)) ν := fun i =>
    ((Integrable.of_bound (E.measurable_eigenfun i).aestronglyMeasurable ((E.eig i)⁻¹ * B)
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]
        unfold eigenfun
        rw [abs_mul, abs_of_pos (inv_pos.2 (E.eig_pos i))]
        exact mul_le_mul_of_nonneg_left (E.abs_coeff_le' hB0 hB i y)
          (inv_pos.2 (E.eig_pos i)).le)).const_mul (E.eigenfun i x)).const_mul _
  have htsum := integral_tsum_of_summable_integral_norm hFi hsum
  have hzero : ∀ i, ∫ y, Real.exp (-(t / E.eig i)) * (E.eigenfun i x * E.eigenfun i y) ∂ν = 0 := by
    intro i
    rw [integral_const_mul, integral_const_mul, E.integral_eigenfun i, mul_zero, mul_zero]
  have e : ∀ y, E.eigenKernel t x y = 1 + (E.eigenKernel t x y - 1) := fun y => by ring
  rw [integral_congr_ae (Eventually.of_forall e), integral_add (integrable_const _) h1]
  have : ∫ y, (E.eigenKernel t x y - 1) ∂ν = 0 := by
    unfold eigenKernel
    simp only [add_sub_cancel_left]
    rw [← htsum, tsum_congr hzero, tsum_zero]
  rw [this]
  simp

end GreenEigenData

end HarmonicBalls
