import HarmonicBalls.Proofs.Potential.ReflectedGreenPositivity

/-!
# The eigenbasis of the centered Green operator

Let `ν` be a probability measure carried by `K₀` with upper power bounds. The centered Green
operator `G` on `L²(ν)` is compact and symmetric, its kernel is the constants
(`eq_smul_oneLp_of_centeredGreenOperator_eq_zero`, from the injectivity of `G` on the functions of
mean zero), and its nonzero eigenvalues are positive, with eigenvectors of mean zero
(`pos_of_centeredGreenOperator_eq_smul`, from `⟪G f, f⟫ ≥ 0`). By the spectral theorem for compact
self-adjoint operators (Mathlib's `orthogonalComplement_iSup_eigenspaces_eq_bot` and
`finite_dimensional_eigenspace`), orthonormal bases of the eigenspaces of the nonzero eigenvalues,
together with the constant `1`, form a Hilbert basis of `L²(ν)` (`exists_greenEigenbasis`). Its
index set is countable, since `L²(ν)` is separable and the balls of radius `1/2` around the
elements of an orthonormal family are disjoint.
-/

open MeasureTheory Set Filter Topology Module Metric
open scoped ENNReal NNReal InnerProductSpace

namespace HarmonicBalls

variable {ν : Measure ℂ} [IsProbabilityMeasure ν]

theorem IsUpperRegularSpeed.isCompactOperator_centeredGreenOperator (hν : IsUpperRegularSpeed ν) :
    IsCompactOperator (centeredGreenOperator hν) := by
  rw [centeredGreenOperator_eq_rowOperator]
  exact isCompactOperator_rowOperator _

/-- `⟪G f, f⟫ ≥ 0` for `f` of mean zero. -/
theorem IsUpperRegularSpeed.inner_centeredGreenOperator_self_nonneg (hν : IsUpperRegularSpeed ν)
    {f : Lp ℝ 2 ν} (hf : ⟪oneLp ν, f⟫_ℝ = 0) : 0 ≤ ⟪centeredGreenOperator hν f, f⟫_ℝ := by
  obtain ⟨-, hsq, hEq⟩ := hν.inner_centeredGreenOperator_self hf
  rw [hEq]
  refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
  rw [hsq s hs]
  exact setIntegral_nonneg measurableSet_closedSquare_zero_one fun _ _ => sq_nonneg _

/-- **The kernel of `G` is the constants.** -/
theorem IsUpperRegularSpeed.eq_smul_oneLp_of_centeredGreenOperator_eq_zero
    (hν : IsUpperRegularSpeed ν) {f : Lp ℝ 2 ν} (hf : centeredGreenOperator hν f = 0) :
    f = ⟪oneLp ν, f⟫_ℝ • oneLp ν := by
  have hu1 : ⟪oneLp ν, f - ⟪oneLp ν, f⟫_ℝ • oneLp ν⟫_ℝ = 0 := by
    rw [inner_sub_right, real_inner_smul_right, inner_oneLp_oneLp, mul_one, sub_self]
  have hTu : centeredGreenOperator hν (f - ⟪oneLp ν, f⟫_ℝ • oneLp ν) = 0 := by
    rw [map_sub, map_smul, hf, centeredGreenOperator_oneLp, smul_zero, sub_zero]
  have h := hν.eq_zero_of_inner_centeredGreenOperator_self_eq_zero hu1
    (by rw [hTu, inner_zero_left])
  exact sub_eq_zero.1 h

/-- **The nonzero eigenvalues of `G` are positive**, with eigenvectors of mean zero. -/
theorem IsUpperRegularSpeed.pos_of_centeredGreenOperator_eq_smul (hν : IsUpperRegularSpeed ν)
    {f : Lp ℝ 2 ν} {m : ℝ} (hf : f ≠ 0) (hm : m ≠ 0)
    (hTf : centeredGreenOperator hν f = m • f) : 0 < m ∧ ⟪oneLp ν, f⟫_ℝ = 0 := by
  have h1 : ⟪oneLp ν, f⟫_ℝ = 0 := by
    have h := inner_oneLp_centeredGreenOperator hν f
    rw [hTf, real_inner_smul_right] at h
    exact (mul_eq_zero.1 h).resolve_left hm
  refine ⟨?_, h1⟩
  have hnn := hν.inner_centeredGreenOperator_self_nonneg h1
  have hne : ⟪centeredGreenOperator hν f, f⟫_ℝ ≠ 0 := fun h0 =>
    hf (hν.eq_zero_of_inner_centeredGreenOperator_self_eq_zero h1 h0)
  rw [hTf, real_inner_smul_left, real_inner_self_eq_norm_sq] at hnn hne
  have hpos : 0 < ‖f‖ ^ 2 := by positivity
  rcases lt_or_eq_of_le hnn with h | h
  · exact pos_of_mul_pos_left h hpos.le
  · exact absurd h.symm hne

/-! ### Eigenbases of compact symmetric operators -/

section Abstract

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- The index set: pairs of a nonzero eigenvalue and an index of an orthonormal basis of its
eigenspace. -/
def eigenIndex (T : X →L[ℝ] X) : Type :=
  Σ m : {m : ℝ // m ≠ 0}, Fin (finrank ℝ (Module.End.eigenspace (T : X →ₗ[ℝ] X) m))

/-- The eigenvectors: orthonormal bases of the eigenspaces of the nonzero eigenvalues. -/
noncomputable def eigenVector {T : X →L[ℝ] X} (hT : IsCompactOperator T) (a : eigenIndex T) : X :=
  haveI := ContinuousLinearMap.finite_dimensional_eigenspace hT a.1.1 a.1.2
  (stdOrthonormalBasis ℝ (Module.End.eigenspace (T : X →ₗ[ℝ] X) a.1) a.2 : X)

theorem eigenVector_apply {T : X →L[ℝ] X} (hT : IsCompactOperator T) (a : eigenIndex T) :
    T (eigenVector hT a) = a.1.1 • eigenVector hT a := by
  have := ContinuousLinearMap.finite_dimensional_eigenspace hT a.1.1 a.1.2
  exact Module.End.mem_eigenspace_iff.1
    (stdOrthonormalBasis ℝ (Module.End.eigenspace (T : X →ₗ[ℝ] X) a.1) a.2).2

theorem orthonormal_eigenVector {T : X →L[ℝ] X} (hT : IsCompactOperator T)
    (hT' : (T : X →ₗ[ℝ] X).IsSymmetric) : Orthonormal ℝ (eigenVector hT) := by
  have hfam := hT'.orthogonalFamily_eigenspaces.comp (γ := {m : ℝ // m ≠ 0}) Subtype.val_injective
  have h := hfam.orthonormal_sigma_orthonormal
    (α := fun m : {m : ℝ // m ≠ 0} => Fin (finrank ℝ (Module.End.eigenspace (T : X →ₗ[ℝ] X) m)))
    (v_family := fun m i => by
      haveI := ContinuousLinearMap.finite_dimensional_eigenspace hT m.1 m.2
      exact stdOrthonormalBasis ℝ (Module.End.eigenspace (T : X →ₗ[ℝ] X) m) i)
    (fun m => by
      have := ContinuousLinearMap.finite_dimensional_eigenspace hT m.1 m.2
      exact (stdOrthonormalBasis ℝ (Module.End.eigenspace (T : X →ₗ[ℝ] X) m)).orthonormal)
  exact h

theorem countable_eigenIndex [TopologicalSpace.SeparableSpace X] {T : X →L[ℝ] X}
    (hT : IsCompactOperator T) (hT' : (T : X →ₗ[ℝ] X).IsSymmetric) : Countable (eigenIndex T) := by
  have hv := orthonormal_eigenVector hT hT'
  refine Pairwise.countable_of_isOpen_disjoint (s := fun a => ball (eigenVector hT a) (1 / 2)) ?_
    (fun _ => isOpen_ball) (fun a => ⟨eigenVector hT a, mem_ball_self (by norm_num)⟩)
  intro a b hab
  refine Set.disjoint_left.2 fun z hza hzb => ?_
  have hsq : ‖eigenVector hT a - eigenVector hT b‖ ^ 2 = 2 := by
    rw [@norm_sub_sq_real, hv.1 a, hv.1 b, hv.2 hab]
    norm_num
  have hlt : ‖eigenVector hT a - eigenVector hT b‖ < 1 := by
    rw [← dist_eq_norm]
    calc dist (eigenVector hT a) (eigenVector hT b)
        ≤ dist (eigenVector hT a) z + dist z (eigenVector hT b) := dist_triangle _ _ _
      _ < 1 / 2 + 1 / 2 := add_lt_add (by rw [dist_comm]; exact hza) hzb
      _ = 1 := by norm_num
  nlinarith [norm_nonneg (eigenVector hT a - eigenVector hT b)]

/-- The eigenvectors and a unit vector `e`. -/
noncomputable def eigenFamily {T : X →L[ℝ] X} (hT : IsCompactOperator T) (e : X) :
    Option (eigenIndex T) → X :=
  fun o => o.elim e (eigenVector hT)

theorem orthonormal_eigenFamily {T : X →L[ℝ] X} (hT : IsCompactOperator T)
    (hT' : (T : X →ₗ[ℝ] X).IsSymmetric) {e : X} (he : ‖e‖ = 1)
    (he' : ∀ a, ⟪e, eigenVector hT a⟫_ℝ = 0) : Orthonormal ℝ (eigenFamily hT e) := by
  classical
  have hv := orthonormal_eigenVector hT hT'
  refine ⟨?_, ?_⟩
  · rintro (_ | a)
    · exact he
    · exact hv.1 a
  · rintro (_ | a) (_ | b) hab
    · exact absurd rfl hab
    · exact he' b
    · show ⟪eigenVector hT a, e⟫_ℝ = 0
      rw [real_inner_comm]
      exact he' a
    · exact hv.2 fun h => hab (congrArg some h)

theorem orthogonal_span_eigenFamily_eq_bot {T : X →L[ℝ] X} (hT : IsCompactOperator T)
    (hT' : (T : X →ₗ[ℝ] X).IsSymmetric) {e : X} (hker : ∀ f, T f = 0 → f = ⟪e, f⟫_ℝ • e) :
    (Submodule.span ℝ (range (eigenFamily hT e)))ᗮ = ⊥ := by
  classical
  refine (Submodule.eq_bot_iff _).2 fun u hu => ?_
  have hwu : ∀ o, ⟪eigenFamily hT e o, u⟫_ℝ = 0 := fun o =>
    Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self o)) hu
  have hmem : u ∈ (⨆ m, Module.End.eigenspace (T : X →ₗ[ℝ] X) m)ᗮ := by
    rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
    intro m
    rw [Submodule.mem_orthogonal]
    intro y hy
    by_cases hm : m = 0
    · subst hm
      have hy0 : T y = 0 := by
        have := Module.End.mem_eigenspace_iff.1 hy
        rwa [zero_smul] at this
      rw [hker y hy0, real_inner_smul_left]
      have := hwu none
      rw [show eigenFamily hT e none = e from rfl] at this
      rw [this, mul_zero]
    · have := ContinuousLinearMap.finite_dimensional_eigenspace hT m hm
      have hrep := (stdOrthonormalBasis ℝ (Module.End.eigenspace (T : X →ₗ[ℝ] X) m)).sum_repr'
        (⟨y, hy⟩ : Module.End.eigenspace (T : X →ₗ[ℝ] X) m)
      have hy' : y = ∑ i, ⟪((stdOrthonormalBasis ℝ (Module.End.eigenspace (T : X →ₗ[ℝ] X) m) i :
          Module.End.eigenspace (T : X →ₗ[ℝ] X) m) : X), y⟫_ℝ •
          ((stdOrthonormalBasis ℝ (Module.End.eigenspace (T : X →ₗ[ℝ] X) m) i :
            Module.End.eigenspace (T : X →ₗ[ℝ] X) m) : X) := by
        have := congrArg (fun z : Module.End.eigenspace (T : X →ₗ[ℝ] X) m => (z : X)) hrep
        simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at this
        exact this.symm
      rw [hy', sum_inner]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [real_inner_smul_left]
      have := hwu (some ⟨⟨m, hm⟩, i⟩)
      rw [show eigenFamily hT e (some ⟨⟨m, hm⟩, i⟩) = eigenVector hT ⟨⟨m, hm⟩, i⟩ from rfl] at this
      unfold eigenVector at this
      rw [this, mul_zero]
  rw [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hT hT'] at hmem
  exact hmem

end Abstract

/-- **The eigenbasis of `G`**: a countable family of eigenvectors with positive eigenvalues which,
with the constant `1`, is a Hilbert basis of `L²(ν)`. -/
theorem IsUpperRegularSpeed.exists_greenEigenbasis (hν : IsUpperRegularSpeed ν) :
    ∃ (ι : Type) (_ : Countable ι) (b : HilbertBasis (Option ι) ℝ (Lp ℝ 2 ν)) (μ : ι → ℝ),
      b none = oneLp ν ∧ ∀ i, 0 < μ i ∧ centeredGreenOperator hν (b (some i)) = μ i • b (some i) := by
  have hT := hν.isCompactOperator_centeredGreenOperator
  have hT' : ((centeredGreenOperator hν : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) :
      Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 ν).IsSymmetric := fun f h => inner_centeredGreenOperator_comm hν f h
  have hpos : ∀ a, 0 < a.1.1 ∧ ⟪oneLp ν, eigenVector hT a⟫_ℝ = 0 := fun a =>
    hν.pos_of_centeredGreenOperator_eq_smul (fun h => by
      have := (orthonormal_eigenVector hT hT').1 a
      rw [h, norm_zero] at this
      exact zero_ne_one this) a.1.2 (eigenVector_apply hT a)
  have hone : ‖oneLp ν‖ = 1 := by
    have h := inner_oneLp_oneLp (ν := ν)
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (oneLp ν)]
  have hw := orthonormal_eigenFamily hT hT' hone fun a => (hpos a).2
  have hsp := orthogonal_span_eigenFamily_eq_bot hT hT' (e := oneLp ν) fun f hf =>
    hν.eq_smul_oneLp_of_centeredGreenOperator_eq_zero hf
  refine ⟨eigenIndex (centeredGreenOperator hν), countable_eigenIndex hT hT',
    HilbertBasis.mkOfOrthogonalEqBot hw hsp, fun a => a.1.1, ?_, fun a => ?_⟩
  · rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
    rfl
  · rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
    exact ⟨(hpos a).1, eigenVector_apply hT a⟩

end HarmonicBalls
