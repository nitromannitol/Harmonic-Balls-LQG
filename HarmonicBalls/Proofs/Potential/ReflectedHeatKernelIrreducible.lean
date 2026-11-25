import HarmonicBalls.Proofs.Potential.ReflectedHeatKernelL2Semigroup

/-!
# Irreducibility of the transition semigroup of the time change from symmetry

Let `p` be a symmetric jointly continuous heat kernel of the time change of reflected Brownian
motion in `K₀ = closedSquare 0 1` with respect to a finite measure `ν` carried by `K₀` that charges
every relative ball of `K₀`. Then the transition semigroup `heatKernelL2Semigroup ν p` is
irreducible ([KLVW] Definition A.1) (`isIrreducibleSemigroup_heatKernelL2Semigroup`).

The proof follows Keller–Lenz–Vogt–Wojciechowski (2015), Appendix A, and Fukushima–Oshima–Takeda
(2011), Theorem 1.6.1, for the reduction to invariant sets:

* a closed subspace `U` of `L²(ν)` stable under bounded multipliers is `L²(D)` for
  `D = {e = 1}`, where `1 = e + e'` with `e ∈ U`, `e' ∈ U^⊥`: the products `e e'` and
  `e (1 - e)` vanish, every `f ∈ U` vanishes off `D` and every element of `U^⊥` on `D`;
* if `U` is also invariant under the symmetric semigroup, so is `U^⊥`, hence `T_t 1_{D^c}` vanishes
  on `D`: `∫_{D^c} p(t, x, y) dν(y) = 0` for `ν`-almost every `x ∈ D`;
* if `0 < ν(D) < ν(K₀)`, the closed supports of `ν` on `D` and on `D^c` cover the connected square,
  so they meet at some `z`, and continuity gives `p(t, z, z) = 0` for every `t > 0`; then
  `0 = p(2s, z, z) = ∫ p(s, z, w)² dν(w)` (Chapman–Kolmogorov and symmetry), against
  `∫ p(s, z, w) dν(w) = 1`.

An invariant set of intermediate measure would separate the connected square: the contradiction
uses the connectedness of `K₀`, the Chapman–Kolmogorov identity of the heat kernel
(`IsLBMHeatKernel.chapmanKolmogorov`) and its symmetry.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess Metric
open scoped ENNReal NNReal InnerProductSpace

namespace HarmonicBalls

/-- The closed support of `ν` on `D`: the points all of whose balls meet `D` in positive mass. -/
def measureSupportOn (ν : Measure ℂ) (D : Set ℂ) : Set ℂ :=
  {x | ∀ r : ℝ, 0 < r → 0 < ν (ball x r ∩ D)}

theorem isClosed_measureSupportOn (ν : Measure ℂ) (D : Set ℂ) :
    IsClosed (measureSupportOn ν D) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro x hx
  simp only [measureSupportOn, mem_compl_iff, mem_ofPred_eq, not_forall, not_lt,
    nonpos_iff_eq_zero, exists_prop] at hx
  obtain ⟨r, hr, h0⟩ := hx
  refine ⟨r / 2, half_pos hr, fun y hy => ?_⟩
  simp only [measureSupportOn, mem_compl_iff, mem_ofPred_eq, not_forall, not_lt,
    nonpos_iff_eq_zero, exists_prop]
  refine ⟨r / 2, half_pos hr, measure_mono_null ?_ h0⟩
  intro w hw
  refine ⟨?_, hw.2⟩
  have h1 : dist w y < r / 2 := hw.1
  have h2 : dist y x < r / 2 := hy
  calc dist w x ≤ dist w y + dist y x := dist_triangle _ _ _
    _ < r := by linarith

/-- The supports of `ν` on `D` and on `Dᶜ` cover every point at which `ν` charges every ball. -/
theorem mem_measureSupportOn_or {ν : Measure ℂ} {D : Set ℂ} {x : ℂ}
    (hx : ∀ r : ℝ, 0 < r → 0 < ν (ball x r)) :
    x ∈ measureSupportOn ν D ∪ measureSupportOn ν Dᶜ := by
  by_contra h
  simp only [mem_union, measureSupportOn, mem_ofPred_eq, not_or, not_forall, not_lt,
    nonpos_iff_eq_zero, exists_prop] at h
  obtain ⟨⟨r₁, hr₁, h₁⟩, ⟨r₂, hr₂, h₂⟩⟩ := h
  have hr : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  refine (hx _ hr).ne' (measure_mono_null (fun w hw => ?_) (measure_union_null h₁ h₂))
  by_cases hwD : w ∈ D
  · exact Or.inl ⟨ball_subset_ball (min_le_left _ _) hw, hwD⟩
  · exact Or.inr ⟨ball_subset_ball (min_le_right _ _) hw, hwD⟩

/-- A compact set carrying a set of positive measure meets its support. -/
theorem inter_measureSupportOn_nonempty {ν : Measure ℂ} {K D : Set ℂ} (hK : IsCompact K)
    (hνK : ν Kᶜ = 0) (hD : 0 < ν D) : (K ∩ measureSupportOn ν D).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hbad : ∀ x ∈ K, ∃ r : ℝ, 0 < r ∧ ν (ball x r ∩ D) = 0 := by
    intro x hx
    by_contra h
    have hxs : x ∈ measureSupportOn ν D := fun r hr =>
      pos_iff_ne_zero.2 fun h0 => h ⟨r, hr, h0⟩
    exact (eq_empty_iff_forall_notMem.1 hne x) ⟨hx, hxs⟩
  choose! r hr0 hr using hbad
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun x => ball x (r x))
    fun x hx => ball_mem_nhds x (hr0 x hx)
  have hsub : D ⊆ (⋃ x ∈ t, ball x (r x) ∩ D) ∪ Kᶜ := by
    intro w hw
    by_cases hwK : w ∈ K
    · obtain ⟨x, hx, hwx⟩ := mem_iUnion₂.1 (hcover hwK)
      exact Or.inl (mem_iUnion₂.2 ⟨x, hx, hwx, hw⟩)
    · exact Or.inr hwK
  refine hD.ne' (measure_mono_null hsub (measure_union_null ?_ hνK))
  exact (measure_biUnion_null_iff t.countable_toSet).2 fun x hx => hr x (htK x hx)

/-- A function continuous and nonnegative on `K` that vanishes `ν`-almost everywhere on `D` vanishes
at every point of `K` in the support of `ν` on `D`. -/
theorem eq_zero_of_mem_measureSupportOn {ν : Measure ℂ} {K D : Set ℂ} (hνK : ν Kᶜ = 0)
    {φ : ℂ → ℝ} (hφc : ContinuousOn φ K) (hφ0 : ∀ x ∈ K, 0 ≤ φ x)
    (hφD : ∀ᵐ x ∂ν, x ∈ D → φ x = 0) {z : ℂ} (hzK : z ∈ K) (hz : z ∈ measureSupportOn ν D) :
    φ z = 0 := by
  by_contra hne
  have hpos : 0 < φ z := lt_of_le_of_ne (hφ0 z hzK) (Ne.symm hne)
  have hev : ∀ᶠ x in 𝓝[K] z, 0 < φ x := (hφc z hzK).eventually (lt_mem_nhds hpos)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.1 hev
  refine (hz r hr).ne' (measure_mono_null (fun w hw => ?_)
    (measure_union_null (ae_iff.1 hφD) hνK))
  by_cases hwK : w ∈ K
  · left
    intro h
    exact (hsub ⟨hw.1, hwK⟩).ne' (h hw.2)
  · exact Or.inr hwK

theorem isPreconnected_closedSquare_zero_one : IsPreconnected (closedSquare 0 1) := by
  refine Convex.isPreconnected ?_
  intro z hz w hw a b ha hb hab
  simp only [closedSquare, Complex.mem_reProdIm, Complex.zero_re, Complex.zero_im, zero_add,
    mem_Icc] at hz hw ⊢
  simp only [Complex.add_re, Complex.add_im, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  refine ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩

section Irreducible

variable {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0} {ν : Measure ℂ} [IsFiniteMeasure ν]
  {p : ℝ → ℂ → ℂ → ℝ}

omit [IsFiniteMeasure ν] in
/-- A product `g v` of a bounded measurable function and an element of `L²(ν)`, as an element of
`L²(ν)`. -/
theorem exists_lp_mul {g : ℂ → ℝ} {C : ℝ} (hg : Measurable g) (hgC : ∀ x, |g x| ≤ C)
    (v : Lp ℝ 2 ν) : ∃ h : Lp ℝ 2 ν, (h : ℂ → ℝ) =ᵐ[ν] fun x => g x * (v : ℂ → ℝ) x := by
  have hm : MemLp (fun x => g x * (v : ℂ → ℝ) x) 2 ν :=
    (Lp.memLp v).of_le_mul (c := C)
      (hg.aestronglyMeasurable.mul (Lp.aestronglyMeasurable v))
      (Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hgC x) (norm_nonneg _))
  exact ⟨hm.toLp _, hm.coeFn_toLp⟩

/-- **Irreducibility of the transition semigroup of a symmetric heat kernel.** -/
theorem isIrreducibleSemigroup_heatKernelL2Semigroup (hA : IsUnitSquarePCAF A)
    (hνK : ν (closedSquare 0 1)ᶜ = 0)
    (hsupp : ∀ y ∈ closedSquare 0 1, ∀ r : ℝ, 0 < r → 0 < ν (ball y r ∩ closedSquare 0 1))
    (hatom : ∀ x ∈ closedSquare 0 1, ν {x} = 0)
    (hp : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
      (closedSquare 0 1) ν p)
    (hpc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1))
    (hsym : ∀ t : ℝ, 0 < t → ∀ x ∈ closedSquare 0 1, ∀ y ∈ closedSquare 0 1, p t x y = p t y x) :
    IsIrreducibleSemigroup ν (heatKernelL2Semigroup ν p) := by
  intro U hUc hM hT
  have hKm : MeasurableSet (closedSquare 0 1) :=
    (isCompact_closedSquare 0 1).isClosed.measurableSet
  have : CompleteSpace U := hUc.completeSpace_coe
  -- the decomposition `1 = e + e'`
  set one : Lp ℝ 2 ν := (memLp_const (1 : ℝ)).toLp _ with hone
  have hone_c : (one : ℂ → ℝ) =ᵐ[ν] fun _ => (1 : ℝ) := (memLp_const (1 : ℝ)).coeFn_toLp
  obtain ⟨e, he, e', he', hee⟩ := U.exists_add_mem_mem_orthogonal one
  have h3 : ((e + e' : Lp ℝ 2 ν) : ℂ → ℝ) =ᵐ[ν] (one : ℂ → ℝ) := by rw [← hee]
  have hsum : ∀ᵐ x ∂ν, (e : ℂ → ℝ) x + (e' : ℂ → ℝ) x = 1 := by
    filter_upwards [hone_c, Lp.coeFn_add e e', h3] with x h1 h2 h3
    have h := h2.symm.trans (h3.trans h1)
    simpa using h
  -- integrals of products against indicators
  have hind : ∀ s, MeasurableSet s → Measurable (s.indicator fun _ : ℂ => (1 : ℝ)) :=
    fun s hs => measurable_const.indicator hs
  have hindC : ∀ s : Set ℂ, ∀ x, |s.indicator (fun _ : ℂ => (1 : ℝ)) x| ≤ 1 := by
    intro s x
    by_cases hx : x ∈ s <;> simp [hx]
  -- an element of `U` and an element of `Uᗮ` have vanishing product
  have hprod : ∀ u ∈ U, ∀ v ∈ Uᗮ,
      (fun x => (u : ℂ → ℝ) x * (v : ℂ → ℝ) x) =ᵐ[ν] 0 := by
    intro u hu v hv
    have huv : Integrable (fun x => (u : ℂ → ℝ) x * (v : ℂ → ℝ) x) ν :=
      (Lp.memLp u).integrable_mul (Lp.memLp v)
    refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ _ => huv.integrableOn)
      fun s hs _ => ?_
    obtain ⟨h, hh⟩ := exists_lp_mul (hind s hs) (hindC s) u
    have hhU : h ∈ U := hM u hu _ 1 (hind s hs) (hindC s) h hh
    have h0 := Submodule.inner_right_of_mem_orthogonal hhU hv
    rw [l2_inner_eq_integral_mul] at h0
    rw [← h0, ← integral_indicator hs]
    refine integral_congr_ae ?_
    filter_upwards [hh] with x hx
    rw [hx]
    by_cases hxs : x ∈ s <;> simp [hxs]
  have hee0 := hprod e he e' he'
  -- `e` is the indicator of `D = {e = 1}` almost everywhere
  set D : Set ℂ := {x | (e : ℂ → ℝ) x = 1} with hD_def
  have hDm : MeasurableSet D :=
    (Lp.stronglyMeasurable e).measurable (measurableSet_singleton 1)
  have hedich : ∀ᵐ x ∂ν, (e : ℂ → ℝ) x = D.indicator (fun _ => (1 : ℝ)) x ∧
      (e' : ℂ → ℝ) x = Dᶜ.indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [hsum, hee0] with x h1 h2
    have h2' : (e : ℂ → ℝ) x * (e' : ℂ → ℝ) x = 0 := h2
    have he'x : (e' : ℂ → ℝ) x = 1 - (e : ℂ → ℝ) x := by linarith
    rw [he'x] at h2'
    have hcases : (e : ℂ → ℝ) x = 0 ∨ (e : ℂ → ℝ) x = 1 := by
      rcases mul_eq_zero.1 h2' with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    rcases hcases with h | h
    · have hxD : x ∉ D := by simp [hD_def, h]
      simp [hxD, h, he'x]
    · have hxD : x ∈ D := h
      simp [hxD, h, he'x]
  -- elements of `U` vanish off `D`, elements of `Uᗮ` vanish on `D`
  have hUoff : ∀ f ∈ U, ∀ᵐ x ∂ν, x ∉ D → (f : ℂ → ℝ) x = 0 := by
    intro f hf
    filter_upwards [hprod f hf e' he', hedich] with x h1 h2 hx
    have h1' : (f : ℂ → ℝ) x * (e' : ℂ → ℝ) x = 0 := h1
    rw [h2.2, indicator_of_mem (show x ∈ Dᶜ from hx), mul_one] at h1'
    exact h1'
  have hUperp : ∀ v ∈ Uᗮ, ∀ᵐ x ∂ν, x ∈ D → (v : ℂ → ℝ) x = 0 := by
    intro v hv
    filter_upwards [hprod e he v hv, hedich] with x h1 h2 hx
    have h1' : (e : ℂ → ℝ) x * (v : ℂ → ℝ) x = 0 := h1
    rw [h2.1, indicator_of_mem hx, one_mul] at h1'
    exact h1'
  -- the three cases
  by_cases hD0 : ν D = 0
  · left
    refine (Submodule.eq_bot_iff U).2 fun f hf => Lp.eq_zero_iff_ae_eq_zero.2 ?_
    filter_upwards [hUoff f hf, measure_eq_zero_iff_ae_notMem.1 hD0] with x h1 h2
    exact h1 h2
  by_cases hDc0 : ν Dᶜ = 0
  · right
    refine (Submodule.orthogonal_eq_bot_iff).1 ((Submodule.eq_bot_iff _).2 fun v hv =>
      Lp.eq_zero_iff_ae_eq_zero.2 ?_)
    filter_upwards [hUperp v hv, measure_eq_zero_iff_ae_notMem.1 hDc0] with x h1 h2
    exact h1 (by simpa using h2)
  exfalso
  -- the semigroup maps `Uᗮ` into itself
  have hTperp : ∀ t, ∀ v ∈ Uᗮ, heatKernelL2Semigroup ν p t v ∈ Uᗮ := by
    intro t v hv
    refine (Submodule.mem_orthogonal' _ _).2 fun u hu => ?_
    rw [real_inner_comm, ← heatKernelL2Semigroup_inner_comm hνK hpc hsym]
    exact Submodule.inner_right_of_mem_orthogonal (hT t u hu) hv
  -- `∫_{Dᶜ} p(t, x, ·) dν = 0` for almost every `x ∈ D`
  have hφ : ∀ t : ℝ, 0 < t → ∀ᵐ x ∂ν, x ∈ D →
      kernelTransform ν (closedSquare 0 1) (p t) (Dᶜ.indicator fun _ => (1 : ℝ)) x = 0 := by
    intro t ht
    have ht' : t.toNNReal ≠ 0 := (Real.toNNReal_pos.2 ht).ne'
    have hd := isL2KernelData_of_continuousOn hνK hpc ht
    have h1 := hUperp _ (hTperp t.toNNReal e' he')
    rw [heatKernelL2Semigroup_of_ne_zero _ _ ht', Real.coe_toNNReal _ ht.le] at h1
    have h2 : (e' : ℂ → ℝ) =ᵐ[ν] Dᶜ.indicator fun _ => (1 : ℝ) := hedich.mono fun x hx => hx.2
    filter_upwards [h1, hd.coeFn_kernelL2Operator e'] with x hx1 hx2 hxD
    rw [← kernelTransform_congr_ae h2, ← hx2]
    exact hx1 hxD
  -- the two supports meet at a point `z`
  have hball : ∀ x ∈ closedSquare 0 1, ∀ r : ℝ, 0 < r → 0 < ν (ball x r) := fun x hx r hr =>
    (hsupp x hx r hr).trans_le (measure_mono inter_subset_left)
  obtain ⟨z, hzK, hzD, hzDc⟩ := isPreconnected_closed_iff.1 isPreconnected_closedSquare_zero_one
    _ _ (isClosed_measureSupportOn ν D) (isClosed_measureSupportOn ν Dᶜ)
    (fun x hx => mem_measureSupportOn_or (hball x hx))
    (inter_measureSupportOn_nonempty (isCompact_closedSquare 0 1) hνK (pos_iff_ne_zero.2 hD0))
    (inter_measureSupportOn_nonempty (isCompact_closedSquare 0 1) hνK (pos_iff_ne_zero.2 hDc0))
  -- `p(t, z, z) = 0` for every `t > 0`
  have hzz : ∀ t : ℝ, 0 < t → p t z z = 0 := by
    intro t ht
    have hd := isL2KernelData_of_continuousOn hνK hpc ht
    have hDci : Integrable (Dᶜ.indicator fun _ : ℂ => (1 : ℝ)) (ν.restrict (closedSquare 0 1)) :=
      (integrable_const (1 : ℝ)).indicator hDm.compl
    have h1 : kernelTransform ν (closedSquare 0 1) (p t) (Dᶜ.indicator fun _ => (1 : ℝ)) z = 0 :=
      eq_zero_of_mem_measureSupportOn hνK (hd.continuousOn_kernelTransform hDci)
        (fun x hx => integral_nonneg_of_ae (by
          filter_upwards [ae_restrict_mem hKm] with y hy
          exact mul_nonneg ((hp t ht x hx).1 y hy) (indicator_nonneg (fun _ _ => zero_le_one) _)))
        (hφ t ht) hzK hzD
    -- hence `p(t, z, ·) = 0` almost everywhere on `Dᶜ`
    have h2 : ∀ᵐ y ∂ν, y ∈ Dᶜ → p t z y = 0 := by
      have hnn : 0 ≤ᵐ[ν.restrict (closedSquare 0 1)]
          fun y => p t z y * Dᶜ.indicator (fun _ => (1 : ℝ)) y := by
        filter_upwards [ae_restrict_mem hKm] with y hy
        exact mul_nonneg ((hp t ht z hzK).1 y hy) (indicator_nonneg (fun _ _ => zero_le_one) _)
      have h3 := (integral_eq_zero_iff_of_nonneg_ae hnn (hd.integrable_mul hzK hDci)).1 h1
      rw [EventuallyEq, ae_restrict_iff' hKm] at h3
      filter_upwards [h3, hd.ae_mem] with y hy hyK hyD
      have := hy hyK
      simp only [Pi.zero_apply, indicator_of_mem hyD, mul_one] at this
      exact this
    exact eq_zero_of_mem_measureSupportOn hνK (hd.continuousOn_right hzK)
      (fun y hy => (hp t ht z hzK).1 y hy) h2 hzK hzDc
  -- contradiction with the Chapman–Kolmogorov identity and the unit mass of the rows
  have hd1 := isL2KernelData_of_continuousOn hνK hpc one_pos
  have hCK := hp.chapmanKolmogorov hA hsupp hatom hpc one_pos one_pos hzK hzK
  rw [hzz (1 + 1) (by norm_num)] at hCK
  have hsq : ∫ w in closedSquare 0 1, p 1 z w ^ 2 ∂ν = 0 := by
    refine (setIntegral_congr_fun hKm fun w hw => ?_).trans hCK.symm
    show p 1 z w ^ 2 = p 1 z w * p 1 w z
    rw [sq, hsym 1 one_pos w hw z hzK]
  have hnn : 0 ≤ᵐ[ν.restrict (closedSquare 0 1)] fun w => p 1 z w ^ 2 :=
    Eventually.of_forall fun w => sq_nonneg _
  have hint : Integrable (fun w => p 1 z w ^ 2) (ν.restrict (closedSquare 0 1)) := by
    have h := hd1.integrable_mul hzK (hd1.integrable_right hzK)
    refine h.congr (Eventually.of_forall fun w => ?_)
    simp only [sq]
  have h0 := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 hsq
  have hmass := hp.setIntegral_eq_one hνK hpc one_pos hzK
  rw [integral_congr_ae (h0.mono fun w hw => by simpa using hw)] at hmass
  simp at hmass

end Irreducible

end HarmonicBalls
