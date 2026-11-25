import HarmonicBalls.Proofs.Potential.ReflectedEigenKernel
import HarmonicBalls.Proofs.Potential.ReflectedCenteredResolvent
import HarmonicBalls.Proofs.Potential.LaplaceTransformUniquenessAe

/-!
# The transition operators of the time change on the eigenfunctions

Let `A` be a clock of reflected Brownian motion in `K₀` whose Revuz measure `ν` is a probability
measure with upper power bounds, and `(1, φ_i)` an eigenbasis of the centered Green operator, with
continuous representatives `ϕ_i` and eigenvalues `μ_i = 1/λ_i`. Let
`P_u h(x) = E_x h(Y_u)` (`timeChangeTransition`). Then, for `x ∈ K₀` and `u > 0`,
`P_u ϕ_i(x) = e^{-λ_i u} ϕ_i(x)` (`timeChangeTransition_eigenfun`):

* `R_c ϕ_i(x) = ϕ_i(x) / (c + λ_i)` (`resolventReal_eigenfun`), from the centered resolvent identity,
  since `V ϕ_i = μ_i ϕ_i + const` on `K₀`;
* `R_c h(x) = ∫_0^∞ e^{-c u} P_u h(x) du` (`resolventReal_eq_setIntegral`, Fubini), so the Laplace
  transforms of `u ↦ P_u ϕ_i(x)` and `u ↦ e^{-λ_i u} ϕ_i(x)` agree at `c = 1, 2, …`, and the two
  functions agree almost everywhere (`ae_eq_of_laplace_eq`);
* `u ↦ P_u h(x)` is right-continuous for `h` continuous on `K₀`
  (`continuousWithinAt_timeChangeTransition`), since the right inverse of a nondecreasing
  unbounded clock is right-continuous (`continuousWithinAt_sInf_lt`), so the two functions agree
  everywhere on `(0, ∞)`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Metric MarkovProcess
open scoped ENNReal NNReal InnerProductSpace

namespace HarmonicBalls

variable {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}

/-! ### Right-continuity of the time change -/

/-- **The right inverse of an unbounded clock is right-continuous.** -/
theorem continuousWithinAt_sInf_lt {a : ℝ≥0 → ℝ≥0} (hu : ∀ r, ∃ t, r < a t)
    (u₀ : ℝ≥0) : ContinuousWithinAt (fun u => sInf {t | u < a t}) (Ici u₀) u₀ := by
  have hne : ∀ r, ({t | r < a t} : Set ℝ≥0).Nonempty := fun r => hu r
  have hmono : ∀ {u v : ℝ≥0}, u ≤ v → sInf {t | u < a t} ≤ sInf {t | v < a t} := fun {u v} huv =>
    csInf_le_csInf (OrderBot.bddBelow _) (hne v) fun t ht => lt_of_le_of_lt huv ht
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with u hu'
    exact lt_of_lt_of_le hc (hmono hu')
  · obtain ⟨t, ht, htc⟩ := exists_lt_of_csInf_lt (hne u₀) hc
    have hIio : Iio (a t) ∈ 𝓝[Ici u₀] u₀ := nhdsWithin_le_nhds (Iio_mem_nhds ht)
    filter_upwards [hIio] with u hu'
    exact lt_of_le_of_lt (csInf_le (OrderBot.bddBelow _) hu') htc

/-- The transition operator `P_u h(x) = E_x h(Y_u)` of the time change. -/
noncomputable def timeChangeTransition (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (h : ℂ → ℝ) (u : ℝ)
    (x : ℂ) : ℝ :=
  ∫ b, h (clockPair A (b, u)).2 ∂reflectedPlanarBrownianMotion 0 1 x

theorem measurable_timeChangeTransition (hA : ∀ t, Measurable (A t)) {h : ℂ → ℝ}
    (hh : Measurable h) (x : ℂ) : Measurable fun u => timeChangeTransition A h u x := by
  have hs : StronglyMeasurable fun q : ContinuousPath ℂ × ℝ => h (clockPair A q).2 :=
    (hh.comp (measurable_clockPair hA).snd).stronglyMeasurable
  exact (hs.integral_prod_left' (μ := reflectedPlanarBrownianMotion 0 1 x)).measurable

theorem abs_timeChangeTransition_le {h : ℂ → ℝ} {M : ℝ} (hM : ∀ z, |h z| ≤ M) (u : ℝ) (x : ℂ) :
    |timeChangeTransition A h u x| ≤ M := by
  unfold timeChangeTransition
  calc |∫ b, h (clockPair A (b, u)).2 ∂reflectedPlanarBrownianMotion 0 1 x|
      ≤ ∫ b, |h (clockPair A (b, u)).2| ∂reflectedPlanarBrownianMotion 0 1 x :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _, M ∂reflectedPlanarBrownianMotion 0 1 x :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const _)
          (Eventually.of_forall fun b => hM _)
    _ = M := by simp

/-- **Right-continuity of the transition operators** for `h` continuous on `K₀`. -/
theorem continuousWithinAt_timeChangeTransition (hA : IsUnitSquarePCAF A)
    [IsProbabilityMeasure (unitSquareRevuzMeasure A)] {h : ℂ → ℝ} (hh : Measurable h)
    (hc : ContinuousOn h (closedSquare 0 1)) {M : ℝ} (hM : ∀ z, |h z| ≤ M) {x : ℂ}
    (hx : x ∈ closedSquare (0 : ℂ) 1) (u₀ : ℝ) :
    ContinuousWithinAt (fun u => timeChangeTransition A h u x) (Ici u₀) u₀ := by
  -- the good paths
  have hgood : ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x,
      (∀ t, clockRationalRegularization A t b = A t b) ∧
        Tendsto (fun t => A t b) atTop atTop ∧ ∀ t, b t ∈ closedSquare 0 1 := by
    filter_upwards [hA.path x hx, hA.hU x hx, OptionalTime.ae_forall_mem_closedSquare_reflected x]
      with b hp hU hK
    exact ⟨fun t => clockRationalRegularization_eq_of_continuous_monotone hp.2.1 hp.2.2 t, hU, hK⟩
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => M)
    (Eventually.of_forall fun u => (hh.comp ((measurable_clockPair hA.measurable).snd.comp
      (measurable_id.prodMk measurable_const))).aestronglyMeasurable)
    (Eventually.of_forall fun u => Eventually.of_forall fun b => by
      rw [Real.norm_eq_abs]; exact hM _) (integrable_const _) ?_
  filter_upwards [hgood] with b ⟨hreg, hU, hK⟩
  -- the clock along `b`
  have hunb : ∀ r, ∃ t, r < clockRationalRegularization A t b := by
    intro r
    obtain ⟨t, ht⟩ := (hU.eventually (eventually_gt_atTop r)).exists
    exact ⟨t, by rw [hreg]; exact ht⟩
  have hτ := continuousWithinAt_sInf_lt hunb u₀.toNNReal
  have hτ' : ContinuousWithinAt (fun u : ℝ => pcafClockInverse (clockRationalRegularization A)
      u.toNNReal b) (Ici u₀) u₀ :=
    hτ.comp continuous_real_toNNReal.continuousWithinAt fun u hu =>
      Real.toNNReal_le_toNNReal hu
  have hY : ContinuousWithinAt (fun u : ℝ => (clockPair A (b, u)).2) (Ici u₀) u₀ :=
    (b.continuous.continuousAt).comp_continuousWithinAt hτ'
  have hmem : ∀ u : ℝ, (clockPair A (b, u)).2 ∈ closedSquare 0 1 := fun u => hK _
  have hcY : ContinuousWithinAt h (closedSquare 0 1) ((clockPair A (b, u₀)).2) := hc _ (hmem u₀)
  exact (ContinuousWithinAt.comp (f := fun u : ℝ => (clockPair A (b, u)).2) (x := u₀) hcY hY
    fun u _ => hmem u).tendsto

/-- **Two right-continuous functions equal almost everywhere on `(0, ∞)` are equal there.** -/
theorem eq_of_ae_eq_of_continuousWithinAt {f g : ℝ → ℝ}
    (hfg : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g)
    (hf : ∀ u₀, 0 < u₀ → ContinuousWithinAt f (Ici u₀) u₀)
    (hg : ∀ u₀, 0 < u₀ → ContinuousWithinAt g (Ici u₀) u₀) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    f u₀ = g u₀ := by
  have hseq : ∀ n : ℕ, ∃ u ∈ Ioo u₀ (u₀ + 1 / (n + 1)), f u = g u := by
    intro n
    by_contra hcon
    push Not at hcon
    have hpos : 0 < volume (Ioo u₀ (u₀ + 1 / (n + 1))) := by
      rw [Real.volume_Ioo]
      simp only [add_sub_cancel_left, ENNReal.ofReal_pos]
      positivity
    have hnull : volume (Ioo u₀ (u₀ + 1 / (n + 1))) = 0 := by
      have h := (ae_restrict_iff' measurableSet_Ioi).1 hfg
      rw [ae_iff] at h
      refine measure_mono_null (fun u hu => ?_) h
      exact fun h' => hcon u hu (h' (lt_trans hu₀ hu.1))
    exact hpos.ne' hnull
  choose u hu hfgu using hseq
  have hlim : Tendsto u atTop (𝓝[Ici u₀] u₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => le_of_lt (hu n).1⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n => le_of_lt (hu n).1) (fun n => le_of_lt (hu n).2)
    simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h1 := (hf u₀ hu₀).tendsto.comp hlim
  have h2 := (hg u₀ hu₀).tendsto.comp hlim
  exact tendsto_nhds_unique h1 (h2.congr fun n => (hfgu n).symm)

/-! ### The resolvent as a Laplace transform -/

/-- **Fubini**: `R_c h(x) = ∫_0^∞ e^{-c u} P_u h(x) du`. -/
theorem resolventReal_eq_setIntegral (hA : ∀ t, Measurable (A t)) {c : ℝ} (hc : 0 < c)
    {h : ℂ → ℝ} (hh : Measurable h) {M : ℝ} (hM : ∀ z, |h z| ≤ M) (x : ℂ) :
    resolventReal A 0 c h x =
      ∫ u in Ioi (0 : ℝ), Real.exp (-(c * u)) * timeChangeTransition A h u x := by
  have hint : Integrable (Function.uncurry fun b u => resolventIntegrand A 0 c h (b, u))
      ((reflectedPlanarBrownianMotion 0 1 x).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine ((integrable_const (1 : ℝ)).mul_prod ((integrableOn_exp_neg_mul hc).const_mul M)).mono'
      (measurable_resolventIntegrand hA 0 c hh).aestronglyMeasurable
      (Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, one_mul]
    exact abs_resolventIntegrand_le le_rfl hM q
  unfold resolventReal
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [resolventIntegrand, zero_mul, neg_zero, Real.exp_zero, one_mul]
  rw [integral_const_mul]
  rfl

theorem resolventReal_add (hA : ∀ t, Measurable (A t)) {β c : ℝ} (hβ : 0 ≤ β) (hc : 0 < c)
    {h₁ h₂ : ℂ → ℝ} (hh₁ : Measurable h₁) (hh₂ : Measurable h₂) {M₁ M₂ : ℝ}
    (hM₁ : ∀ z, |h₁ z| ≤ M₁) (hM₂ : ∀ z, |h₂ z| ≤ M₂) (x : ℂ) :
    resolventReal A β c (fun z => h₁ z + h₂ z) x =
      resolventReal A β c h₁ x + resolventReal A β c h₂ x := by
  unfold resolventReal
  rw [← integral_add (integrable_inner_resolventIntegrand hA hβ hc hh₁ hM₁ x)
    (integrable_inner_resolventIntegrand hA hβ hc hh₂ hM₂ x)]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only
  rw [← integral_add (integrable_resolventIntegrand hA hβ hc hh₁ hM₁ b).1
    (integrable_resolventIntegrand hA hβ hc hh₂ hM₂ b).1]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [resolventIntegrand]
  ring

theorem resolventReal_const_mul {β c : ℝ} (a : ℝ) (h : ℂ → ℝ) (x : ℂ) :
    resolventReal A β c (fun z => a * h z) x = a * resolventReal A β c h x := by
  unfold resolventReal
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [resolventIntegrand]
  ring

section Eigen

variable [IsProbabilityMeasure (unitSquareRevuzMeasure A)]
  {hν : IsUpperRegularSpeed (unitSquareRevuzMeasure A)} (E : GreenEigenData hν)

theorem GreenEigenData.abs_eigenfun_le {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ closedSquare (0 : ℂ) 1, ‖centeredGreenRow hν x‖ ≤ B) (i : E.ι) (z : ℂ) :
    |E.eigenfun i z| ≤ (E.eig i)⁻¹ * B := by
  unfold GreenEigenData.eigenfun
  rw [abs_mul, abs_of_pos (inv_pos.2 (E.eig_pos i))]
  exact mul_le_mul_of_nonneg_left (E.abs_coeff_le' hB0 hB i z) (inv_pos.2 (E.eig_pos i)).le

/-- **The Green potential of an eigenfunction**: `V ϕ_i = μ_i ϕ_i + ⟪V 1, φ_i⟫` on `K₀`. -/
theorem GreenEigenData.centeredGreenPotential_eigenfun (i : E.ι) {z : ℂ}
    (hz : z ∈ closedSquare (0 : ℂ) 1) :
    centeredGreenPotential (unitSquareRevuzMeasure A) (E.eigenfun i) z =
      E.eig i * E.eigenfun i z + ⟪greenOperator hν (oneLp _), E.basis (some i)⟫_ℝ := by
  have hQ : meanZeroProj _ (E.basis (some i)) = E.basis (some i) :=
    meanZeroProj_of_inner_eq_zero (E.inner_oneLp_basis_some i)
  have h1 : E.coeff i z = ⟪greenRow _ z, E.basis (some i)⟫_ℝ -
      ⟪greenOperator hν (oneLp _), E.basis (some i)⟫_ℝ := by
    rw [GreenEigenData.coeff, rowEval_of_mem hz, centeredGreenRow, inner_sub_left,
      inner_meanZeroProj_comm, inner_meanZeroProj_comm, hQ]
  have h2 : ⟪greenRow _ z, E.basis (some i)⟫_ℝ =
      centeredGreenPotential (unitSquareRevuzMeasure A) (E.eigenfun i) z := by
    rw [hν.inner_greenRow hz, centeredGreenPotential]
    refine integral_congr_ae ?_
    filter_upwards [E.coeFn_basis_eq_eigenfun i] with y hy
    rw [hy]
  rw [← h2, ← E.coeff_eq_mul_eigenfun, h1]
  ring

/-- **The resolvent of an eigenfunction**: `R_c ϕ_i(x) = ϕ_i(x) / (c + λ_i)` on `K₀`. -/
theorem resolventReal_eigenfun (hA : IsUnitSquarePCAF A) (i : E.ι) {c : ℝ} (hc : 0 < c) {x : ℂ}
    (hx : x ∈ closedSquare (0 : ℂ) 1) :
    resolventReal A 0 c (E.eigenfun i) x = E.eigenfun i x / (c + 1 / E.eig i) := by
  obtain ⟨B, hB0, hB⟩ := hν.isRowFamily_centeredGreenRow.bound
  have hϕm := E.measurable_eigenfun i
  have hϕM := E.abs_eigenfun_le hB0 hB i
  have hμ := E.eig_pos i
  set k := ⟪greenOperator hν (oneLp (unitSquareRevuzMeasure A)), E.basis (some i)⟫_ℝ with hk
  have hid := resolventReal_add_resolventReal_greenPotential hA hν hc hϕm hϕM
    (E.integral_eigenfun i) hx
  rw [E.centeredGreenPotential_eigenfun i hx] at hid
  have hcongr : resolventReal A 0 c ((closedSquare 0 1).indicator
      (centeredGreenPotential (unitSquareRevuzMeasure A) (E.eigenfun i))) x =
      resolventReal A 0 c (fun z => E.eig i * E.eigenfun i z + k) x := by
    refine resolventReal_congr (fun z hz => ?_) x
    rw [indicator_of_mem hz, E.centeredGreenPotential_eigenfun i hz]
  have hlin : resolventReal A 0 c (fun z => E.eig i * E.eigenfun i z + k) x =
      E.eig i * resolventReal A 0 c (E.eigenfun i) x + k / c := by
    rw [resolventReal_add hA.measurable le_rfl hc (hϕm.const_mul _) measurable_const
      (M₁ := E.eig i * ((E.eig i)⁻¹ * B)) (M₂ := |k|) (fun z => by
        rw [abs_mul, abs_of_pos hμ]; exact mul_le_mul_of_nonneg_left (hϕM z) hμ.le)
      (fun _ => le_rfl), resolventReal_const_mul, resolventReal_const hc]
  rw [hcongr, hlin] at hid
  have hne : c + 1 / E.eig i ≠ 0 := by positivity
  rw [eq_div_iff hne]
  have h2 : resolventReal A 0 c (E.eigenfun i) x * (1 + c * E.eig i) =
      E.eig i * E.eigenfun i x := by
    have := hid
    field_simp at this ⊢
    linarith
  field_simp
  nlinarith [h2]

/-- **The transition operators on an eigenfunction**: `P_u ϕ_i(x) = e^{-λ_i u} ϕ_i(x)` for
`x ∈ K₀` and `u > 0`. -/
theorem timeChangeTransition_eigenfun (hA : IsUnitSquarePCAF A) (i : E.ι) {x : ℂ}
    (hx : x ∈ closedSquare (0 : ℂ) 1) {u : ℝ} (hu : 0 < u) :
    timeChangeTransition A (E.eigenfun i) u x = Real.exp (-(u / E.eig i)) * E.eigenfun i x := by
  obtain ⟨B, hB0, hB⟩ := hν.isRowFamily_centeredGreenRow.bound
  have hϕm := E.measurable_eigenfun i
  set M := (E.eig i)⁻¹ * B with hM_def
  have hϕM : ∀ z, |E.eigenfun i z| ≤ M := E.abs_eigenfun_le hB0 hB i
  have hμ := E.eig_pos i
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hϕM 0)
  set φ₁ : ℝ → ℝ := fun u => timeChangeTransition A (E.eigenfun i) u x + M with hφ₁
  set φ₂ : ℝ → ℝ := fun u => Real.exp (-(u / E.eig i)) * E.eigenfun i x + M with hφ₂
  have hb1 : ∀ u, |timeChangeTransition A (E.eigenfun i) u x| ≤ M := fun u =>
    abs_timeChangeTransition_le hϕM u x
  have hb2 : ∀ u, 0 ≤ u → |Real.exp (-(u / E.eig i)) * E.eigenfun i x| ≤ M := fun u hu => by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_of_le_one_left (abs_nonneg _) (Real.exp_le_one_iff.2 (by
      have := div_nonneg hu hμ.le; linarith))).trans (hϕM x)
  have h1m : Measurable φ₁ := (measurable_timeChangeTransition hA.measurable hϕm x).add_const _
  have h2m : Measurable φ₂ :=
    ((Real.continuous_exp.measurable.comp ((measurable_id.div_const _).neg)).mul_const _).add_const _
  have hlap : ∀ n : ℕ, ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-((n + 1) * u))) *
      ENNReal.ofReal (φ₁ u) = ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-((n + 1) * u))) *
        ENNReal.ofReal (φ₂ u) := by
    intro n
    have hc : (0 : ℝ) < n + 1 := by positivity
    have hexp := integrableOn_exp_neg_mul hc
    have hφ1 : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ φ₁ u := fun u _ => by
      simp only [hφ₁]; linarith [(abs_le.1 (hb1 u)).1]
    have hφ2 : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ φ₂ u := fun u hu => by
      simp only [hφ₂]; linarith [(abs_le.1 (hb2 u (le_of_lt hu))).1]
    have hi1 : IntegrableOn (fun u => Real.exp (-((n + 1) * u)) * φ₁ u) (Ioi 0) := by
      refine (hexp.mul_const (2 * M)).mono' ((Real.continuous_exp.measurable.comp
        ((measurable_id.const_mul _).neg)).mul h1m).aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_))
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (hφ1 u hu)]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      simp only [hφ₁]; linarith [(abs_le.1 (hb1 u)).2]
    have hi2 : IntegrableOn (fun u => Real.exp (-((n + 1) * u)) * φ₂ u) (Ioi 0) := by
      refine (hexp.mul_const (2 * M)).mono' ((Real.continuous_exp.measurable.comp
        ((measurable_id.const_mul _).neg)).mul h2m).aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_))
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (hφ2 u hu)]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      simp only [hφ₂]; linarith [(abs_le.1 (hb2 u (le_of_lt hu))).2]
    have hconv : ∀ φ : ℝ → ℝ, (∀ u ∈ Ioi (0 : ℝ), 0 ≤ φ u) →
        IntegrableOn (fun u => Real.exp (-((n + 1) * u)) * φ u) (Ioi 0) →
        ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-((n + 1) * u))) * ENNReal.ofReal (φ u) =
          ENNReal.ofReal (∫ u in Ioi (0 : ℝ), Real.exp (-((n + 1) * u)) * φ u) := by
      intro φ h0 hi
      rw [ofReal_integral_eq_lintegral_ofReal hi ((ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun u hu => mul_nonneg (Real.exp_pos _).le (h0 u hu)))]
      exact setLIntegral_congr_fun measurableSet_Ioi fun u _ =>
        (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
    rw [hconv φ₁ hφ1 hi1, hconv φ₂ hφ2 hi2]
    congr 1
    -- the two real Laplace transforms
    have hsplit : ∀ g : ℝ → ℝ, IntegrableOn (fun u => Real.exp (-((n + 1) * u)) * g u) (Ioi 0) →
        ∫ u in Ioi (0 : ℝ), Real.exp (-((n + 1) * u)) * (g u + M) =
          (∫ u in Ioi (0 : ℝ), Real.exp (-((n + 1) * u)) * g u) + M / (n + 1) := by
      intro g hg
      have e : (fun u => Real.exp (-((n + 1) * u)) * (g u + M)) =
          fun u => Real.exp (-((n + 1) * u)) * g u + Real.exp (-((n + 1) * u)) * M := by
        funext u; ring
      rw [e, integral_add hg (hexp.mul_const M), integral_mul_const, setIntegral_exp_neg_mul hc]
      ring
    have hg1 : IntegrableOn (fun u => Real.exp (-((n + 1) * u)) *
        timeChangeTransition A (E.eigenfun i) u x) (Ioi 0) :=
      (hexp.mul_const M).mono' ((Real.continuous_exp.measurable.comp
        ((measurable_id.const_mul _).neg)).mul (measurable_timeChangeTransition hA.measurable hϕm
          x)).aestronglyMeasurable (Eventually.of_forall fun u => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
            exact mul_le_mul_of_nonneg_left (hb1 u) (Real.exp_pos _).le)
    have hc' : (0 : ℝ) < n + 1 + 1 / E.eig i := by positivity
    have hg2 : IntegrableOn (fun u => Real.exp (-((n + 1) * u)) *
        (Real.exp (-(u / E.eig i)) * E.eigenfun i x)) (Ioi 0) := by
      refine IntegrableOn.congr_fun ((integrableOn_exp_neg_mul hc').mul_const (E.eigenfun i x))
        (fun u _ => ?_) measurableSet_Ioi
      show Real.exp (-((n + 1 + 1 / E.eig i) * u)) * E.eigenfun i x =
        Real.exp (-((n + 1) * u)) * (Real.exp (-(u / E.eig i)) * E.eigenfun i x)
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    simp only [hφ₁, hφ₂]
    rw [hsplit _ hg1, hsplit _ hg2, ← resolventReal_eq_setIntegral hA.measurable hc hϕm hϕM x,
      resolventReal_eigenfun E hA i hc hx]
    congr 1
    have e2 : (fun u => Real.exp (-((n + 1) * u)) * (Real.exp (-(u / E.eig i)) * E.eigenfun i x)) =
        fun u => Real.exp (-((n + 1 + 1 / E.eig i) * u)) * E.eigenfun i x := by
      funext u
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [e2, integral_mul_const, setIntegral_exp_neg_mul hc']
    ring
  have hae := ae_eq_of_laplace_eq h1m h2m (fun u _ => by
      simp only [hφ₁]; linarith [(abs_le.1 (hb1 u)).1])
    (fun u hu => by simp only [hφ₂]; linarith [(abs_le.1 (hb2 u (le_of_lt hu))).1])
    (B := 2 * M) (fun u _ => by simp only [hφ₁]; linarith [(abs_le.1 (hb1 u)).2])
    (fun u hu => by simp only [hφ₂]; linarith [(abs_le.1 (hb2 u (le_of_lt hu))).2]) hlap
  have hae' : (fun u => timeChangeTransition A (E.eigenfun i) u x) =ᵐ[volume.restrict (Ioi 0)]
      fun u => Real.exp (-(u / E.eig i)) * E.eigenfun i x := by
    filter_upwards [hae] with u hu
    simp only [hφ₁, hφ₂] at hu
    linarith
  refine eq_of_ae_eq_of_continuousWithinAt hae' (fun u₀ _ =>
    continuousWithinAt_timeChangeTransition hA hϕm (E.continuousOn_eigenfun i) hϕM hx u₀)
    (fun u₀ _ => ((Real.continuous_exp.comp ((continuous_id.div_const _).neg)).mul
      continuous_const).continuousWithinAt) hu

end Eigen

end HarmonicBalls
