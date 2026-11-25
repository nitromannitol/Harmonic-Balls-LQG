import HarmonicBalls.Proofs.Potential.UniversalClock
import HarmonicBalls.Proofs.Potential.ReflectedBrownianFoldInvariance
import HarmonicBalls.Proofs.Potential.LQGClockAllStarts

/-!
# One clock of reflected Brownian motion in the unit square for the LQG clocks of a square

Let `F x` be LQG clocks of reflected Brownian motion in `K = closedSquare a L` from every
`x ∈ K`, for a field with continuous circle averages. Read through the path chart
`Ψ b = (t ↦ (b (L² t) - a)/L)` and divided by a constant `M > 0`, they become clocks of reflected
Brownian motion in the unit square from every start, limits of the transported approximations
`ã_k(b', u) = M⁻¹ a_k(Ψ⁻¹ b', L² u)`. The universal clock (`exists_universal_clock`) with the
standard Gaussian reference start, fold invariance and the Markov transfer of
`ReflectedBrownianFoldInvariance` gives one measurable functional `A` of unit-square paths such
that, from every start, `A` is almost surely zero at zero, continuous, nondecreasing and additive,
and `F x b s = M A(s / L², Ψ b)` almost surely (`exists_unitSquare_clock_of_isLQGClock`).
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

/-- The triangle wave takes values in `[0, 1]`. -/
theorem unitIntervalFold_mem_Icc (u : ℝ) : unitIntervalFold u ∈ Icc (0 : ℝ) 1 := by
  unfold unitIntervalFold
  refine ⟨div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le, ?_⟩
  rw [div_le_one Real.pi_pos]
  exact Real.arccos_le_pi _

/-- The fold onto the unit square takes values in the unit square. -/
theorem squareFold_zero_one_mem (z : ℂ) : squareFold 0 1 z ∈ closedSquare 0 1 := by
  rw [squareFold_zero_one_apply, closedSquare, Complex.mem_reProdIm]
  simpa using ⟨unitIntervalFold_mem_Icc z.re, unitIntervalFold_mem_Icc z.im⟩

/-- The path chart intertwines the time shifts. -/
theorem unitSquarePathChart_shift (a : ℂ) {L : ℝ} (hL : 0 < L) (b : ContinuousPath ℂ)
    (s : ℝ≥0) : unitSquarePathChart a hL (ContinuousPath.shift ((L ^ 2).toNNReal * s) b) =
      ContinuousPath.shift s (unitSquarePathChart a hL b) := by
  ext t
  simp only [unitSquarePathChart_apply, ContinuousPath.shift_apply, mul_add]

/-- The transported approximate clocks. -/
noncomputable def transportedClockApprox (γ : ℝ) (hε : ℝ → ℂ → ℝ) (a : ℂ) {L : ℝ} (hL : 0 < L)
    (M : ℝ) (k : ℕ) (b' : ContinuousPath ℂ) (u : ℝ≥0) : ℝ :=
  lqgClockApprox γ hε (dyadicScale k) ((unitSquarePathChart a hL).symm b') ((L ^ 2).toNNReal * u) / M

theorem isApproxClocks_transportedClockApprox {γ : ℝ} {hε : ℝ → ℂ → ℝ} (a : ℂ) {L : ℝ}
    (hL : 0 < L) {M : ℝ} (hM : 0 < M) (hc : ∀ k, Continuous (hε (dyadicScale k))) :
    IsApproxClocks (transportedClockApprox γ hε a hL M) where
  measurable k t :=
    ((measurable_lqgClockApprox_time (hc k) _).comp
      (unitSquarePathChart a hL).symm.continuous.measurable).div_const _
  continuous k b :=
    ((continuous_lqgClockApprox_dyadic (hc k) _).comp
      (continuous_const.mul continuous_id)).div_const _
  monotone k b s t hst := div_le_div_of_nonneg_right
    (lqgClockApprox_dyadic_mono (hc k) _ (mul_le_mul_right hst _)) hM.le
  map_zero k b := by simp [transportedClockApprox, lqgClockApprox_zero]
  shift k b s t := by
    simp only [transportedClockApprox, mul_add]
    have h := lqgClockApprox_dyadic_shift (γ := γ) (hc k) ((unitSquarePathChart a hL).symm b)
      ((L ^ 2).toNNReal * s) ((L ^ 2).toNNReal * t)
    have hs : ContinuousPath.shift ((L ^ 2).toNNReal * s) ((unitSquarePathChart a hL).symm b) =
        (unitSquarePathChart a hL).symm (ContinuousPath.shift s b) := by
      rw [Homeomorph.eq_symm_apply, unitSquarePathChart_shift, Homeomorph.apply_symm_apply]
    rw [hs] at h
    rw [h]
    ring

/-- **LQG clocks of reflected Brownian motion in a square, read in the unit square**, are limits
of the transported approximations. -/
theorem tendstoClockInMeasure_transported {γ : ℝ} {hε : ℝ → ℂ → ℝ} {a : ℂ} {L : ℝ} (hL : 0 < L)
    {M : ℝ} (hM : 0 < M) {x : ℂ} {Fx : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hx : IsLQGClock (reflectedPlanarBrownianMotion a L) γ hε x Fx) :
    TendstoClockInMeasure (reflectedPlanarBrownianMotion 0 1 ((x - a) / (L : ℂ)))
      (transportedClockApprox γ hε a hL M)
      (fun b' u => Fx ((unitSquarePathChart a hL).symm b') ((L ^ 2).toNNReal * u) / M) := by
  intro T η hη
  rw [← reflectedPlanarBrownianMotion_map_unitSquarePathChart a hL x]
  have hpre : ∀ k, ((reflectedPlanarBrownianMotion a L x).map (unitSquarePathChart a hL))
      {b' | ∃ u ≤ T, η ≤ |transportedClockApprox γ hε a hL M k b' u -
        Fx ((unitSquarePathChart a hL).symm b') ((L ^ 2).toNNReal * u) / M|} ≤
      reflectedPlanarBrownianMotion a L x {b | ∃ s ≤ (L ^ 2).toNNReal * T,
        M * η ≤ |lqgClockApprox γ hε (dyadicScale k) b s - Fx b s|} := by
    intro k
    rw [← (unitSquarePathChart a hL).toMeasurableEquiv_coe, MeasurableEquiv.map_apply]
    refine measure_mono fun b hb => ?_
    obtain ⟨u, hu, hη'⟩ := hb
    refine ⟨(L ^ 2).toNNReal * u, mul_le_mul_right hu _, ?_⟩
    simp only [transportedClockApprox, Homeomorph.toMeasurableEquiv_coe,
      Homeomorph.symm_apply_apply] at hη'
    rw [← sub_div, abs_div, abs_of_pos hM, le_div_iff₀ hM] at hη'
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hx ((L ^ 2).toNNReal * T) (M * η) (mul_pos hM hη)) (fun k => zero_le) hpre

/-- **One clock of reflected Brownian motion in the unit square for the LQG clocks of a square.**
For LQG clocks `F x` of reflected Brownian motion in `K = closedSquare a L` from every `x ∈ K`
(continuous circle averages) and `M > 0`, there is a measurable functional `A` of unit-square
paths which, from every start of the unit square, is almost surely zero at zero, continuous,
nondecreasing and additive, is adapted to every filtration to which the transported
approximations are adapted, and satisfies `F x b s = M A(s / L², Ψ b)` almost surely from every
`x ∈ K`. -/
theorem exists_unitSquare_clock_of_isLQGClock {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    (hc : ∀ k, Continuous (hε (dyadicScale k))) {a : ℂ} {L : ℝ} (hL : 0 < L) {M : ℝ}
    (hM : 0 < M) {F : ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : ∀ x ∈ closedSquare a L, IsLQGClock (reflectedPlanarBrownianMotion a L) γ hε x (F x)) :
    ∃ A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, (∀ t, Measurable (A t)) ∧
      (∀ x ∈ closedSquare 0 1, ∀ᵐ b ∂(reflectedPlanarBrownianMotion 0 1 x),
        A 0 b = 0 ∧ Continuous (fun t => A t b) ∧ Monotone (fun t => A t b)) ∧
      (∀ x ∈ closedSquare 0 1, ∀ s t, ∀ᵐ b ∂(reflectedPlanarBrownianMotion 0 1 x),
        A (t + s) b = A t b + A s (ContinuousPath.shift t b)) ∧
      (∀ m : ℝ≥0 → MeasurableSpace (ContinuousPath ℂ), Monotone m →
        (∀ k t, Measurable[m t] fun b => transportedClockApprox γ hε a hL M k b t) →
        ∀ t, Measurable[m t] (A t)) ∧
      ∀ x ∈ closedSquare a L, ∀ᵐ b ∂(reflectedPlanarBrownianMotion a L x), ∀ s : ℝ≥0,
        F x b s = M * (A (s / (L ^ 2).toNNReal) (unitSquarePathChart a hL b) : ℝ) := by
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  have hc0 : (L ^ 2).toNNReal ≠ 0 := (Real.toNNReal_pos.2 (by positivity)).ne'
  let G : ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ := fun x' b' u =>
    F (a + (L : ℂ) * x') ((unitSquarePathChart a hL).symm b') ((L ^ 2).toNNReal * u) / M
  have hchart : ∀ x' : ℂ, (a + (L : ℂ) * x' - a) / (L : ℂ) = x' := fun x' => by
    field_simp
    ring
  have hmemK : ∀ x' ∈ closedSquare 0 1, a + (L : ℂ) * x' ∈ closedSquare a L := by
    intro x' hx'
    have h := unitSquareChart_preimage_closedSquare (a := a) hL
    have : a + (L : ℂ) * x' ∈ (fun z : ℂ => (z - a) / (L : ℂ)) ⁻¹' closedSquare 0 1 := by
      simp only [mem_preimage, hchart]
      exact hx'
    rwa [h] at this
  have hG : ∀ x' ∈ closedSquare 0 1, TendstoClockInMeasure (reflectedPlanarBrownianMotion 0 1 x')
      (transportedClockApprox γ hε a hL M) (G x') := by
    intro x' hx'
    have := tendstoClockInMeasure_transported hL hM (hF _ (hmemK x' hx'))
    rwa [hchart] at this
  have href : ∀ᵐ w ∂(planarGaussian 0 1), ∃ G', TendstoClockInMeasure
      (reflectedPlanarBrownianMotion 0 1 w) (transportedClockApprox γ hε a hL M) G' :=
    Eventually.of_forall fun w => ⟨G (squareFold 0 1 w), by
      rw [← reflectedPlanarBrownianMotion_zero_one_squareFold w]
      exact hG _ (squareFold_zero_one_mem w)⟩
  have ha := isApproxClocks_transportedClockApprox (γ := γ) a hL hM hc
  obtain ⟨A, hAm, hAad, hAinc⟩ := exists_universal_clock (Q := reflectedPlanarBrownianMotion 0 1)
    (ρ := planarGaussian 0 1) ha hG href
    (fun x _ s hs S hS h => ae_reflected_shift_of_ae_ref (x := x) hs hS h)
  -- identification and regularity from every start of the unit square
  have hreg : ∀ x' ∈ closedSquare 0 1, ∀ᵐ b ∂(reflectedPlanarBrownianMotion 0 1 x'),
      (∀ u, (A u b : ℝ) = G x' b u) ∧ G x' b 0 = 0 ∧ Continuous (G x' b) ∧ Monotone (G x' b) := by
    intro x' hx'
    obtain ⟨φ, -, hae⟩ := ae_tendsto_of_tendstoClockInMeasure ha (hG x' hx') tendsto_id
    have h0 : ∀ᵐ b ∂(reflectedPlanarBrownianMotion 0 1 x'), G x' b 0 = 0 := by
      filter_upwards [hae] with b hb
      exact hb.2.1
    filter_upwards [IsApproxClocks.ae_eq_of_shift_zero (hAinc x' hx' 0) h0, hae] with b hb hb'
    exact ⟨hb, hb'.2⟩
  refine ⟨A, hAm, fun x' hx' => ?_, fun x' hx' s t => ?_, hAad, fun x hx => ?_⟩
  · filter_upwards [hreg x' hx'] with b ⟨hid, h0, hcont, hmono⟩
    refine ⟨?_, ?_, fun u v huv => ?_⟩
    · exact NNReal.coe_eq_zero.1 ((hid 0).trans h0)
    · refine continuous_induced_rng.2 ?_
      convert hcont using 1
      funext u
      exact hid u
    · have := hmono huv
      rw [← hid, ← hid] at this
      exact_mod_cast this
  · filter_upwards [hreg x' hx', hAinc x' hx' t] with b ⟨hid, _⟩ hshift
    have h := hshift s
    apply NNReal.eq
    rw [NNReal.coe_add, h, hid (t + s), hid t]
    ring
  · have hx' : (x - a) / (L : ℂ) ∈ closedSquare 0 1 := div_ofReal_mem_closedSquare_zero_one hL hx
    have hmap := reflectedPlanarBrownianMotion_map_unitSquarePathChart a hL x
    have h := hreg _ hx'
    rw [← hmap, (unitSquarePathChart a hL).measurableEmbedding.ae_map_iff] at h
    filter_upwards [h] with b ⟨hid, _⟩ s
    have hs := hid (s / (L ^ 2).toNNReal)
    simp only [G, Homeomorph.symm_apply_apply, mul_div_cancel₀ s hc0] at hs
    have hx'' : a + (L : ℂ) * ((x - a) / (L : ℂ)) = x := by
      field_simp
      ring
    rw [hx''] at hs
    rw [hs]
    field_simp

/-! ### Adaptedness -/

/-- A time integral of a continuous function of `u(s, x)`, continuous in `s` and measurable in
`x`, is measurable in `x`. -/
theorem measurable_intervalIntegral_comp {α : Type*} {m : MeasurableSpace α} {u : ℝ → α → ℂ}
    (hu_cont : ∀ x, Continuous fun s => u s x) (hu : ∀ s, Measurable (u s)) {φ : ℂ → ℝ}
    (hφ : Continuous φ) (T : ℝ) : Measurable fun x => ∫ s in (0 : ℝ)..T, φ (u s x) := by
  have hj : Measurable (Function.uncurry u) :=
    measurable_uncurry_of_continuous_of_measurable hu_cont hu
  have hs : StronglyMeasurable (Function.uncurry fun s x => φ (u s x)) :=
    (hφ.measurable.comp hj).stronglyMeasurable
  simp only [intervalIntegral]
  exact ((hs.integral_prod_left (μ := volume.restrict (Ioc 0 T))).measurable).sub
    ((hs.integral_prod_left (μ := volume.restrict (Ioc T 0))).measurable)

/-- The position at a time `r ≤ t` is measurable for the natural filtration at time `t`. -/
theorem measurable_eval_pathNaturalFiltration {r t : ℝ≥0} (hrt : r ≤ t) :
    Measurable[pathNaturalFiltration t] fun b : ContinuousPath ℂ => b r := by
  rw [measurable_iff_comap_le]
  exact le_iSup₂ (f := fun s (_ : s ≤ t) =>
    MeasurableSpace.comap (fun b : ContinuousPath ℂ => b s) inferInstance) r hrt

theorem pathNaturalFiltration_mono : Monotone pathNaturalFiltration := fun _ t hst =>
  iSup₂_le fun r hr => le_iSup₂ (f := fun r (_ : r ≤ t) =>
    MeasurableSpace.comap (fun b : ContinuousPath ℂ => b r) inferInstance) r (hr.trans hst)

/-- **The approximate clocks are adapted**: the approximate clock at time `T₀` is measurable for
the natural filtration at time `T₀`. -/
theorem measurable_lqgClockApprox_pathNaturalFiltration {γ : ℝ} {hε : ℝ → ℂ → ℝ} {ε : ℝ}
    (hc : Continuous (hε ε)) (T₀ : ℝ≥0) :
    Measurable[pathNaturalFiltration T₀] fun b => lqgClockApprox γ hε ε b T₀ := by
  have hφ : Continuous fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε z) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc))
  have hmeas := measurable_intervalIntegral_comp (m := pathNaturalFiltration T₀)
    (u := fun s b => b (min s.toNNReal T₀))
    (fun b => b.continuous.comp (continuous_real_toNNReal.min continuous_const))
    (fun s => measurable_eval_pathNaturalFiltration (min_le_right _ _)) hφ T₀
  have heq : (fun b => lqgClockApprox γ hε ε b T₀) = fun b => ∫ s in (0 : ℝ)..(T₀ : ℝ),
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b (min s.toNNReal T₀))) := by
    funext b
    unfold lqgClockApprox
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le T₀.coe_nonneg] at hs
    simp only [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hs.2)]
  rw [heq]
  exact hmeas

/-- The inverse path chart is measurable from the natural filtration at time `t` to the natural
filtration at time `L² t`. -/
theorem measurable_unitSquarePathChart_symm_pathNaturalFiltration (a : ℂ) {L : ℝ} (hL : 0 < L)
    (t : ℝ≥0) : @Measurable _ _ (pathNaturalFiltration t)
      (pathNaturalFiltration ((L ^ 2).toNNReal * t)) (unitSquarePathChart a hL).symm := by
  have hcpos : 0 < (L ^ 2).toNNReal := Real.toNNReal_pos.2 (by positivity)
  rw [measurable_iff_comap_le, MeasurableSpace.comap_iSup]
  refine iSup_le fun s => ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun hs => ?_
  rw [MeasurableSpace.comap_comp, ← measurable_iff_comap_le]
  have hfun : ((fun b : ContinuousPath ℂ => b s) ∘ (unitSquarePathChart a hL).symm) =
      fun b' => a + (L : ℂ) * b' (s / (L ^ 2).toNNReal) := by
    funext b'
    have h := eq_add_mul_unitSquarePathChart a hL ((unitSquarePathChart a hL).symm b')
      (s / (L ^ 2).toNNReal)
    rw [Homeomorph.apply_symm_apply, mul_div_cancel₀ s hcpos.ne'] at h
    exact h
  rw [hfun]
  have hst : s / (L ^ 2).toNNReal ≤ t := by
    rw [div_le_iff₀ hcpos, mul_comm]
    exact hs
  exact measurable_const.add (measurable_const.mul (measurable_eval_pathNaturalFiltration hst))

/-- **The transported approximate clocks are adapted.** -/
theorem measurable_transportedClockApprox_pathNaturalFiltration {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    (hc : ∀ k, Continuous (hε (dyadicScale k))) (a : ℂ) {L : ℝ} (hL : 0 < L) (M : ℝ) (k : ℕ)
    (t : ℝ≥0) : Measurable[pathNaturalFiltration t]
      fun b' => transportedClockApprox γ hε a hL M k b' t := by
  unfold transportedClockApprox
  exact ((measurable_lqgClockApprox_pathNaturalFiltration (hc k) _).comp
    (measurable_unitSquarePathChart_symm_pathNaturalFiltration a hL t)).div_const _

theorem pathTimeShift_eq_shift (b : ContinuousPath ℂ) (t : ℝ≥0) :
    pathTimeShift b t = ContinuousPath.shift t b := by
  ext u
  rfl

/-- **The LQG clocks of a square are one positive continuous additive functional of reflected
Brownian motion in the unit square**: for LQG clocks `F x` of reflected Brownian motion in
`K = closedSquare a L` from every `x ∈ K` (continuous circle averages) and `M > 0`, there is
`A` with `IsUnitSquarePCAF A` and `F x b s = M A(s / L², Ψ b)` almost surely from every `x ∈ K`. -/
theorem exists_isUnitSquarePCAF_of_isLQGClock {γ : ℝ} {hε : ℝ → ℂ → ℝ}
    (hc : ∀ k, Continuous (hε (dyadicScale k))) {a : ℂ} {L : ℝ} (hL : 0 < L) {M : ℝ}
    (hM : 0 < M) {F : ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : ∀ x ∈ closedSquare a L, IsLQGClock (reflectedPlanarBrownianMotion a L) γ hε x (F x)) :
    ∃ A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsUnitSquarePCAF A ∧
      ∀ x ∈ closedSquare a L, ∀ᵐ b ∂(reflectedPlanarBrownianMotion a L x), ∀ s : ℝ≥0,
        F x b s = M * (A (s / (L ^ 2).toNNReal) (unitSquarePathChart a hL b) : ℝ) := by
  obtain ⟨A, hAm, hpath, hadd, hAad, hFA⟩ := exists_unitSquare_clock_of_isLQGClock hc hL hM hF
  refine ⟨A, ⟨hAm, fun x _ t => ⟨A t, hAad pathNaturalFiltration pathNaturalFiltration_mono
    (measurable_transportedClockApprox_pathNaturalFiltration hc a hL M) t, ae_eq_refl _⟩,
    hpath, fun x hx s t => ?_⟩, hFA⟩
  filter_upwards [hadd x hx s t] with b hb
  rw [pathTimeShift_eq_shift]
  exact hb

end HarmonicBalls

