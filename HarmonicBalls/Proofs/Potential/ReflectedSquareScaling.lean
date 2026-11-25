import HarmonicBalls.Proofs.Potential.SquareClippedBallVolume
import HarmonicBalls.Proofs.Potential.LQGClockSquareVisitComparison
import HarmonicBalls.Proofs.Sec6.ExitTimeSpatialMap

/-!
# Scaling of reflected Liouville Brownian motion from the unit square to any square

The proof of Proposition 2.6 (corrected paper lines 563-567) passes from the unit square
`K₀ = [0, 1]²` to a square `K = a + L K₀` by "a scaling argument". This module proves it.

* The fold onto `K` is the affine image of the fold onto `K₀` (`squareFold_eq_affine`), so
  reflected Brownian motion in `K` from `x`, seen through the path chart
  `Ψ b = (t ↦ L⁻¹ (b (L² t) - a))` (`unitSquarePathChart`), is reflected Brownian motion in `K₀`
  from `(x - a)/L` (`reflectedPlanarBrownianMotion_map_unitSquarePathChart`), by Brownian scaling.
* If the clock of the process in `K` is `M` times the clock of the process in `K₀` read through
  `Ψ`, with the time change `s ↦ s / L²`, where `M = m(K)`, then the inverse clocks satisfy
  `F⁻¹(t) = L² F'⁻¹(t / M)` (`clockInverse_mul_comp_div`), the Liouville Brownian path in `K` is the
  affine image of the one in `K₀` at time `t / M`, and a heat kernel `p'` of the process in `K₀`
  with respect to the normalized measure `ν = m(K)⁻¹ ((z - a)/L)_* (m|_K)`
  (`unitSquareNormalizedMeasure`) gives the heat kernel
  `p(t, x, y) = M⁻¹ p'(t / M, (x - a)/L, (y - a)/L)` of the process in `K` with respect to `m`
  (`isLBMHeatKernel_of_unitSquare`), jointly continuous and strictly positive when `p'` is.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Metric Set MarkovProcess
open scoped ENNReal NNReal

/-- The fold onto a square is the affine image of the fold onto the unit square. -/
theorem squareFold_eq_affine (a : ℂ) (L : ℝ) (z : ℂ) :
    squareFold a L z = a + (L : ℂ) * squareFold 0 1 ((z - a) / (L : ℂ)) := by
  apply Complex.ext <;>
    simp [squareFold, Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.mul_re, Complex.mul_im]

/-- The chart `z ↦ (z - a)/L` is `affineScaling`. -/
theorem div_ofReal_eq_affineScaling {a : ℂ} {L : ℝ} (hL : 0 < L) (z : ℂ) :
    (z - a) / (L : ℂ) = affineScaling hL a z := by
  rw [affineScaling_apply, Complex.real_smul, Complex.ofReal_inv, div_eq_inv_mul]

/-- The unit-square chart of paths `b ↦ (t ↦ L⁻¹ (b (L² t) - a))`. -/
noncomputable def unitSquarePathChart (a : ℂ) {L : ℝ} (hL : 0 < L) :
    ContinuousPath ℂ ≃ₜ ContinuousPath ℂ :=
  Section6.spacetimePathHomeomorph (affineScaling hL a) (L ^ 2).toNNReal
    (Real.toNNReal_pos.2 (by positivity))

theorem unitSquarePathChart_apply (a : ℂ) {L : ℝ} (hL : 0 < L) (b : ContinuousPath ℂ)
    (t : ℝ≥0) : unitSquarePathChart a hL b t = (b ((L ^ 2).toNNReal * t) - a) / (L : ℂ) := by
  rw [unitSquarePathChart, Section6.spacetimePathHomeomorph_apply, div_ofReal_eq_affineScaling hL]

/-- A path is recovered from its chart: `b (L² t) = a + L Ψ b (t)`. -/
theorem eq_add_mul_unitSquarePathChart (a : ℂ) {L : ℝ} (hL : 0 < L) (b : ContinuousPath ℂ)
    (t : ℝ≥0) : b ((L ^ 2).toNNReal * t) = a + (L : ℂ) * unitSquarePathChart a hL b t := by
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  rw [unitSquarePathChart_apply]
  field_simp
  ring

/-- **Reflected Brownian motion in a square is the scaled image of reflected Brownian motion in
the unit square.** -/
theorem reflectedPlanarBrownianMotion_map_unitSquarePathChart (a : ℂ) {L : ℝ} (hL : 0 < L)
    (x : ℂ) : (reflectedPlanarBrownianMotion a L x).map (unitSquarePathChart a hL) =
      reflectedPlanarBrownianMotion 0 1 ((x - a) / (L : ℂ)) := by
  rw [reflectedPlanarBrownianMotion, Kernel.map_apply _ (measurable_comp_squareFoldCM a L),
    Measure.map_map (unitSquarePathChart a hL).continuous.measurable
      (measurable_comp_squareFoldCM a L),
    reflectedPlanarBrownianMotion, Kernel.map_apply _ (measurable_comp_squareFoldCM 0 1),
    div_ofReal_eq_affineScaling hL, affineScaling_apply,
    ← planarBrownianMotion_map_rescale_affineScaling hL a x,
    Measure.map_map (measurable_comp_squareFoldCM 0 1)
      (ContinuousPath.continuous_rescale _ _).measurable]
  congr 1
  funext b
  ext t
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  simp only [Function.comp_apply, ContinuousMap.comp_apply, ContinuousPath.rescale_apply]
  rw [unitSquarePathChart_apply, ← div_ofReal_eq_affineScaling hL]
  change (squareFold a L (b ((L ^ 2).toNNReal * t)) - a) / (L : ℂ) =
    squareFold 0 1 ((b ((L ^ 2).toNNReal * t) - a) / (L : ℂ))
  rw [squareFold_eq_affine a L]
  field_simp
  ring

/-- **Scaling of the inverse clock**: if `f(s) = M g(s / c)` with `c, M > 0`, then
`f⁻¹(t) = c g⁻¹(t / M)`. -/
theorem clockInverse_mul_comp_div (g : ℝ≥0 → ℝ) {c M : ℝ≥0} (hc : 0 < c) (hM : 0 < M)
    (t : ℝ≥0) : clockInverse (fun s => (M : ℝ) * g (s / c)) t = c * clockInverse g (t / M) := by
  unfold clockInverse
  have hset : {s : ℝ≥0 | (t : ℝ) < M * g (s / c)} =
      (OrderIso.mulLeft₀ c hc) '' {u : ℝ≥0 | ((t / M : ℝ≥0) : ℝ) < g u} := by
    ext s
    simp only [mem_ofPred_eq, mem_image, OrderIso.mulLeft₀_apply, NNReal.coe_div]
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    constructor
    · intro h
      refine ⟨s / c, ?_, mul_div_cancel₀ s hc.ne'⟩
      rw [div_lt_iff₀' hM']
      exact h
    · rintro ⟨u, hu, rfl⟩
      rw [mul_div_cancel_left₀ u hc.ne']
      rw [div_lt_iff₀' hM'] at hu
      exact hu
  rw [hset]
  rcases eq_empty_or_nonempty {u : ℝ≥0 | ((t / M : ℝ≥0) : ℝ) < g u} with h | h
  · rw [h, image_empty, NNReal.sInf_empty, mul_zero]
  · rw [← (OrderIso.mulLeft₀ c hc).map_csInf' h (OrderBot.bddBelow _), OrderIso.mulLeft₀_apply]

/-- **The Liouville Brownian path in a square is the affine image of the one in the unit
square** under the clock relation of `isLBMHeatKernel_of_unitSquare`. -/
theorem liouvilleBrownianPath_eq_of_clock_eq {a : ℂ} {L : ℝ} (hL : 0 < L) {M : ℝ≥0} (hM : 0 < M)
    {f : ContinuousPath ℂ → ℝ≥0 → ℝ} {g : ContinuousPath ℂ → ℝ≥0 → ℝ} {b : ContinuousPath ℂ}
    (h : ∀ s : ℝ≥0, f b s = M * g (unitSquarePathChart a hL b) (s / (L ^ 2).toNNReal))
    (t : ℝ≥0) : liouvilleBrownianPath f b t =
      a + (L : ℂ) * liouvilleBrownianPath g (unitSquarePathChart a hL b) (t / M) := by
  have hc : 0 < (L ^ 2).toNNReal := Real.toNNReal_pos.2 (by positivity)
  have hfb : f b = fun s => (M : ℝ) * g (unitSquarePathChart a hL b) (s / (L ^ 2).toNNReal) :=
    funext h
  rw [liouvilleBrownianPath, hfb, clockInverse_mul_comp_div _ hc hM,
    eq_add_mul_unitSquarePathChart a hL b, liouvilleBrownianPath]

/-- The chart point of a point of the square lies in the unit square. -/
theorem div_ofReal_mem_closedSquare_zero_one {a x : ℂ} {L : ℝ} (hL : 0 < L)
    (hx : x ∈ closedSquare a L) : (x - a) / (L : ℂ) ∈ closedSquare 0 1 := by
  have h := unitSquareChart_preimage_closedSquare (a := a) hL
  rw [← h] at hx
  exact hx

/-- **The heat kernel of reflected Liouville Brownian motion in a square from the unit square.**
If the clocks `F` of reflected Brownian motion in `K = closedSquare a L` are `M = m(K)` times the
clocks `F'` in the unit square read through the path chart with time `s / L²`, then a heat kernel
`p'` of the unit-square process with respect to `unitSquareNormalizedMeasure m a L` gives the heat
kernel `p(t, x, y) = M⁻¹ p'(t / M, (x - a)/L, (y - a)/L)` of the process in `K` with respect to
`m`. -/
theorem isLBMHeatKernel_of_unitSquare {a : ℂ} {L : ℝ} (hL : 0 < L) {m : Measure ℂ}
    (hpos : 0 < m (closedSquare a L)) (hfin : m (closedSquare a L) < ⊤)
    {F F' : ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ} {p' : ℝ → ℂ → ℂ → ℝ}
    (hp' : IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) F' (closedSquare 0 1)
      (unitSquareNormalizedMeasure m a L) p')
    (hF : ∀ x ∈ closedSquare a L, ∀ᵐ b ∂(reflectedPlanarBrownianMotion a L x), ∀ s : ℝ≥0,
      F x b s = (m (closedSquare a L)).toReal *
        F' ((x - a) / (L : ℂ)) (unitSquarePathChart a hL b) (s / (L ^ 2).toNNReal)) :
    IsLBMHeatKernel (reflectedPlanarBrownianMotion a L) F (closedSquare a L) m
      (fun t x y => ((m (closedSquare a L)).toReal)⁻¹ *
        p' (t / (m (closedSquare a L)).toReal) ((x - a) / (L : ℂ)) ((y - a) / (L : ℂ))) := by
  set K := closedSquare a L with hK
  set M := (m K).toReal with hMdef
  have hM0 : 0 < M := ENNReal.toReal_pos hpos.ne' hfin.ne
  set M' : ℝ≥0 := M.toNNReal with hM'def
  have hM'0 : 0 < M' := Real.toNNReal_pos.2 hM0
  have hM'coe : (M' : ℝ) = M := Real.coe_toNNReal _ hM0.le
  set Ψ := unitSquarePathChart a hL with hΨ
  set χ : ℂ → ℂ := fun z => (z - a) / (L : ℂ) with hχ
  have hχe : χ = affineScaling hL a := funext (div_ofReal_eq_affineScaling hL)
  intro t ht x hx
  have hχx : χ x ∈ closedSquare 0 1 := div_ofReal_mem_closedSquare_zero_one hL hx
  have htM : 0 < t / M := div_pos ht hM0
  obtain ⟨hnn', hlaw'⟩ := hp' (t / M) htM (χ x) hχx
  refine ⟨fun y hy => mul_nonneg (inv_nonneg.2 hM0.le)
    (hnn' _ (div_ofReal_mem_closedSquare_zero_one hL hy)), fun S hS => ?_⟩
  -- the Liouville Brownian path in `K` is the affine image of the one in the unit square
  set T : ℂ → ℂ := fun y => a + (L : ℂ) * y with hT
  have hTm : Measurable T := (continuous_const.add (continuous_const.mul continuous_id)).measurable
  have htt : (t / M).toNNReal = t.toNNReal / M' := Real.toNNReal_div ht.le
  have hae : {b | liouvilleBrownianPath (F x) b t.toNNReal ∈ S} =ᵐ[reflectedPlanarBrownianMotion a L x]
      Ψ ⁻¹' {b' | liouvilleBrownianPath (F' (χ x)) b' (t / M).toNNReal ∈ T ⁻¹' S} := by
    filter_upwards [hF x hx] with b hb
    have hb' : ∀ s : ℝ≥0, F x b s = (M' : ℝ) * F' (χ x) (Ψ b) (s / (L ^ 2).toNNReal) := by
      intro s
      rw [hM'coe]
      exact hb s
    have hpath := liouvilleBrownianPath_eq_of_clock_eq hL hM'0 hb' t.toNNReal
    apply propext
    simp only [mem_ofPred_eq, mem_preimage, hT, htt]
    rw [hpath]
  rw [measure_congr hae]
  -- transport by the chart of paths
  have hmap := reflectedPlanarBrownianMotion_map_unitSquarePathChart a hL x
  have hΨe : (reflectedPlanarBrownianMotion a L x) (Ψ ⁻¹' {b' | liouvilleBrownianPath (F' (χ x)) b'
      (t / M).toNNReal ∈ T ⁻¹' S}) = (reflectedPlanarBrownianMotion 0 1 (χ x))
        {b' | liouvilleBrownianPath (F' (χ x)) b' (t / M).toNNReal ∈ T ⁻¹' S} := by
    rw [← hmap, ← Ψ.toMeasurableEquiv_coe, MeasurableEquiv.map_apply]
  rw [hΨe, hlaw' _ (hTm hS)]
  -- change variables in the integral against the normalized measure
  have hχm : MeasurableEmbedding χ := by
    rw [hχe]
    exact (affineScaling hL a).measurableEmbedding
  have hset : χ ⁻¹' (T ⁻¹' S ∩ closedSquare 0 1) ∩ K = S ∩ K := by
    have hTχ : ∀ z, T (χ z) = z := by
      intro z
      have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
      simp only [hT, hχ]
      field_simp
      ring
    rw [preimage_inter, unitSquareChart_preimage_closedSquare hL]
    ext z
    simp only [mem_inter_iff, mem_preimage, hTχ]
    tauto
  have hKm : MeasurableSet K := (isCompact_closedSquare a L).isClosed.measurableSet
  have hinv : (m K)⁻¹ = ENNReal.ofReal M⁻¹ := by
    rw [hMdef, ENNReal.ofReal_inv_of_pos hM0, ENNReal.ofReal_toReal hfin.ne]
  rw [unitSquareNormalizedMeasure, Measure.restrict_smul, lintegral_smul_measure,
    Measure.restrict_map hχm.measurable ((hTm hS).inter
      (isCompact_closedSquare 0 1).isClosed.measurableSet), hχm.lintegral_map,
    Measure.restrict_restrict (hχm.measurable ((hTm hS).inter
      (isCompact_closedSquare 0 1).isClosed.measurableSet)), hset, ← hK, hinv, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun (hS.inter hKm) fun y _ => ?_
  simp only [hχ]
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 hM0.le)]

/-- Joint continuity passes from the unit square to the square. -/
theorem continuousOn_scaled_kernel {a : ℂ} {L : ℝ} (hL : 0 < L) {M : ℝ} (hM : 0 < M)
    {p' : ℝ → ℂ → ℂ → ℝ}
    (hc : ContinuousOn (fun s : ℝ × ℂ × ℂ => p' s.1 s.2.1 s.2.2)
      (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1)) :
    ContinuousOn (fun s : ℝ × ℂ × ℂ => M⁻¹ * p' (s.1 / M) ((s.2.1 - a) / (L : ℂ))
      ((s.2.2 - a) / (L : ℂ))) (Ioi 0 ×ˢ closedSquare a L ×ˢ closedSquare a L) := by
  have hφ : Continuous (fun s : ℝ × ℂ × ℂ => (s.1 / M, (s.2.1 - a) / (L : ℂ),
      (s.2.2 - a) / (L : ℂ))) := by fun_prop
  refine continuousOn_const.mul (hc.comp hφ.continuousOn ?_)
  rintro ⟨t, x, y⟩ ⟨ht, hx, hy⟩
  exact ⟨div_pos ht hM, div_ofReal_mem_closedSquare_zero_one hL hx,
    div_ofReal_mem_closedSquare_zero_one hL hy⟩

/-- Strict positivity passes from the unit square to the square. -/
theorem scaled_kernel_pos {a : ℂ} {L : ℝ} (hL : 0 < L) {M : ℝ} (hM : 0 < M) {p' : ℝ → ℂ → ℂ → ℝ}
    (hp : ∀ t : ℝ, 0 < t → ∀ x ∈ closedSquare 0 1, ∀ y ∈ closedSquare 0 1, 0 < p' t x y)
    {t : ℝ} (ht : 0 < t) {x y : ℂ} (hx : x ∈ closedSquare a L) (hy : y ∈ closedSquare a L) :
    0 < M⁻¹ * p' (t / M) ((x - a) / (L : ℂ)) ((y - a) / (L : ℂ)) :=
  mul_pos (inv_pos.2 hM) (hp _ (div_pos ht hM) _ (div_ofReal_mem_closedSquare_zero_one hL hx) _
    (div_ofReal_mem_closedSquare_zero_one hL hy))

/-- **Proposition 2.6 from the clock identification and positivity on the unit square.** Let
`F` be clocks of reflected Brownian motion in `K = closedSquare a L`. Suppose that almost surely
there is a positive continuous additive functional `A` of reflected Brownian motion in the unit
square whose Revuz measure is the normalized LQG measure of `K` carried to the unit square, with
`F ω x b s = μ_h(K) A(s / L², Ψ b)` almost surely from every start `x ∈ K` (the clock
identification), and that every jointly continuous heat kernel of such a time change is strictly
positive (positivity). Then, from Kigami's Theorem 13.1 (`kigamiHeatKernelContinuityCited`), the
volume bounds (13.1) (`ae_forall_closedSquare_kigamiVolumeBounds`) and the scaling
(`isLBMHeatKernel_of_unitSquare`), almost surely the heat kernel of reflected Liouville Brownian
motion in `K` with respect to `μ_h` exists, is jointly continuous and strictly positive on
`(0, ∞) × K × K`: the conclusion of `ReflectedLBMHeatKernelStmt`. -/
theorem reflectedLBMHeatKernel_of_identification (hKig : kigamiHeatKernelContinuityCited)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {a : ℂ} {L : ℝ} (hL : 0 < L) (F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hid : ∀ᵐ ω ∂P, ∃ A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0, IsUnitSquarePCAF A ∧
      unitSquareRevuzMeasure A = unitSquareNormalizedMeasure (μ ω) a L ∧
      ∀ x ∈ closedSquare a L, ∀ᵐ b ∂(reflectedPlanarBrownianMotion a L x), ∀ s : ℝ≥0,
        F ω x b s = (μ ω (closedSquare a L)).toReal *
          (A (s / (L ^ 2).toNNReal) (unitSquarePathChart a hL b) : ℝ))
    (hpos : ∀ᵐ ω ∂P, ∀ (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (p' : ℝ → ℂ → ℂ → ℝ),
      IsUnitSquarePCAF A → unitSquareRevuzMeasure A = unitSquareNormalizedMeasure (μ ω) a L →
      IsLBMHeatKernel (reflectedPlanarBrownianMotion 0 1) (fun _ b t => (A t b : ℝ))
        (closedSquare 0 1) (unitSquareNormalizedMeasure (μ ω) a L) p' →
      ContinuousOn (fun s : ℝ × ℂ × ℂ => p' s.1 s.2.1 s.2.2)
        (Ioi 0 ×ˢ closedSquare 0 1 ×ˢ closedSquare 0 1) →
      ∀ t : ℝ, 0 < t → ∀ x ∈ closedSquare 0 1, ∀ y ∈ closedSquare 0 1, 0 < p' t x y) :
    ∀ᵐ ω ∂P, ∃ p : ℝ → ℂ → ℂ → ℝ,
      IsLBMHeatKernel (reflectedPlanarBrownianMotion a L) (F ω) (closedSquare a L) (μ ω) p ∧
      ContinuousOn (fun s : ℝ × ℂ × ℂ => p s.1 s.2.1 s.2.2)
        (Ioi 0 ×ˢ closedSquare a L ×ˢ closedSquare a L) ∧
      ∀ t : ℝ, 0 < t → ∀ x ∈ closedSquare a L, ∀ y ∈ closedSquare a L, 0 < p t x y := by
  filter_upwards [ae_forall_closedSquare_heatKernel_of_kigami hKig hγ hγ2 hα hh hμ,
    ae_forall_closedSquare_volume_bounds hγ hγ2 hα hh hμ, hid, hpos] with ω hker hvol hidω hposω
  obtain ⟨A, hA, hRev, hFA⟩ := hidω
  obtain ⟨p', hp', hcont'⟩ := hker a L hL A hA hRev
  obtain ⟨hKpos, hKfin, -⟩ := hvol a L hL
  have hM : 0 < (μ ω (closedSquare a L)).toReal := ENNReal.toReal_pos hKpos.ne' hKfin.ne
  refine ⟨_, isLBMHeatKernel_of_unitSquare hL hKpos hKfin (F' := fun _ b t => (A t b : ℝ)) hp' hFA,
    continuousOn_scaled_kernel hL hM hcont', fun t ht x hx y hy =>
      scaled_kernel_pos hL hM (hposω A p' hA hRev hp' hcont') ht hx hy⟩

end HarmonicBalls

