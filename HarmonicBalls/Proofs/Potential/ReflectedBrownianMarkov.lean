import HarmonicBalls.Proofs.Potential.ReflectedLebesgueInvariance

/-!
# The Markov property of reflected Brownian motion in the unit square and occupation integrals

Reflected Brownian motion in the unit square `K₀ = [0, 1]²` from `x` is the fold `fold ∘ W` of a
planar Brownian motion `W` from `x`. Since the fold commutes with the time shifts and reflected
Brownian motion from `w` only depends on `fold w` (`reflectedPlanarBrownianMotion_zero_one_squareFold`),
the simple Markov property of planar Brownian motion at a fixed time `s` gives
`E_x[g(b_s) Ψ(θ_s b)] = ∫ g(fold w) E_w[Ψ] N(x, s)(dw)` (`lintegral_reflected_eval_mul_shift`).

For the occupation integral `I(b) = ∫_{(0,1]} g(b_s) ds` (`windowOccupation`) this gives the
second moment bound of Khas'minskii type: if `E_y[I] ≤ U` for every `y ∈ K₀`, then
`E_x[I²] ≤ 2 U E_x[I]` for every start `x` (`lintegral_windowOccupation_sq_le`).

Credit: the planar Markov property at a fixed time, the pathwise symmetrization of the square of a
window integral and the second moment bound follow `planarBrownianMotion_map_shift`,
`lintegral_eval_mul_shift`, `sq_setLIntegral_Ioc_le` and `lintegral_windowOcc_sq_le` of the
IDLA-Mated-CRT formalization (MatedCRT/FirstPass/Derived/LBMApproxRestart.lean and
MatedCRT/FirstPass/Derived/PlanarOccupationSecondMoment.lean), written there for planar Brownian
motion.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

/-! ### The Markov property at a fixed time -/

/-- **Simple Markov property of planar Brownian motion at a fixed time**: the law of the shifted
path `θ_δ b` under planar Brownian motion from `z` is planar Brownian motion started from the heat
kernel at time `δ`. -/
theorem planarBrownianMotion_map_shift_eq_comp (z : ℂ) (δ : ℝ≥0) :
    (planarBrownianMotion z).map (ContinuousPath.shift δ) =
      planarBrownianMotion ∘ₘ planarHeatSemigroup δ z := by
  have h := congrArg (fun K => K z)
    (SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_shift
      planarHeatSemigroup isConservative_planarHeatSemigroup
      isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup δ)
  rw [ProbabilityTheory.Kernel.map_apply _ (ContinuousPath.measurable_shift_fixed δ) z,
    ProbabilityTheory.Kernel.comp_apply] at h
  rw [planarBrownianMotion_eq_continuousProcess]
  exact h

/-- **Simple Markov property of planar Brownian motion at a fixed time, position-weighted form**:
`E_z[g(b_s) Ψ(θ_s b)] = ∫ g(y) E_y[Ψ] N(z, s)(dy)`. -/
theorem lintegral_planarBrownianMotion_eval_mul_shift {g : ℂ → ℝ≥0∞} (hg : Measurable g)
    {Ψ : ContinuousPath ℂ → ℝ≥0∞} (hΨ : Measurable Ψ) (s : ℝ≥0) (z : ℂ) :
    ∫⁻ b, g (b s) * Ψ (ContinuousPath.shift s b) ∂planarBrownianMotion z =
      ∫⁻ y, g y * ∫⁻ b, Ψ b ∂planarBrownianMotion y ∂planarGaussian z s := by
  have hΦ : Measurable fun b : ContinuousPath ℂ => g (b 0) * Ψ b :=
    (hg.comp (continuous_eval_const 0).measurable).mul hΨ
  have h1 : ∫⁻ b, g (b s) * Ψ (ContinuousPath.shift s b) ∂planarBrownianMotion z =
      ∫⁻ b', g (b' 0) * Ψ b' ∂(planarBrownianMotion z).map (ContinuousPath.shift s) := by
    rw [lintegral_map hΦ (ContinuousPath.measurable_shift_fixed s)]
    simp only [ContinuousPath.shift_apply, add_zero]
  rw [h1, planarBrownianMotion_map_shift_eq_comp z s,
    Measure.lintegral_bind (planarBrownianMotion.measurable.aemeasurable) hΦ.aemeasurable,
    planarHeatSemigroup_apply]
  refine lintegral_congr fun y => ?_
  rw [← lintegral_const_mul _ hΨ]
  exact lintegral_congr_ae (by
    filter_upwards [ae_planarBrownianMotion_eval_zero y] with b hb
    rw [hb])

/-- **Simple Markov property of reflected Brownian motion in the unit square at a fixed time**:
`E_x[g(b_s) Ψ(θ_s b)] = ∫ g(fold w) E_w[Ψ] N(x, s)(dw)`. -/
theorem lintegral_reflected_eval_mul_shift {g : ℂ → ℝ≥0∞} (hg : Measurable g)
    {Ψ : ContinuousPath ℂ → ℝ≥0∞} (hΨ : Measurable Ψ) (s : ℝ≥0) (x : ℂ) :
    ∫⁻ b, g (b s) * Ψ (ContinuousPath.shift s b) ∂(reflectedPlanarBrownianMotion 0 1 x) =
      ∫⁻ w, g (squareFold 0 1 w) * ∫⁻ b, Ψ b ∂(reflectedPlanarBrownianMotion 0 1 w)
        ∂(planarGaussian x s) := by
  have hF := measurable_comp_squareFoldCM 0 1
  have hfold : Measurable (squareFold 0 1) := (continuous_squareFold 0 1).measurable
  have hQ : ∀ y, reflectedPlanarBrownianMotion 0 1 y =
      (planarBrownianMotion y).map fun b => (squareFoldCM 0 1).comp b := fun y => by
    rw [reflectedPlanarBrownianMotion, Kernel.map_apply _ hF]
  have hint : ∀ b : ContinuousPath ℂ, g (((squareFoldCM 0 1).comp b) s) *
      Ψ (ContinuousPath.shift s ((squareFoldCM 0 1).comp b)) =
      g (squareFold 0 1 (b s)) * Ψ ((squareFoldCM 0 1).comp (ContinuousPath.shift s b)) :=
    fun b => rfl
  have hm : Measurable fun b : ContinuousPath ℂ => g (b s) * Ψ (ContinuousPath.shift s b) :=
    (hg.comp (continuous_eval_const s).measurable).mul
      (hΨ.comp (ContinuousPath.measurable_shift_fixed s))
  rw [hQ x, lintegral_map hm hF]
  refine (lintegral_congr hint).trans
    ((lintegral_planarBrownianMotion_eval_mul_shift (g := fun w => g (squareFold 0 1 w))
      (hg.comp hfold) (Ψ := fun b => Ψ ((squareFoldCM 0 1).comp b)) (hΨ.comp hF) s x).trans
      (lintegral_congr fun y => ?_))
  rw [hQ y, lintegral_map hΨ hF]

/-- The marginal of reflected Brownian motion at a fixed time, integral form:
`E_x[v(b_s)] = ∫ v(fold w) N(x, s)(dw)`. -/
theorem lintegral_reflected_eval_eq (s : ℝ≥0) {v : ℂ → ℝ≥0∞} (hv : Measurable v) (x : ℂ) :
    ∫⁻ b, v (b s) ∂(reflectedPlanarBrownianMotion 0 1 x) =
      ∫⁻ w, v (squareFold 0 1 w) ∂(planarGaussian x s) := by
  have hev : Measurable fun b : ContinuousPath ℂ => b s := (continuous_eval_const s).measurable
  calc ∫⁻ b, v (b s) ∂(reflectedPlanarBrownianMotion 0 1 x)
      = ∫⁻ y, v y ∂((reflectedPlanarBrownianMotion 0 1 x).map fun b => b s) :=
        (lintegral_map hv hev).symm
    _ = ∫⁻ y, v y ∂((planarGaussian x s).map (squareFold 0 1)) := by
        rw [reflectedPlanarBrownianMotion_zero_one_map_eval]
    _ = ∫⁻ w, v (squareFold 0 1 w) ∂(planarGaussian x s) :=
        lintegral_map hv (continuous_squareFold 0 1).measurable

/-! ### Occupation integrals over the unit time window -/

/-- Joint measurability of the evaluation `(t, b) ↦ b t` of the canonical path. -/
theorem measurable_path_eval_uncurry :
    Measurable fun p : ℝ≥0 × ContinuousPath ℂ => p.2 p.1 :=
  measurable_uncurry_of_continuous_of_measurable
    (u := fun (t : ℝ≥0) (ω : ContinuousPath ℂ) => ω t)
    (fun ω => ω.continuous) (fun t => (continuous_eval_const t).measurable)

/-- Joint measurability of the path evaluation at a real time. -/
theorem measurable_eval_toNNReal_uncurry {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun p : ℝ × ContinuousPath ℂ => g (p.2 p.1.toNNReal) :=
  hg.comp (measurable_path_eval_uncurry.comp
    ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))

/-- The occupation integral `∫_{(0,1]} g(b_s) ds` of `g` along the path `b` over the time window
`(0, 1]`. -/
noncomputable def windowOccupation (g : ℂ → ℝ≥0∞) (b : ContinuousPath ℂ) : ℝ≥0∞ :=
  ∫⁻ s in Ioc (0 : ℝ) 1, g (b s.toNNReal)

/-- The window occupation integral is measurable in the path. -/
theorem measurable_windowOccupation {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    Measurable (windowOccupation g) := by
  have h : Measurable fun p : ContinuousPath ℂ × ℝ => g (p.1 p.2.toNNReal) :=
    (measurable_eval_toNNReal_uncurry hg).comp measurable_swap
  exact h.lintegral_prod_right'

/-- The window occupation integral of the shifted path is jointly measurable in the shift and the
path. -/
theorem measurable_windowOccupation_shift_uncurry {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun p : ℝ × ContinuousPath ℂ =>
      windowOccupation g (ContinuousPath.shift p.1.toNNReal p.2) := by
  have h : Measurable fun q : (ℝ × ContinuousPath ℂ) × ℝ =>
      g (q.1.2 (q.1.1.toNNReal + q.2.toNNReal)) :=
    hg.comp (measurable_path_eval_uncurry.comp
      ((((measurable_real_toNNReal.comp (measurable_fst.comp measurable_fst)).add
        (measurable_real_toNNReal.comp measurable_snd))).prodMk
          (measurable_snd.comp measurable_fst)))
  exact h.lintegral_prod_right'

/-- The expected window occupation integral is the time integral of the expected values. -/
theorem lintegral_windowOccupation_eq {g : ℂ → ℝ≥0∞} (hg : Measurable g)
    (μ : Measure (ContinuousPath ℂ)) [SFinite μ] :
    ∫⁻ b, windowOccupation g b ∂μ = ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ b, g (b s.toNNReal) ∂μ := by
  unfold windowOccupation
  exact lintegral_lintegral_swap (f := fun (b : ContinuousPath ℂ) (s : ℝ) => g (b s.toNNReal))
    (((measurable_eval_toNNReal_uncurry hg).comp measurable_swap).aemeasurable)

/-- **Pathwise symmetrization**: the square of a window integral is at most twice the integral
over ordered pairs of times. -/
theorem sq_setLIntegral_Ioc_le {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    (∫⁻ s in Ioc (0 : ℝ) 1, φ s) ^ 2 ≤
      2 * ∫⁻ s in Ioc (0 : ℝ) 1, φ s * ∫⁻ t in Ioc (0 : ℝ) 1, (Ici s).indicator φ t := by
  set Q1 : ℝ × ℝ → ℝ≥0∞ := {p : ℝ × ℝ | p.2 ≤ p.1}.indicator fun p => φ p.1 * φ p.2 with hQ1
  set Q2 : ℝ × ℝ → ℝ≥0∞ := {p : ℝ × ℝ | p.1 ≤ p.2}.indicator fun p => φ p.1 * φ p.2 with hQ2
  have hΦ : Measurable fun p : ℝ × ℝ => φ p.1 * φ p.2 :=
    (hφ.comp measurable_fst).mul (hφ.comp measurable_snd)
  have hS1 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} := measurableSet_le measurable_snd measurable_fst
  have hS2 : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} := measurableSet_le measurable_fst measurable_snd
  have hQ1m : Measurable Q1 := hΦ.indicator hS1
  have hQ2m : Measurable Q2 := hΦ.indicator hS2
  have hsq : (∫⁻ s in Ioc (0 : ℝ) 1, φ s) ^ 2 =
      ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ t in Ioc (0 : ℝ) 1, φ s * φ t := by
    rw [sq, ← lintegral_mul_const _ hφ]
    refine lintegral_congr fun s => ?_
    rw [lintegral_const_mul _ hφ]
  have hpt : ∀ s t : ℝ, φ s * φ t ≤ Q1 (s, t) + Q2 (s, t) := by
    intro s t
    rcases le_total t s with h | h
    · have : Q1 (s, t) = φ s * φ t := by
        rw [hQ1, Set.indicator_of_mem (show (s, t) ∈ {p : ℝ × ℝ | p.2 ≤ p.1} from h)]
      rw [this]
      exact le_self_add
    · have : Q2 (s, t) = φ s * φ t := by
        rw [hQ2, Set.indicator_of_mem (show (s, t) ∈ {p : ℝ × ℝ | p.1 ≤ p.2} from h)]
      rw [this]
      exact le_add_self
  have hswap : ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ t in Ioc (0 : ℝ) 1, Q1 (s, t) =
      ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ t in Ioc (0 : ℝ) 1, Q2 (s, t) := by
    rw [lintegral_lintegral_swap (f := fun s t => Q1 (s, t)) hQ1m.aemeasurable]
    refine lintegral_congr fun t => lintegral_congr fun s => ?_
    by_cases h : t ≤ s
    · rw [hQ1, hQ2, Set.indicator_of_mem (show (s, t) ∈ {p : ℝ × ℝ | p.2 ≤ p.1} from h),
        Set.indicator_of_mem (show (t, s) ∈ {p : ℝ × ℝ | p.1 ≤ p.2} from h), mul_comm]
    · rw [hQ1, hQ2, Set.indicator_of_notMem (show (s, t) ∉ {p : ℝ × ℝ | p.2 ≤ p.1} from h),
        Set.indicator_of_notMem (show (t, s) ∉ {p : ℝ × ℝ | p.1 ≤ p.2} from h)]
  have hQ2eq : ∀ s : ℝ, ∫⁻ t in Ioc (0 : ℝ) 1, Q2 (s, t) =
      φ s * ∫⁻ t in Ioc (0 : ℝ) 1, (Ici s).indicator φ t := by
    intro s
    rw [← lintegral_const_mul _ (hφ.indicator measurableSet_Ici)]
    refine lintegral_congr fun t => ?_
    by_cases h : s ≤ t
    · rw [hQ2, Set.indicator_of_mem (show (s, t) ∈ {p : ℝ × ℝ | p.1 ≤ p.2} from h),
        Set.indicator_of_mem (show t ∈ Ici s from h)]
    · rw [hQ2, Set.indicator_of_notMem (show (s, t) ∉ {p : ℝ × ℝ | p.1 ≤ p.2} from h),
        Set.indicator_of_notMem (show t ∉ Ici s from h), mul_zero]
  calc (∫⁻ s in Ioc (0 : ℝ) 1, φ s) ^ 2
      = ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ t in Ioc (0 : ℝ) 1, φ s * φ t := hsq
    _ ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ t in Ioc (0 : ℝ) 1, (Q1 (s, t) + Q2 (s, t)) :=
        lintegral_mono fun s => lintegral_mono fun t => hpt s t
    _ = ∫⁻ s in Ioc (0 : ℝ) 1, ((∫⁻ t in Ioc (0 : ℝ) 1, Q1 (s, t)) +
          ∫⁻ t in Ioc (0 : ℝ) 1, Q2 (s, t)) :=
        lintegral_congr fun s => lintegral_add_left (hQ1m.comp measurable_prodMk_left) _
    _ = (∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ t in Ioc (0 : ℝ) 1, Q1 (s, t)) +
          ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ t in Ioc (0 : ℝ) 1, Q2 (s, t) :=
        lintegral_add_left hQ1m.lintegral_prod_right' _
    _ = 2 * ∫⁻ s in Ioc (0 : ℝ) 1, φ s * ∫⁻ t in Ioc (0 : ℝ) 1, (Ici s).indicator φ t := by
        rw [hswap, ← two_mul]
        congr 1
        exact lintegral_congr hQ2eq

/-- **The future window is a shifted window**: for `s ≥ 0`,
`∫_{(0,1]} 1_{[s, ∞)} φ ≤ ∫_{(0,1]} φ(s + r) dr`. -/
theorem setLIntegral_Ioc_indicator_Ici_le (φ : ℝ → ℝ≥0∞) {s : ℝ} (hs : 0 ≤ s) :
    ∫⁻ t in Ioc (0 : ℝ) 1, (Ici s).indicator φ t ≤ ∫⁻ r in Ioc (0 : ℝ) 1, φ (s + r) := by
  calc ∫⁻ t in Ioc (0 : ℝ) 1, (Ici s).indicator φ t
      = ∫⁻ t, (Ioc (0 : ℝ) 1).indicator ((Ici s).indicator φ) t :=
        (lintegral_indicator measurableSet_Ioc _).symm
    _ = ∫⁻ r, (Ioc (0 : ℝ) 1).indicator ((Ici s).indicator φ) (s + r) :=
        (lintegral_add_left_eq_self
          (fun t => (Ioc (0 : ℝ) 1).indicator ((Ici s).indicator φ) t) s).symm
    _ ≤ ∫⁻ r, (Icc (0 : ℝ) 1).indicator (fun r => φ (s + r)) r := by
        refine lintegral_mono fun r => ?_
        by_cases h : s + r ∈ Ioc (0 : ℝ) 1 ∧ s + r ∈ Ici s
        · have hr : r ∈ Icc (0 : ℝ) 1 := ⟨by simpa using h.2, by linarith [h.1.2]⟩
          rw [Set.indicator_of_mem h.1, Set.indicator_of_mem h.2, Set.indicator_of_mem hr]
        · have h0 : (Ioc (0 : ℝ) 1).indicator ((Ici s).indicator φ) (s + r) = 0 := by
            by_cases h1 : s + r ∈ Ioc (0 : ℝ) 1
            · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem (fun h2 => h ⟨h1, h2⟩)]
            · rw [Set.indicator_of_notMem h1]
          rw [h0]
          exact zero_le
    _ = ∫⁻ r in Icc (0 : ℝ) 1, φ (s + r) := lintegral_indicator measurableSet_Icc _
    _ = ∫⁻ r in Ioc (0 : ℝ) 1, φ (s + r) := (setLIntegral_congr Ioc_ae_eq_Icc).symm

/-- **Second moment of the window occupation integral of reflected Brownian motion**
(Khas'minskii-type bound). If `E_y[I] ≤ U` for every start `y` in the unit square, then
`E_x[I²] ≤ 2 U E_x[I]` for every start `x`. -/
theorem lintegral_windowOccupation_sq_le {g : ℂ → ℝ≥0∞} (hg : Measurable g) {U : ℝ≥0∞}
    (hU : ∀ y ∈ closedSquare 0 1,
      ∫⁻ b, windowOccupation g b ∂(reflectedPlanarBrownianMotion 0 1 y) ≤ U) (x : ℂ) :
    ∫⁻ b, windowOccupation g b ^ 2 ∂(reflectedPlanarBrownianMotion 0 1 x) ≤
      2 * (U * ∫⁻ b, windowOccupation g b ∂(reflectedPlanarBrownianMotion 0 1 x)) := by
  have hev := measurable_eval_toNNReal_uncurry hg
  have hW := measurable_windowOccupation_shift_uncurry hg
  have hevb : ∀ b : ContinuousPath ℂ, Measurable fun t : ℝ => g (b t.toNNReal) := fun b =>
    hg.comp (b.continuous.comp continuous_real_toNNReal).measurable
  have hJ : ∀ w : ℂ, ∫⁻ b, windowOccupation g b ∂(reflectedPlanarBrownianMotion 0 1 w) ≤ U := by
    intro w
    rw [← reflectedPlanarBrownianMotion_zero_one_squareFold w]
    exact hU _ (squareFold_zero_one_mem w)
  calc ∫⁻ b, windowOccupation g b ^ 2 ∂(reflectedPlanarBrownianMotion 0 1 x)
      ≤ ∫⁻ b, (2 * ∫⁻ s in Ioc (0 : ℝ) 1, g (b s.toNNReal) *
          windowOccupation g (ContinuousPath.shift s.toNNReal b))
            ∂(reflectedPlanarBrownianMotion 0 1 x) := by
        refine lintegral_mono fun b => ?_
        refine (sq_setLIntegral_Ioc_le (hevb b)).trans ?_
        refine mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Ioc fun s hs => ?_)
        refine mul_le_mul' le_rfl ?_
        refine (setLIntegral_Ioc_indicator_Ici_le _ hs.1.le).trans (le_of_eq ?_)
        unfold windowOccupation
        refine setLIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
        simp only [ContinuousPath.shift_apply]
        rw [Real.toNNReal_add hs.1.le hr.1.le]
    _ = 2 * ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ b, g (b s.toNNReal) *
          windowOccupation g (ContinuousPath.shift s.toNNReal b)
            ∂(reflectedPlanarBrownianMotion 0 1 x) := by
        rw [lintegral_const_mul' _ _ (by simp)]
        congr 1
        exact lintegral_lintegral_swap (f := fun (b : ContinuousPath ℂ) (s : ℝ) =>
          g (b s.toNNReal) * windowOccupation g (ContinuousPath.shift s.toNNReal b))
          ((((hev.mul hW).comp measurable_swap)).aemeasurable)
    _ = 2 * ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ w, g (squareFold 0 1 w) *
          ∫⁻ b, windowOccupation g b ∂(reflectedPlanarBrownianMotion 0 1 w)
            ∂(planarGaussian x s.toNNReal) := by
        congr 1
        exact setLIntegral_congr_fun measurableSet_Ioc fun s _ =>
          lintegral_reflected_eval_mul_shift hg (measurable_windowOccupation hg) s.toNNReal x
    _ ≤ 2 * ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ w, g (squareFold 0 1 w) * U
          ∂(planarGaussian x s.toNNReal) :=
        mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Ioc fun s _ =>
          lintegral_mono fun w => mul_le_mul' le_rfl (hJ w))
    _ = 2 * (U * ∫⁻ b, windowOccupation g b ∂(reflectedPlanarBrownianMotion 0 1 x)) := by
        have hm : Measurable fun s : ℝ =>
            ∫⁻ b, g (b s.toNNReal) ∂(reflectedPlanarBrownianMotion 0 1 x) :=
          hev.lintegral_prod_right'
        have h1 : ∀ s : ℝ, ∫⁻ w, g (squareFold 0 1 w) * U ∂(planarGaussian x s.toNNReal) =
            (∫⁻ b, g (b s.toNNReal) ∂(reflectedPlanarBrownianMotion 0 1 x)) * U := fun s => by
          rw [lintegral_mul_const _ (show Measurable fun w => g (squareFold 0 1 w) from
              hg.comp (continuous_squareFold 0 1).measurable),
            lintegral_reflected_eval_eq s.toNNReal hg x]
        rw [lintegral_windowOccupation_eq hg]
        simp_rw [h1]
        rw [lintegral_mul_const _ hm, mul_comm U]

end HarmonicBalls
