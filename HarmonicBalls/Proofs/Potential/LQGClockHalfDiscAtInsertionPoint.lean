import HarmonicBalls.Proofs.Potential.LQGClockInsertionPointInner
import HarmonicBalls.Proofs.Potential.ClockConvergenceInProbability
import HarmonicBalls.Proofs.Potential.LQGClockHalfDiscAwayFromInsertion

/-! # Half-disc clocks for Brownian motion started at the insertion point

For Brownian motion started at the insertion point of the field `h - α log |·|`, with
`α < Q` and `γ ^ 2 < 2`, the dyadic half-disc clocks converge in probability, uniformly on
every finite time interval, for almost every field. The annular clocks converge almost
surely; the inner occupation near the origin has expectation at most a constant times a
positive power of the inner radius, uniformly in the scale, by the occupation density of
Brownian motion from the origin and the power-law bound on the masses of the inserted
approximations near the insertion.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology Metric
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The difference of two primitives of ordered locally integrable functions is monotone. -/
theorem monotone_primitive_sub {g₁ g₂ : ℝ → ℝ}
    (h₁ : ∀ a b, IntervalIntegrable g₁ volume a b) (h₂ : ∀ a b, IntervalIntegrable g₂ volume a b)
    (hle : ∀ s, g₂ s ≤ g₁ s) :
    Monotone (fun t : ℝ≥0 => (∫ s in (0 : ℝ)..(t : ℝ), g₁ s) - ∫ s in (0 : ℝ)..(t : ℝ), g₂ s) := by
  intro s t hst
  have hst' : (s : ℝ) ≤ t := hst
  have e₁ := intervalIntegral.integral_add_adjacent_intervals (h₁ 0 s) (h₁ s t)
  have e₂ := intervalIntegral.integral_add_adjacent_intervals (h₂ 0 s) (h₂ s t)
  have hd : 0 ≤ (∫ u in (s : ℝ)..(t : ℝ), g₁ u) - ∫ u in (s : ℝ)..(t : ℝ), g₂ u := by
    rw [← intervalIntegral.integral_sub (h₁ s t) (h₂ s t)]
    exact intervalIntegral.integral_nonneg hst' fun u _ => sub_nonneg.mpr (hle u)
  dsimp only
  linarith

/-- On a field sample where the inserted approximations have power-law ball masses near the
origin, the inner occupation of Brownian motion from the origin up to time `T` has
expectation at most a power of the inner radius, uniformly in the scale. -/
theorem lintegral_ofReal_inner_occupation_zero_le {γ : ℝ} {hε : ℝ → ℂ → ℝ} {k : ℕ}
    (hc : Continuous (fun z => (dyadicScale k) ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) z)))
    {C β r₀ θ δ : ℝ} (hC : 0 ≤ C) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθβ : 2 * θ < β)
    (hδ : 0 < δ) (hδr : δ ≤ r₀) (hδ2 : δ ≤ 1 / 2)
    (hbound : ∀ s : ℝ, 0 < s → s ≤ r₀ →
      lqgApprox γ hε (dyadicScale k) (ball 0 s) ≤ ENNReal.ofReal (C * s ^ β))
    (T : ℝ≥0) :
    (∫⁻ b, ENNReal.ofReal ((∫ s in (0 : ℝ)..(T : ℝ),
        {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (dyadicScale k) ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) z)) (b s.toNNReal)) -
      ∫ s in (0 : ℝ)..(T : ℝ), {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (dyadicScale k) ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) z)) (b s.toNNReal))
      ∂planarBrownianMotion 0) ≤
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * ((T : ℝ) ^ θ / θ)) *
        ENNReal.ofReal (C * 4 ^ θ * δ ^ (β - 2 * θ) / (1 - 2 ^ (-(β - 2 * θ)))) := by
  set f : ℂ → ℝ := fun z => (dyadicScale k) ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) z)
    with hfdef
  have hf0 : ∀ z, 0 ≤ f z := fun z =>
    mul_nonneg (Real.rpow_nonneg (dyadicScale_pos k).le _) (Real.exp_pos _).le
  set g : ℂ → ℝ := (ball (0 : ℂ) δ).indicator f with hgdef
  have hg0 : ∀ z, 0 ≤ g z := fun z => Set.indicator_nonneg (fun z _ => hf0 z) z
  have hgm : Measurable g := hc.measurable.indicator measurableSet_ball
  have hdiff : ∀ z, {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f z -
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f z = g z := by
    intro z
    by_cases h1 : ‖z‖ < δ
    · have hz : z ∈ ball (0 : ℂ) δ := by simpa [mem_ball, dist_zero_right] using h1
      rw [Set.indicator_of_mem (show z ∈ {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2} from
        ⟨norm_nonneg z, by linarith⟩), Set.indicator_of_notMem (show z ∉
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2} from fun h => absurd h.1 (not_le.mpr h1)),
        hgdef, Set.indicator_of_mem hz, sub_zero]
    · have hz : z ∉ ball (0 : ℂ) δ := by simpa [mem_ball, dist_zero_right] using h1
      rw [hgdef, Set.indicator_of_notMem hz]
      by_cases h2 : ‖z‖ ≤ 1 / 2
      · rw [Set.indicator_of_mem (show z ∈ {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2} from
          ⟨norm_nonneg z, h2⟩), Set.indicator_of_mem (show z ∈ {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
          from ⟨not_lt.mp h1, h2⟩), sub_self]
      · rw [Set.indicator_of_notMem (show z ∉ {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2} from
          fun h => h2 h.2), Set.indicator_of_notMem (show z ∉ {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
          from fun h => h2 h.2), sub_self]
  have hpath : ∀ b : ContinuousPath ℂ, ENNReal.ofReal ((∫ s in (0 : ℝ)..(T : ℝ),
      {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal)) -
      ∫ s in (0 : ℝ)..(T : ℝ), {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal)) =
      ∫⁻ s in Ioc 0 (T : ℝ), ENNReal.ofReal (g (b s.toNNReal)) := by
    intro b
    have h1 := intervalIntegrable_annular_density f hc 0 b 0 T
    have h2 := intervalIntegrable_annular_density f hc δ b 0 T
    rw [← intervalIntegral.integral_sub h1 h2]
    have hcongr : (∫ s in (0 : ℝ)..(T : ℝ), ({z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f
        (b s.toNNReal) - {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal))) =
        ∫ s in (0 : ℝ)..(T : ℝ), g (b s.toNNReal) :=
      intervalIntegral.integral_congr fun s _ => hdiff _
    have hgi : IntervalIntegrable (fun s : ℝ => g (b s.toNNReal)) volume 0 T := by
      have hfun : (fun s : ℝ => g (b s.toNNReal)) = fun s : ℝ =>
          {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal) -
            {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal) :=
        funext fun s => (hdiff _).symm
      rw [hfun]
      exact h1.sub h2
    rw [hcongr, intervalIntegral.integral_of_le T.coe_nonneg,
      ofReal_integral_eq_lintegral_ofReal ((intervalIntegrable_iff_integrableOn_Ioc_of_le
        T.coe_nonneg).mp hgi) (Eventually.of_forall fun s => hg0 _)]
  have hθ' : (0 : ℝ) ≤ T := T.coe_nonneg
  calc (∫⁻ b, ENNReal.ofReal ((∫ s in (0 : ℝ)..(T : ℝ),
        {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal)) -
      ∫ s in (0 : ℝ)..(T : ℝ), {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal))
      ∂planarBrownianMotion 0)
      = ∫⁻ b, (∫⁻ s in Ioc 0 (T : ℝ), ENNReal.ofReal (g (b s.toNNReal)))
          ∂planarBrownianMotion 0 := lintegral_congr hpath
    _ ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * ((T : ℝ) ^ θ / θ)) *
          ∫⁻ z, ENNReal.ofReal (g z) * ENNReal.ofReal ‖z‖ ^ (-(2 * θ)) :=
        lintegral_planarBrownianMotion_zero_occupation_le hθ0 hθ1 hθ'
          (fun z => ENNReal.ofReal (g z)) hgm.ennreal_ofReal
    _ = ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * ((T : ℝ) ^ θ / θ)) *
          ∫⁻ z in ball (0 : ℂ) δ, ENNReal.ofReal ‖z‖ ^ (-(2 * θ)) ∂lqgApprox γ hε (dyadicScale k) := by
        congr 1
        rw [lqgApprox, ← lintegral_indicator measurableSet_ball,
          lintegral_withDensity_eq_lintegral_mul _ hc.measurable.ennreal_ofReal
            (show Measurable ((ball (0 : ℂ) δ).indicator
              (fun z : ℂ => ENNReal.ofReal ‖z‖ ^ (-(2 * θ)))) from
              ((ENNReal.measurable_ofReal.comp measurable_norm).pow_const _).indicator
                measurableSet_ball)]
        apply lintegral_congr
        intro z
        simp only [Pi.mul_apply]
        rw [hgdef]
        by_cases hz : z ∈ ball (0 : ℂ) δ
        · simp only [Set.indicator_of_mem hz, hfdef]
        · simp only [Set.indicator_of_notMem hz, ENNReal.ofReal_zero, zero_mul, mul_zero]
    _ ≤ _ := by
        gcongr
        refine lintegral_ball_norm_rpow_neg_le_of_ball_le hC hθ0 hθβ hδ hδr hbound ?_
        rw [lqgApprox, withDensity_apply _ (measurableSet_singleton 0),
          Measure.restrict_eq_zero.mpr (measure_singleton 0), lintegral_zero_measure]

/-- **Half-disc clocks at the insertion point.** For `γ ^ 2 < 2` and `α < Q`, for almost
every field, the dyadic half-disc clocks of the inserted field along Brownian motion
started at the insertion point converge in probability, uniformly on every finite time
interval. -/
theorem exists_ae_tendsto_measure_halfDiscClock_at_origin
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ)
    (hγ2 : γ ^ 2 < 2) (hα : α < lqgQ γ) :
    ∃ F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ, ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
      Tendsto (fun j => planarBrownianMotion 0 {b | ∃ t ≤ T, η ≤
        |(∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (j+1)) z))
              (b s.toNNReal)) - F ω b t|}) atTop (𝓝 0) := by
  classical
  have : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hγlt : γ < 2 := by nlinarith
  let f : Ω → ℕ → ℂ → ℝ := fun ω j z => (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (j+1)) z)
  let δn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have hδn0 : ∀ n, 0 < δn n := fun n => by positivity
  have hδn2 : ∀ n, δn n ≤ 1 / 2 := fun n =>
    one_div_le_one_div_of_le (by norm_num) (by have := n.cast_nonneg (α := ℝ); linarith)
  have hδn_mono : ∀ n m, n ≤ m → δn m ≤ δn n := fun n m h =>
    one_div_le_one_div_of_le (by positivity)
      (by have h' : (n : ℝ) ≤ m := (by exact_mod_cast h); linarith)
  let Q : Ω → (ContinuousPath ℂ → ℝ≥0 → ℝ) → Prop := fun ω Fω => ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
    Tendsto (fun j => planarBrownianMotion 0 {b | ∃ t ≤ T, η ≤
      |(∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (f ω j)
        (b s.toNNReal)) - Fω b t|}) atTop (𝓝 0)
  -- annular limits
  have hann := fun n : ℕ => exists_measurable_locally_uniform_limit_annularClock hh 0 hγ hγ2 α
    (hδn0 n)
  choose Gn hGnm hGnr hGnlim using hann
  have hslice : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ᵐ b ∂planarBrownianMotion 0, ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
      ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
        |(∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | δn n ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (f ω j)
          (b s.toNNReal)) - Gn n ((ω, b), t)| < η :=
    ae_all_iff.mpr fun n => Measure.ae_ae_of_ae_prod (hGnlim n)
  -- the power bound near the insertion
  have hpow := ae_singular_approximant_near_origin_ball_power
    ((LPBridge.isWholePlaneGFF_iff P hC hcirc).2 hh) hγ hγlt hα (δ := 1) (r := 1/4) (ρ := 1/2)
    one_pos (by norm_num) ⟨by norm_num, by norm_num⟩ (by norm_num)
  -- continuity of the densities
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hdensity : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (f ω k) := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec k
    have hc : Continuous (hcirc ω (dyadicScale (k+1))) := by
      rw [← funext (hω (dyadicScale (k+1)))]
      exact hHc ω (dyadicScale (k+1)) (dyadicScale_pos (k+1))
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (k+1)) z) =
        fun z => hcirc ω (dyadicScale (k+1)) z - hcirc ω 1 0 -
          α * Real.log (max (dyadicScale (k+1)) ‖z‖) := by
      funext z
      exact (hrec _ z (dyadicScale_pos (k+1))).symm
    have hci : Continuous (fun z =>
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (k+1)) z) := by
      rw [heq]
      exact (hc.sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log
          (fun _ => (lt_max_of_lt_left (dyadicScale_pos (k+1))).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hci))
  have hgood : ∀ᵐ ω ∂P, ∃ Fω, Q ω Fω := by
    filter_upwards [hpow, hdensity, hslice] with ω hpω hc hsl
    obtain ⟨C, β, r₀, hC0, hβ, hr₀, hbound⟩ := hpω
    let ind : ℝ → ℕ → ℂ → ℝ := fun δ j => {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (f ω j)
    have hf0 : ∀ j z, 0 ≤ f ω j z := fun j z =>
      mul_nonneg (Real.rpow_nonneg (dyadicScale_pos _).le _) (Real.exp_pos _).le
    have hint : ∀ δ j (b : ContinuousPath ℂ) a c,
        IntervalIntegrable (fun s : ℝ => ind δ j (b s.toNNReal)) volume a c :=
      fun δ j b a c => intervalIntegrable_annular_density (f ω j) (hc j) δ b a c
    have hind_le : ∀ δ δ' j z, δ' ≤ δ → ind δ j z ≤ ind δ' j z := by
      intro δ δ' j z h
      by_cases hz : z ∈ {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
      · have hz' : z ∈ {z : ℂ | δ' ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2} := ⟨h.trans hz.1, hz.2⟩
        simp only [ind, Set.indicator_of_mem hz, Set.indicator_of_mem hz', le_refl]
      · simp only [ind, Set.indicator_of_notMem hz]
        exact Set.indicator_nonneg (fun z _ => hf0 j z) _
    have hindm : ∀ δ j, Measurable (ind δ j) := fun δ j => (hc j).measurable.indicator
      ((measurableSet_le measurable_const measurable_norm).inter
        (measurableSet_le measurable_norm measurable_const))
    let A : ℕ → ContinuousPath ℂ → ℝ≥0 → ℝ := fun j b t =>
      ∫ s in (0 : ℝ)..(t : ℝ), ind 0 j (b s.toNNReal)
    let Y : ℕ → ℕ → ContinuousPath ℂ → ℝ≥0 → ℝ := fun n j b t =>
      ∫ s in (0 : ℝ)..(t : ℝ), ind (δn n) j (b s.toNNReal)
    let Z : ℕ → ℕ → ContinuousPath ℂ → ℝ≥0 → ℝ := fun n j b t => A j b t - Y n j b t
    let G : ℕ → ContinuousPath ℂ → ℝ≥0 → ℝ := fun n b t => Gn n ((ω, b), t)
    have hAm : ∀ j t, Measurable (fun b => A j b t) := fun j t =>
      (SubMarkovKernelSemigroup.stronglyMeasurable_feynmanKacAdditiveFunctional
        (hindm 0 j) t).measurable
    have hYm : ∀ n j t, Measurable (fun b => Y n j b t) := fun n j t =>
      (SubMarkovKernelSemigroup.stronglyMeasurable_feynmanKacAdditiveFunctional
        (hindm (δn n) j) t).measurable
    -- the inner bound
    let θ : ℝ := min (1 / 2) (β / 4)
    have hθ0 : 0 < θ := lt_min (by norm_num) (by positivity)
    have hθ1 : θ ≤ 1 := (min_le_left _ _).trans (by norm_num)
    have hθβ : 2 * θ < β := by
      have := min_le_right (1 / 2 : ℝ) (β / 4)
      linarith
    have hZbound : ∀ T : ℝ≥0, ∃ ε : ℕ → ℝ≥0∞, Tendsto ε atTop (𝓝 0) ∧
        ∀ n j, ∫⁻ b, ENNReal.ofReal (Z n j b T) ∂planarBrownianMotion 0 ≤ ε n := by
      intro T
      let cT : ℝ≥0∞ := ENNReal.ofReal ((2 * Real.pi)⁻¹ * 2 ^ θ * ((T : ℝ) ^ θ / θ))
      refine ⟨fun n => if δn n ≤ r₀ then cT * ENNReal.ofReal
          (C * 4 ^ θ * δn n ^ (β - 2 * θ) / (1 - 2 ^ (-(β - 2 * θ)))) else ⊤, ?_, ?_⟩
      · have hδlim : Tendsto δn atTop (𝓝 0) := by
          have h := tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
          exact tendsto_const_nhds.div_atTop h
        have hpowlim : Tendsto (fun n => δn n ^ (β - 2 * θ)) atTop (𝓝 0) := by
          have h := (Real.continuousAt_rpow_const 0 (β - 2 * θ) (Or.inr (by linarith))).tendsto.comp
            hδlim
          rwa [Real.zero_rpow (by linarith)] at h
        have hreal : Tendsto (fun n => C * 4 ^ θ * δn n ^ (β - 2 * θ) / (1 - 2 ^ (-(β - 2 * θ))))
            atTop (𝓝 0) := by
          have h := (hpowlim.const_mul (C * 4 ^ θ)).div_const (1 - 2 ^ (-(β - 2 * θ)))
          simpa using h
        have hen : Tendsto (fun n => cT * ENNReal.ofReal
            (C * 4 ^ θ * δn n ^ (β - 2 * θ) / (1 - 2 ^ (-(β - 2 * θ))))) atTop (𝓝 0) := by
          have h := ENNReal.Tendsto.const_mul
            ((ENNReal.continuous_ofReal.tendsto 0).comp hreal) (Or.inr ENNReal.ofReal_ne_top)
            (a := cT)
          simpa using h
        refine hen.congr' ?_
        filter_upwards [hδlim.eventually (gt_mem_nhds hr₀)] with n hn
        exact (ite_eq_left_iff.mpr fun h => absurd hn.le h).symm
      · intro n j
        by_cases hn : δn n ≤ r₀
        · simp only [hn, ↓reduceIte]
          exact lintegral_ofReal_inner_occupation_zero_le (k := j + 1)
            (hε := LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) (hc j) hC0.le hθ0 hθ1 hθβ (hδn0 n) hn
            (hδn2 n) (fun s hs hsr => hbound (j+1) 0 s hs hsr (by simpa using hs.le)) T
        · simp only [hn, ↓reduceIte]
          exact le_top
    obtain ⟨Fω, hFω⟩ := exists_tendsto_measure_of_split_inner_small
      (μ := planarBrownianMotion 0) A Y Z G
      (fun n j b t => by simp only [Z]; ring)
      (fun n j b t => sub_nonneg.mpr (intervalIntegral.integral_mono_on t.coe_nonneg
        (hint _ j b 0 t) (hint 0 j b 0 t) fun s _ => hind_le _ _ j _ (hδn0 n).le))
      (fun n j b => monotone_primitive_sub (hint 0 j b) (hint (δn n) j b)
        (fun s => hind_le _ _ j _ (hδn0 n).le))
      (fun n m j b t hnm => intervalIntegral.integral_mono_on t.coe_nonneg
        (hint _ j b 0 t) (hint _ j b 0 t) fun s _ => hind_le _ _ j _ (hδn_mono n m hnm))
      (fun n m j b hnm => monotone_primitive_sub (hint (δn m) j b) (hint (δn n) j b)
        (fun s => hind_le _ _ j _ (hδn_mono n m hnm)))
      (fun n j b => (intervalIntegral.continuous_primitive (hint _ j b) 0).comp
        NNReal.continuous_coe)
      (fun n b => (hGnr n (ω, b)).1)
      hYm
      (fun n t => (hGnm n).comp ((measurable_const.prodMk measurable_id).prodMk measurable_const))
      (fun n j t => (hAm j t).sub (hYm n j t))
      (fun n => hsl n)
      hZbound
    exact ⟨Fω, hFω⟩
  have key : ∀ ω, ∃ Fω : ContinuousPath ℂ → ℝ≥0 → ℝ, (∃ G, Q ω G) → Q ω Fω := by
    intro ω
    by_cases h : ∃ G, Q ω G
    · exact ⟨h.choose, fun _ => h.choose_spec⟩
    · exact ⟨fun _ _ => 0, fun h' => absurd h' h⟩
  choose F hF using key
  exact ⟨F, by filter_upwards [hgood] with ω hω using hF ω hω⟩

end HarmonicBalls
