import HarmonicBalls.Proofs.Potential.LQGClockAnnularUniformL1Limit

/-! # Measurable locally uniform limits

A locally uniform limit admits a jointly measurable representative on nonnegative time.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter HarmonicBalls.Section6
open scoped NNReal ENNReal Topology

namespace HarmonicBalls

/-- A sequence of jointly measurable functions that converges locally uniformly almost surely
has a jointly measurable representative of its limit with continuous, nonnegative and
nondecreasing time paths. -/
theorem exists_measurable_locally_uniform_limit
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (A : ℕ → X × ℝ≥0 → ℝ) (hA : ∀ n, Measurable (A n))
    (hconv : ∀ᵐ x ∂μ, ∃ G : ℝ≥0 → ℝ,
      Continuous G ∧ (∀ t, 0 ≤ G t) ∧ Monotone G ∧
      ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
        |A n (x, t) - G t| < ε) :
    ∃ F : X × ℝ≥0 → ℝ, Measurable F ∧
      (∀ x, Continuous (fun t => F (x, t)) ∧ (∀ t, 0 ≤ F (x, t)) ∧
        Monotone (fun t => F (x, t))) ∧
      ∀ᵐ x ∂μ, ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        ∀ t : ℝ≥0, t ≤ T → |A n (x, t) - F (x, t)| < ε := by
  classical
  let L : X × ℝ≥0 → ℝ := fun p => limUnder atTop (fun n => A n p)
  have hLm : Measurable L :=
    (StronglyMeasurable.limUnder (fun n => (hA n).stronglyMeasurable)).measurable
  let Q (x : X) : Prop :=
    Continuous (fun t => L (x, t)) ∧ (∀ t, 0 ≤ L (x, t)) ∧
    Monotone (fun t => L (x, t)) ∧
    ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
      |A n (x, t) - L (x, t)| < ε
  have hQ : ∀ᵐ x ∂μ, Q x := by
    filter_upwards [hconv] with x hx
    obtain ⟨G, hGc, hG0, hGm, hG⟩ := hx
    have hLG : (fun t => L (x, t)) = G := by
      funext t
      apply Tendsto.limUnder_eq
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      filter_upwards [hG t ε hε] with n hn
      simpa only [Real.dist_eq] using hn t le_rfl
    have heq (t : ℝ≥0) : L (x, t) = G t := congrFun hLG t
    refine ⟨hLG ▸ hGc, fun t => (heq t) ▸ hG0 t, hLG ▸ hGm, ?_⟩
    intro T ε hε
    filter_upwards [hG T ε hε] with n hn t ht
    rw [heq t]
    exact hn t ht
  let S : Set X := (toMeasurable μ {x | ¬ Q x})ᶜ
  have hS : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hSc : μ Sᶜ = 0 := by
    rw [compl_compl, measure_toMeasurable]
    exact ae_iff.mp hQ
  have hSQ (x : X) (hx : x ∈ S) : Q x :=
    by_contra fun h => hx (subset_toMeasurable _ _ h)
  let F : X × ℝ≥0 → ℝ := fun p => if p.1 ∈ S then L p else 0
  have hFm : Measurable F :=
    Measurable.ite (hS.preimage measurable_fst) hLm measurable_const
  refine ⟨F, hFm, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ S
    · obtain ⟨hc, h0, hm, _⟩ := hSQ x hx
      simpa only [F, hx, ↓reduceIte] using And.intro hc (And.intro h0 hm)
    · simp only [F, hx, ↓reduceIte]
      exact ⟨continuous_const, fun _ => le_rfl, monotone_const⟩
  · have hae : ∀ᵐ x ∂μ, x ∈ S := ae_iff.mpr hSc
    filter_upwards [hae] with x hx
    obtain ⟨_, _, _, h⟩ := hSQ x hx
    simpa only [F, hx, ↓reduceIte] using h

/-- Uniform almost-sure convergence under an integrable bound gives uniform L¹ convergence
to the prescribed measurable limit. -/
theorem integral_uniform_distance_tendsto_of_dominated {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {T : ℝ≥0}
    (A : ℕ → X → C(Icc (0 : ℝ) (T : ℝ), ℝ)) (hA : ∀ k, Measurable (A k))
    (F : X → C(Icc (0 : ℝ) (T : ℝ), ℝ))
    (G : X → ℝ) (hG : Integrable G μ)
    (hbound : ∀ᵐ x ∂μ, ∀ k, ‖A k x‖ ≤ G x)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun k => A k x) atTop (𝓝 (F x))) :
    (∀ k, Integrable (fun x => ‖A k x - F x‖) μ) ∧
      Tendsto (fun k => ∫ x, ‖A k x - F x‖ ∂μ) atTop (𝓝 0) := by
  obtain ⟨F', _, hF', hi, ht⟩ :=
    tendsto_integral_uniform_distance_of_dominated A hA G hG hbound
      (hconv.mono fun x hx => ⟨F x, hx⟩)
  have heq : ∀ᵐ x ∂μ, F x = F' x := by
    filter_upwards [hconv, hF'] with x hx hx'
    exact tendsto_nhds_unique hx hx'
  have he (k : ℕ) : (fun x => ‖A k x - F x‖) =ᵐ[μ] (fun x => ‖A k x - F' x‖) := by
    filter_upwards [heq] with x hx
    rw [hx]
  refine ⟨fun k => (hi k).congr (he k).symm, ?_⟩
  have hi_eq : (fun k => ∫ x, ‖A k x - F x‖ ∂μ) =
      (fun k => ∫ x, ‖A k x - F' x‖ ∂μ) := by
    funext k
    exact integral_congr_ae (he k)
  rw [hi_eq]
  exact ht

/-- For almost every field, the actual stopped annular clocks have one jointly measurable
Brownian-path and time limit, simultaneously on all finite horizons. -/
theorem ae_exists_measurable_locally_uniform_limit_stopped_annular_clock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) :
    ∀ᵐ ω ∂P, ∃ F : ContinuousPath ℂ × ℝ≥0 → ℝ, Measurable F ∧
      (∀ b, Continuous (fun t => F (b, t)) ∧ (∀ t, 0 ≤ F (b, t)) ∧
        Monotone (fun t => F (b, t))) ∧
      (∀ᵐ b ∂planarBrownianMotion x, ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ k in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
            {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale k)^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z))
                  (b s.toNNReal)) - F (b, t)| < ε) ∧
      ∀ T : ℝ≥0, ∃ (A : ℕ → ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ))
          (B : ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ)),
        (∀ k b t, A k b t = ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            (dyadicScale k)^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z))
              (b s.toNNReal)) ∧
        (∀ b t, B b t = F (b, (t : ℝ).toNNReal)) ∧ Measurable B ∧
        (∀ᵐ b ∂planarBrownianMotion x, Tendsto (fun k => A k b) atTop (𝓝 (B b))) ∧
        (∀ k, Integrable (fun b => ‖A k b - B b‖) (planarBrownianMotion x)) ∧
        Tendsto (fun k => ∫ b, ‖A k b - B b‖ ∂planarBrownianMotion x) atTop (𝓝 0) := by
  have hγlt : γ < 2 := by nlinarith [sq_nonneg (γ - 1)]
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  filter_upwards [hcont, ae_recentered_inserted_circle_average hh α,
    ae_field_ae_path_exists_locally_uniform_limit_annularClock_stopped hh x hγ hγ2 α hδ hDb,
    ae_exists_integrable_bound_stopped_annular_clock hh hγ hγlt α x hδ hD hDb]
      with ω hcont hrec hconv hbound
  let Z : ℕ → ℂ → ℝ := fun k z => (dyadicScale k)^(γ^2/2) *
    Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z)
  have hc (k : ℕ) : Continuous (Z k) := by
    have hr := dyadicScale_pos k
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) =
        fun z => hcirc ω (dyadicScale k) z - hcirc ω 1 0 - α * Real.log (max (dyadicScale k) ‖z‖) := by
      funext z
      exact (hrec _ z hr).symm
    have hc' : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) := by
      rw [heq]
      exact ((hcont _ hr).sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hr).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc'))
  let A : ℕ → ContinuousPath ℂ × ℝ≥0 → ℝ := fun k p =>
    ∫ s in (0 : ℝ)..min (p.2 : ℝ) (ContinuousPath.exitTime D p.1).toReal,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (Z k) (p.1 s.toNNReal)
  have hAm (k : ℕ) : Measurable (A k) := by
    apply (measurable_uncurry_of_continuous_of_measurable
      (u := fun t b => A k (b, t)) ?_ ?_).comp measurable_swap
    · intro b
      change Continuous (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (Z k) (b s.toNNReal))
      exact (intervalIntegral.continuous_primitive
        (fun a c => intervalIntegrable_annular_density (Z k) (hc k) δ b a c) 0).comp
          (continuous_subtype_val.min continuous_const)
    · intro t
      exact measurable_stopped_annular_time_integral hD (Z k) (hc k) δ t
  have hAc : ∀ᵐ b ∂planarBrownianMotion x, ∃ F : ℝ≥0 → ℝ,
      Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
      ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ t : ℝ≥0, t ≤ T →
        |A k (b, t) - F t| < ε := by
    filter_upwards [hconv] with b hb
    obtain ⟨_, F, hFc, hF0, hFm, hF⟩ := hb
    exact ⟨F, hFc, hF0, hFm, hF⟩
  obtain ⟨F, hFm, hFc, hFlim⟩ :=
    exists_measurable_locally_uniform_limit (planarBrownianMotion x) A hAm hAc
  obtain ⟨G, hG, hbound⟩ := hbound
  refine ⟨F, hFm, hFc, hFlim, ?_⟩
  intro T
  let AT : ℕ → ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ) := fun k b =>
    ⟨fun t => A k (b, (t : ℝ).toNNReal),
      (by
        have heq : (fun t : Icc (0 : ℝ) (T : ℝ) => A k (b, (t : ℝ).toNNReal)) =
            (fun t : Icc (0 : ℝ) (T : ℝ) => ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
              {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (Z k) (b s.toNNReal)) := by
          funext t
          simp only [A, Real.toNNReal_of_nonneg t.property.1, NNReal.coe_mk]
        rw [heq]
        exact (intervalIntegral.continuous_primitive
          (fun a c => intervalIntegrable_annular_density (Z k) (hc k) δ b a c) 0).comp
            (continuous_subtype_val.min continuous_const))⟩
  let B : ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ) := fun b =>
    ⟨fun t => F (b, (t : ℝ).toNNReal),
      (hFc b).1.comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩
  have hATm (k : ℕ) : Measurable (AT k) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (hAm k).comp (measurable_id.prodMk measurable_const)
  have hBm : Measurable B := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact hFm.comp (measurable_id.prodMk measurable_const)
  have hATb : ∀ᵐ b ∂planarBrownianMotion x, ∀ k, ‖AT k b‖ ≤ G b := by
    filter_upwards [hbound] with b hb k
    have hG0 : 0 ≤ G b := (abs_nonneg _).trans (hb 0 0)
    apply (ContinuousMap.norm_le (AT k b) hG0).2
    intro t
    simpa only [AT, A, ContinuousMap.coe_mk, Real.norm_eq_abs,
      Real.toNNReal_of_nonneg t.property.1, NNReal.coe_mk] using hb k ((t : ℝ).toNNReal)
  have hBT : ∀ᵐ b ∂planarBrownianMotion x, Tendsto (fun k => AT k b) atTop (𝓝 (B b)) := by
    filter_upwards [hFlim] with b hb
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hb T (ε / 2) (half_pos hε)] with k hk
    have hle : ‖AT k b - B b‖ ≤ ε / 2 := by
      apply (ContinuousMap.norm_le (AT k b - B b) (le_of_lt (half_pos hε))).2
      intro t
      have ht : (t : ℝ).toNNReal ≤ T := by
        exact NNReal.coe_le_coe.mp (by simpa [Real.toNNReal_of_nonneg t.property.1] using t.property.2)
      have hx := (hk ((t : ℝ).toNNReal) ht).le
      simpa only [AT, B, A, ContinuousMap.sub_apply, ContinuousMap.coe_mk, Real.norm_eq_abs,
        Real.toNNReal_of_nonneg t.property.1, NNReal.coe_mk] using hx
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hle (half_lt_self hε)
  obtain ⟨hi, ht⟩ := integral_uniform_distance_tendsto_of_dominated AT hATm B G hG hATb hBT
  refine ⟨AT, B, ?_, (fun _ _ => rfl), hBm, hBT, hi, ht⟩
  intro k b t
  simp only [AT, A, Z, ContinuousMap.coe_mk, Real.toNNReal_of_nonneg t.property.1, NNReal.coe_mk]

end HarmonicBalls
