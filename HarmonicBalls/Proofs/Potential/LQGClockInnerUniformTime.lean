import HarmonicBalls.Proofs.Potential.LQGClockInnerUniformization

/-! # Uniform-time inner occupation

Nonnegative inner occupations are controlled by their unit-time spatial mass.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

private theorem continuous_integrable_unit_path_occupation (b : ContinuousPath ℂ)
    (f : ℂ → ℝ) (hf : Continuous f) :
    Integrable f (Measure.map (fun t => b t)
      (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) := by
  have ht : Integrable (fun s : ℝ => f (b s.toNNReal))
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (hf.comp (b.continuous.comp continuous_real_toNNReal)).integrableOn_Icc
  have hν : Integrable (fun t : ℝ≥0 => f (b t))
      (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))) :=
    (integrable_map_measure (hf.comp b.continuous).aestronglyMeasurable
      continuous_real_toNNReal.measurable.aemeasurable).2 ht
  exact (integrable_map_measure hf.aestronglyMeasurable b.continuous.measurable.aemeasurable).2 hν

/-- A nonnegative inner time integral is bounded by the corresponding unit-time
closed-cutoff spatial occupation. -/
theorem lintegral_inner_time_le_closed_unit_occupation
    (b : ContinuousPath ℂ) (f : ℂ → ℝ) (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z)
    (δ t : ℝ) (ht : t ≤ 1) :
    (∫⁻ s in Ioc (0 : ℝ) t, ENNReal.ofReal
      ({z : ℂ | ‖z‖ < δ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal))) ≤
    ENNReal.ofReal (∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator f z
      ∂(Measure.map (fun u => b u) (Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))))) := by
  let E : Set ℂ := {z | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}
  let I : Set ℂ := {z | ‖z‖ < δ ∧ ‖z‖ ≤ 1/2}
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let μ : Measure ℂ := Measure.map (fun u => b u) ν
  have hE : MeasurableSet E :=
    (measurableSet_le measurable_norm measurable_const).inter
      (measurableSet_le measurable_norm measurable_const)
  have hi : Integrable (E.indicator f) μ :=
    (continuous_integrable_unit_path_occupation b f hf).indicator hE
  have hmeas : Measurable (fun z => ENNReal.ofReal (E.indicator f z)) :=
    (hf.measurable.indicator hE).ennreal_ofReal
  have heq : (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (E.indicator f (b s.toNNReal))) =
      ENNReal.ofReal (∫ z, E.indicator f z ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi]
    · rw [show μ = Measure.map (fun u => b u) ν from rfl,
        lintegral_map hmeas b.continuous.measurable]
      dsimp [ν]
      rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
      symm
      exact lintegral_map (hmeas.comp b.continuous.measurable) continuous_real_toNNReal.measurable
    · filter_upwards with z
      change (0 : ℝ) ≤ E.indicator f z
      by_cases hz : z ∈ E
      · rw [Set.indicator_of_mem hz]
        exact hf0 z
      · simp [hz]
  calc
    _ ≤ ∫⁻ s in Ioc (0 : ℝ) t, ENNReal.ofReal (E.indicator f (b s.toNNReal)) := by
      apply lintegral_mono
      intro s
      apply ENNReal.ofReal_le_ofReal
      apply Set.indicator_le_indicator_of_subset _ hf0
      intro z hz
      exact ⟨hz.1.le, hz.2⟩
    _ ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal (E.indicator f (b s.toNNReal)) :=
      lintegral_mono_set (Ioc_subset_Ioc le_rfl ht)
    _ = _ := heq

/-- The actual inner occupations vanish uniformly over all dyadic smoothing
scales and times in the unit interval, almost surely under the product law. -/
theorem ae_prod_tendsto_iSup_time_inner_inserted_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) :
    ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      Tendsto (fun n : ℕ => ⨆ i : ℕ, ⨆ t : Icc (0 : ℝ) 1,
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (i+1)
        ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator
            (fun z => ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal)))
        atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  filter_upwards [ae_prod_tendsto_iSup_inserted_closedBall_occupation_zero hh x hq0 hq2 hγ hsub,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hcont,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae
      (ae_recentered_inserted_circle_average hh α)] with q hsmall hc hr
  let d : ℕ → ℝ := fun i => (2 : ℝ)⁻¹ ^ (i+1)
  have hd (i : ℕ) : 0 < d i := by dsimp [d]; positivity
  let F : ℕ → ℂ → ℝ := fun i z => (d i)^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (d i) z)
  have hF (i : ℕ) : Continuous (F i) := by
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (d i) z) =
        fun z => hcirc q.1 (d i) z - hcirc q.1 1 0 - α * Real.log (max (d i) ‖z‖) := by
      funext z
      exact (hr (d i) z (hd i)).symm
    have hcircins : Continuous
        (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (d i) z) := by
      rw [heq]
      exact ((hc _ (hd i)).sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left (hd i)).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hcircins))
  have hF0 (i : ℕ) (z : ℂ) : 0 ≤ F i z :=
    mul_nonneg (Real.rpow_nonneg (hd i).le _) (Real.exp_pos _).le
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsmall
  · intro n
    exact zero_le
  · intro n
    apply iSup_le
    intro i
    apply iSup_le
    intro t
    refine (lintegral_inner_time_le_closed_unit_occupation q.2 (F i) (hF i) (hF0 i)
      ((2 : ℝ)⁻¹ ^ (n+2)) t.1 t.2.2).trans ?_
    change ENNReal.ofReal (∫ z, {z : ℂ | ‖z‖ ≤ (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator (F i) z
      ∂(Measure.map (fun u => q.2 u) (Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))))) ≤
      ⨆ j : ℕ, ENNReal.ofReal (∫ z, {z : ℂ | ‖z‖ ≤ (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator (F j) z
        ∂(Measure.map (fun u => q.2 u) (Measure.map Real.toNNReal
          (volume.restrict (Icc (0 : ℝ) 1)))))
    exact le_iSup (fun j : ℕ => ENNReal.ofReal
      (∫ z, {z : ℂ | ‖z‖ ≤ (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator (F j) z
        ∂(Measure.map (fun u => q.2 u) (Measure.map Real.toNNReal
          (volume.restrict (Icc (0 : ℝ) 1)))))) i

/-- The uniform-time, uniform-dyadic-scale inner occupations vanish for almost
every field and then almost every Brownian path. -/
theorem ae_field_ae_tendsto_iSup_time_inner_inserted_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x,
      Tendsto (fun n : ℕ => ⨆ i : ℕ, ⨆ t : Icc (0 : ℝ) 1,
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (i+1)
        ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < (2 : ℝ)⁻¹ ^ (n+2) ∧ ‖z‖ ≤ 1/2}.indicator
            (fun z => ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) (b s.toNNReal)))
        atTop (𝓝 0) :=
  Measure.ae_ae_of_ae_prod
    (ae_prod_tendsto_iSup_time_inner_inserted_zero hh x hq0 hq2 hγ hsub)


end HarmonicBalls
