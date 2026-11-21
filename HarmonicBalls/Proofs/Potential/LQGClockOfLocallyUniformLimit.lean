import HarmonicBalls.Proofs.Potential.LQGClockHalfDiscMeasurableLimit
import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveMeasurableLimit

/-! # LQG clocks from almost sure locally uniform limits

Almost sure locally uniform convergence of the dyadic clock approximations to a limit with
continuous time paths and measurable time marginals makes the limit an LQG clock in the sense
of `IsLQGClock`. Under the product law of the field and the Brownian path, such convergence
yields an LQG clock for almost every field.

The whole-plane clock approximations of the inserted field split into the half-disc clocks
and the exterior clocks. Jointly measurable half-disc limits are available for nonpositive
insertions and, for positive insertions, in the parameter range of the inner occupation
estimates; a jointly measurable locally uniform exterior limit therefore gives the actual
inserted clock for almost every field.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

private theorem exists_rat_seq_tendsto (t : ℝ) :
    ∃ r : ℕ → ℚ, Tendsto (fun n => (r n : ℝ)) atTop (𝓝 t) := by
  have h (n : ℕ) : ∃ q : ℚ, t - 1/((n : ℝ)+1) < q ∧ (q : ℝ) < t + 1/((n : ℝ)+1) := by
    have : (0 : ℝ) < 1/((n : ℝ)+1) := by positivity
    exact exists_rat_btwn (by linarith)
  choose r hr using h
  refine ⟨r, ?_⟩
  have h0 : Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Tendsto (fun n : ℕ => t - 1/((n : ℝ)+1)) atTop (𝓝 t) := by
    have := (tendsto_const_nhds (x := t)).sub h0
    rwa [sub_zero] at this
  have hu : Tendsto (fun n : ℕ => t + 1/((n : ℝ)+1)) atTop (𝓝 t) := by
    have := (tendsto_const_nhds (x := t)).add h0
    rwa [add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu (fun n => (hr n).1.le)
    (fun n => (hr n).2.le)

/-- Almost sure locally uniform convergence of the dyadic clock approximations to a limit
with continuous time paths and measurable time marginals makes the limit an LQG clock. -/
theorem isLQGClock_of_ae_eventually_uniform {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    (hcont : ∀ k : ℕ, Continuous (hε (dyadicScale k)))
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hFc : ∀ b, Continuous (F b))
    (hFm : ∀ t, Measurable (fun b => F b t))
    (hlim : ∀ᵐ b ∂(planarBrownianMotion x), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
      ∀ᶠ k in atTop, ∀ t ≤ T, |lqgClockApprox γ hε (dyadicScale k) b t - F b t| < η) :
    IsLQGClock planarBrownianMotion γ hε x F := by
  intro T η hη
  let A : ℕ → ContinuousPath ℂ → ℝ≥0 → ℝ := fun k b t => lqgClockApprox γ hε (dyadicScale k) b t
  let w : ℕ → ℂ → ℝ := fun k y => dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) y)
  have hw (k : ℕ) : Continuous (w k) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hcont k)))
  have hAc (k : ℕ) (b : ContinuousPath ℂ) : Continuous (A k b) := by
    have h : Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t, w k (b s.toNNReal)) :=
      intervalIntegral.continuous_primitive (fun u v =>
        ((hw k).comp (b.continuous.comp continuous_real_toNNReal)).intervalIntegrable u v) 0
    exact h.comp NNReal.continuous_coe
  have hAm (k : ℕ) (t : ℝ≥0) : Measurable (fun b => A k b t) :=
    (SubMarkovKernelSemigroup.stronglyMeasurable_feynmanKacAdditiveFunctional
      (hw k).measurable t).measurable
  let τ : ℚ → ℝ≥0 := fun r => min (Real.toNNReal r) T
  let g : ℕ → ContinuousPath ℂ → ℝ≥0∞ := fun k b =>
    ⨆ r : ℚ, ENNReal.ofReal |A k b (τ r) - F b (τ r)|
  have hgm (k : ℕ) : Measurable (g k) :=
    Measurable.iSup (fun r => (((hAm k (τ r)).sub (hFm (τ r))).abs).ennreal_ofReal)
  let S : ℕ → Set (ContinuousPath ℂ) := fun k => {b | ENNReal.ofReal η ≤ g k b}
  have hSm (k : ℕ) : MeasurableSet (S k) := measurableSet_le measurable_const (hgm k)
  have hsub (k : ℕ) :
      {b | ∃ t ≤ T, η ≤ |lqgClockApprox γ hε (dyadicScale k) b t - F b t|} ⊆ S k := by
    rintro b ⟨t, ht, hle⟩
    obtain ⟨r, hr⟩ := exists_rat_seq_tendsto (t : ℝ)
    have hτ : Tendsto (fun n => τ (r n)) atTop (𝓝 t) := by
      have h1 : Tendsto (fun n => Real.toNNReal (r n)) atTop (𝓝 (Real.toNNReal t)) :=
        (continuous_real_toNNReal.tendsto _).comp hr
      have h2 := h1.min (tendsto_const_nhds (x := T))
      rwa [Real.toNNReal_coe, min_eq_left ht] at h2
    have hcf : Continuous (fun s => ENNReal.ofReal |A k b s - F b s|) :=
      ENNReal.continuous_ofReal.comp (((hAc k b).sub (hFc b)).abs)
    have hlimit := (hcf.tendsto t).comp hτ
    have hle' : ENNReal.ofReal |A k b t - F b t| ≤ g k b :=
      le_of_tendsto' hlimit (fun n =>
        le_iSup (fun r : ℚ => ENNReal.ofReal |A k b (τ r) - F b (τ r)|) (r n))
    exact (ENNReal.ofReal_le_ofReal hle).trans hle'
  have hS : Tendsto (fun k => planarBrownianMotion x (S k)) atTop (𝓝 0) := by
    have h := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (μ := planarBrownianMotion x)
      atTop MeasurableSet.empty hSm ?_
    · simpa using h
    filter_upwards [hlim] with b hb
    filter_upwards [hb T (η/2) (half_pos hη)] with k hk
    simp only [mem_empty_iff_false, iff_false]
    intro hkS
    have hg : g k b ≤ ENNReal.ofReal (η/2) := by
      apply iSup_le
      intro r
      apply ENNReal.ofReal_le_ofReal
      exact (hk (τ r) (min_le_right _ _)).le
    have hc := hkS.trans hg
    rw [ENNReal.ofReal_le_ofReal_iff (by linarith)] at hc
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hS (fun _ => zero_le)
    (fun k => measure_mono (hsub k))

/-- Almost sure locally uniform convergence under the product law of the field and the
Brownian path, to a jointly measurable limit with continuous time paths, gives an LQG clock
for almost every field. -/
theorem ae_isLQGClock_of_ae_prod_eventually_uniform {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} {hε : Ω → ℝ → ℂ → ℝ} {x : ℂ}
    (hcont : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (hε ω (dyadicScale k)))
    (F : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ) (hFm : Measurable F)
    (hFc : ∀ p, Continuous (fun t => F (p, t)))
    (hlim : ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
      ∀ᶠ k in atTop, ∀ t ≤ T, |lqgClockApprox γ (hε p.1) (dyadicScale k) p.2 t - F (p, t)| < η) :
    ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ (hε ω) x (fun b t => F ((ω, b), t)) := by
  filter_upwards [hcont, Measure.ae_ae_of_ae_prod hlim] with ω hω hl
  exact isLQGClock_of_ae_eventually_uniform hω (fun b => hFc (ω, b))
    (fun t => hFm.comp ((measurable_const.prodMk measurable_id).prodMk measurable_const)) hl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- For almost every field, the inserted circle averages are continuous at every positive
radius. -/
theorem ae_continuous_fieldCircleAverage (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (α : ℝ) :
    ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r →
      Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hr r hr0
  have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) =
      fun z => hcirc ω r z - hcirc ω 1 0 - α * Real.log (max r ‖z‖) := by
    funext z
    exact (hr r z hr0).symm
  have hc : Continuous (hcirc ω r) := by
    rw [← funext (hω r)]
    exact hHc ω r hr0
  rw [heq]
  exact (hc.sub continuous_const).sub (continuous_const.mul
    ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hr0).ne')))

/-- Locally uniform limits of the half-disc and exterior clocks of the inserted field give
an LQG clock of the inserted field for almost every field. -/
theorem ae_isLQGClock_fieldCircleAverage_of_halfDisc_exterior
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (F G : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ) (hFm : Measurable F) (hGm : Measurable G)
    (hFc : ∀ p, Continuous (fun t => F (p, t))) (hGc : ∀ p, Continuous (fun t => G (p, t)))
    (hF : ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
      ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
        |(∫ s in (0 : ℝ)..(t : ℝ),
          {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                (p.2 s.toNNReal)) - F (p,t)| < η)
    (hG : ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
      ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
        |(∫ s in (0 : ℝ)..(t : ℝ),
          {z : ℂ | 1/2 < ‖z‖}.indicator (fun z =>
            (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                (p.2 s.toNNReal)) - G (p,t)| < η) :
    ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) x
      (fun b t => F ((ω, b), t) + G ((ω, b), t)) := by
  have hcont := ae_continuous_fieldCircleAverage hh α
  have hcontk : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (fun z =>
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) := by
    filter_upwards [hcont] with ω hω k
    exact hω _ (dyadicScale_pos k)
  let B : Set ℂ := {z | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  let E : Set ℂ := {z | 1/2 < ‖z‖}
  have hB : MeasurableSet B := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  have hE : MeasurableSet E := measurableSet_lt measurable_const measurable_norm
  have hsplit (f : ℂ → ℝ) (hf : Continuous f) (b : ContinuousPath ℂ) (t : ℝ≥0) :
      (∫ s in (0 : ℝ)..(t : ℝ), f (b s.toNNReal)) =
        (∫ s in (0 : ℝ)..(t : ℝ), B.indicator f (b s.toNNReal)) +
          ∫ s in (0 : ℝ)..(t : ℝ), E.indicator f (b s.toNNReal) := by
    have hpath : Continuous (fun s : ℝ => b s.toNNReal) :=
      b.continuous.comp continuous_real_toNNReal
    have hfi : IntervalIntegrable (fun s : ℝ => f (b s.toNNReal)) volume 0 t :=
      (hf.comp hpath).intervalIntegrable _ _
    have hBi : IntervalIntegrable (fun s : ℝ => B.indicator f (b s.toNNReal)) volume 0 t := by
      refine hfi.mono_fun ((hf.measurable.indicator hB).comp hpath.measurable).aestronglyMeasurable
        (Filter.Eventually.of_forall fun s => ?_)
      by_cases hs : b s.toNNReal ∈ B
      · simp [Set.indicator_of_mem hs]
      · simp [Set.indicator_of_notMem hs]
    have hEi : IntervalIntegrable (fun s : ℝ => E.indicator f (b s.toNNReal)) volume 0 t := by
      refine hfi.mono_fun ((hf.measurable.indicator hE).comp hpath.measurable).aestronglyMeasurable
        (Filter.Eventually.of_forall fun s => ?_)
      by_cases hs : b s.toNNReal ∈ E
      · simp [Set.indicator_of_mem hs]
      · simp [Set.indicator_of_notMem hs]
    rw [← intervalIntegral.integral_add hBi hEi]
    congr 1
    funext s
    by_cases h : ‖b s.toNNReal‖ ≤ 1/2
    · have hb : b s.toNNReal ∈ B := ⟨norm_nonneg _, h⟩
      have he : b s.toNNReal ∉ E := fun he => (not_lt.mpr h) he
      rw [Set.indicator_of_mem hb, Set.indicator_of_notMem he, add_zero]
    · have hb : b s.toNNReal ∉ B := fun hb => h hb.2
      have he : b s.toNNReal ∈ E := lt_of_not_ge h
      rw [Set.indicator_of_notMem hb, Set.indicator_of_mem he, zero_add]
  apply ae_isLQGClock_of_ae_prod_eventually_uniform hcontk (fun q => F q + G q)
    (hFm.add hGm) (fun p => (hFc p).add (hGc p))
  filter_upwards [hF, hG, (Measure.quasiMeasurePreserving_fst (μ := P)
    (ν := planarBrownianMotion x)).ae hcontk] with p hpF hpG hpc T η hη
  have hev := ((hpF T (η/2) (half_pos hη)).and (hpG T (η/2) (half_pos hη)))
  rw [eventually_atTop] at hev ⊢
  obtain ⟨N, hN⟩ := hev
  refine ⟨N + 1, fun k hk t ht => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨h1, h2⟩ := hN j (by omega)
  have hf : Continuous (fun z => (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hpc (j+1))))
  have heq := hsplit _ hf p.2 t
  have hA : lqgClockApprox γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1))
      (dyadicScale (j+1)) p.2 t =
      ∫ s in (0 : ℝ)..(t : ℝ), (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) (p.2 s.toNNReal)) :=
    rfl
  rw [hA, heq]
  have hb1 := h1 t ht
  have hb2 := h2 t ht
  calc
    _ = |((∫ s in (0 : ℝ)..(t : ℝ), B.indicator (fun z =>
            (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                (p.2 s.toNNReal)) - F (p,t)) +
          ((∫ s in (0 : ℝ)..(t : ℝ), E.indicator (fun z =>
            (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                (p.2 s.toNNReal)) - G (p,t))| := by
      congr 1
      ring
    _ ≤ _ := abs_add_le _ _
    _ < η/2 + η/2 := add_lt_add hb1 hb2
    _ = η := by ring

/-- For a nonpositive insertion and `γ ^ 2 < 2`, a jointly measurable locally uniform limit
of the exterior clocks gives an LQG clock of the inserted field for almost every field. -/
theorem exists_ae_isLQGClock_fieldCircleAverage_of_exterior_of_nonpos
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (hα : α ≤ 0)
    (hext : ∃ G : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable G ∧
      (∀ p, Continuous (fun t => G (p, t))) ∧
      ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
        ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ),
            {z : ℂ | 1/2 < ‖z‖}.indicator (fun z =>
              (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                  (p.2 s.toNNReal)) - G (p,t)| < η) :
    ∃ F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ, ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) x (F ω) := by
  obtain ⟨F, hFm, hFr, hF⟩ :=
    exists_measurable_locally_uniform_limit_nonpositive_halfDiscClock hh x hγ hγ2 hα
  obtain ⟨G, hGm, hGc, hG⟩ := hext
  exact ⟨_, ae_isLQGClock_fieldCircleAverage_of_halfDisc_exterior hh x F G hFm hGm
    (fun p => (hFr p).1) hGc hF hG⟩

/-- For a positive insertion in the range of the inner occupation estimates and
`γ ^ 2 < 2`, a jointly measurable locally uniform limit of the exterior clocks gives an LQG
clock of the inserted field for almost every field. -/
theorem exists_ae_isLQGClock_fieldCircleAverage_of_exterior_of_pos
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ) (hγ2 : γ^2 < 2)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α))
    (hext : ∃ G : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable G ∧
      (∀ p, Continuous (fun t => G (p, t))) ∧
      ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
        ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ),
            {z : ℂ | 1/2 < ‖z‖}.indicator (fun z =>
              (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                  (p.2 s.toNNReal)) - G (p,t)| < η) :
    ∃ F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ, ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) x (F ω) := by
  obtain ⟨F, hFm, hFr, hF⟩ :=
    exists_measurable_locally_uniform_limit_halfDiscClock hh x hq0 hq2 hγ hγ2 hsub
  obtain ⟨G, hGm, hGc, hG⟩ := hext
  exact ⟨_, ae_isLQGClock_fieldCircleAverage_of_halfDisc_exterior hh x F G hFm hGm
    (fun p => (hFr p).1) hGc hF hG⟩

end HarmonicBalls
