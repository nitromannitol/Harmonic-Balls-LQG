import HarmonicBalls.Proofs.Potential.LQGClockStoppedDomainGluing
import HarmonicBalls.Proofs.Potential.LQGClockAnnularStoppedUniformLimit

/-! # Exterior clocks on finite horizons

Assume the dyadic time-cell moment bound for the bounded exterior occupation
`{1/2 < ‖z‖ ≤ R}` at every Brownian start. Then the unit-interval convergence of the
bounded exterior clocks holds after every integer time shift, by the Markov property
of planar Brownian motion, and the unit blocks combine into locally uniform convergence
on `[0, ∞)`. Composing with the exit time of a bounded domain gives the exit-stopped
exterior clocks, and adding a locally uniform half-disc limit gives the exit-stopped
full clock on every finite horizon.

## Main results

* `ae_exists_locally_uniform_limit_bounded_exterior_clock_of_cell_moment`
* `ae_exists_locally_uniform_limit_stopped_exterior_clock_of_cell_moment`
* `ae_exists_locally_uniform_limit_stopped_domain_clock_of_halfDisc_of_cell_moment`
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology HarmonicBalls.Section6
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- A clock along a path shifted by an integer time is an increment of the clock along
the original path. -/
theorem integral_indicator_shift_eq_sub (f : ℂ → ℝ) (hf : Continuous f) {A : Set ℂ}
    (hA : MeasurableSet A) (b : ContinuousPath ℂ) (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    (∫ s in (0 : ℝ)..u, A.indicator f ((ContinuousPath.shift (k : ℝ≥0) b) s.toNNReal)) =
      (∫ s in (0 : ℝ)..((k : ℝ) + u), A.indicator f (b s.toNNReal)) -
        ∫ s in (0 : ℝ)..(k : ℝ), A.indicator f (b s.toNNReal) := by
  let g : ℝ → ℝ := fun t => A.indicator f (b t.toNNReal)
  have hi1 : IntervalIntegrable g volume 0 k := intervalIntegrable_indicator_along_path f hf hA b 0 k
  have hi2 : IntervalIntegrable g volume k ((k : ℝ) + u) :=
    intervalIntegrable_indicator_along_path f hf hA b k ((k : ℝ) + u)
  have hsum := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have heq : (∫ s in (0 : ℝ)..u, A.indicator f ((ContinuousPath.shift (k : ℝ≥0) b) s.toNNReal)) =
      ∫ t in (0 : ℝ)..u, g ((k : ℝ) + t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hu] at ht
    dsimp only [g]
    simp only [ContinuousPath.shift_apply, Real.toNNReal_add (Nat.cast_nonneg k) ht.1,
      Real.toNNReal_natCast]
  rw [heq]
  have htrans := intervalIntegral.integral_comp_add_left g (k : ℝ) (a := 0) (b := u)
  simp only [add_zero] at htrans
  rw [htrans]
  change (∫ t in (k : ℝ)..((k : ℝ) + u), g t) = _
  linarith

/-- The closed half-disc and exterior pieces of a continuous density add up to the
full occupation integral. -/
theorem integral_halfDisc_add_exterior (f : ℂ → ℝ) (hf : Continuous f) (b : ContinuousPath ℂ)
    (u : ℝ) :
    (∫ s in (0 : ℝ)..u, {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal)) +
      (∫ s in (0 : ℝ)..u, {z : ℂ | (1 : ℝ) / 2 < ‖z‖}.indicator f (b s.toNNReal)) =
    ∫ s in (0 : ℝ)..u, f (b s.toNNReal) := by
  have hI : MeasurableSet {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2} :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hE : MeasurableSet {z : ℂ | (1 : ℝ) / 2 < ‖z‖} :=
    measurableSet_lt measurable_const measurable_norm
  rw [← intervalIntegral.integral_add (intervalIntegrable_indicator_along_path f hf hI b 0 u)
    (intervalIntegrable_indicator_along_path f hf hE b 0 u)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  show {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal) +
      {z : ℂ | (1 : ℝ) / 2 < ‖z‖}.indicator f (b s.toNNReal) = f (b s.toNNReal)
  by_cases h : ‖b s.toNNReal‖ ≤ (1 : ℝ) / 2
  · rw [Set.indicator_of_mem (show b s.toNNReal ∈ {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2} from
      ⟨norm_nonneg _, h⟩), Set.indicator_of_notMem
        (show b s.toNNReal ∉ {z : ℂ | (1 : ℝ) / 2 < ‖z‖} from not_lt.mpr h), add_zero]
  · rw [Set.indicator_of_notMem (show b s.toNNReal ∉ {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2} from
      fun hz => h hz.2), Set.indicator_of_mem
        (show b s.toNNReal ∈ {z : ℂ | (1 : ℝ) / 2 < ‖z‖} from not_le.mp h), zero_add]

/-- Under the cell moment bound at every start, the unit-interval convergence of the
bounded exterior clocks holds simultaneously after every integer time shift. -/
theorem ae_exists_uniform_limit_integer_shift_bounded_exterior_clock_of_cell_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {R : ℝ} (hR : 0 < R)
    {p a C : ℝ} (hp : 0 < p) (ha : 1 < a)
    (hmom : ∀ y : ℂ, ∀ᶠ n in atTop, ∀ m j : ℕ, j < 2 ^ m →
      ∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc ((j : ℝ) / 2 ^ m) ((j + 1) / 2 ^ m),
        ENNReal.ofReal ({z : ℂ | (1 : ℝ) / 2 < ‖z‖ ∧ ‖z‖ ≤ R}.indicator (fun z =>
          dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z))
          (q.2 s.toNNReal))) ^ p ∂(P.prod (planarBrownianMotion y)) ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ m)⁻¹ ^ a)) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), ∀ k : ℕ, ∃ F : Icc (0 : ℝ) 1 → ℝ,
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ u : Icc (0 : ℝ) 1,
        |(∫ s in (0 : ℝ)..(u : ℝ), {z : ℂ | (1 : ℝ) / 2 < ‖z‖ ∧ ‖z‖ ≤ R}.indicator (fun z =>
            dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z))
          ((ContinuousPath.shift (k : ℝ≥0) q.2) s.toNNReal)) - F u| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let A : Set ℂ := {z : ℂ | (1 : ℝ) / 2 < ‖z‖ ∧ ‖z‖ ≤ R}
  have hA : MeasurableSet A := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  choose M hMm hMr hMae using fun n : ℕ =>
    exists_measurable_stopped_indicator_clock_prod_time hh (dyadicScale_pos (n + 1)) γ α hA
      (measurable_const (a := (1 : ℝ))) (fun _ => zero_le_one)
  let B (n : ℕ) (q : Ω × ContinuousPath ℂ) : C(Icc (0 : ℝ) 1, ℝ) :=
    ⟨fun t => M n (q, (t : ℝ).toNNReal),
      (hMr n q).1.comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩
  have hBm (n : ℕ) : Measurable (B n) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (hMm n).comp (measurable_id.prodMk measurable_const)
  let S : Set (Ω × ContinuousPath ℂ) := {q | ∃ F, Tendsto (fun n => B n q) atTop (𝓝 F)}
  have hSm : MeasurableSet S := measurableSet_exists_tendsto hBm
  have hS (y : ℂ) : ∀ᵐ q ∂(P.prod (planarBrownianMotion y)), q ∈ S := by
    filter_upwards [ae_tendstoUniformlyOn_bounded_exterior_clock_of_cell_moment hh hγ0 hγ2 α y
      (measurable_const (a := (1 : ℝ))) (fun _ => zero_le_one) hR hp ha (hmom y),
      (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion y)).ae
        (ae_all_iff.mpr hMae)] with q hq hM
    obtain ⟨F, hFc, -, -, hF⟩ := hq
    let G : C(Icc (0 : ℝ) 1, ℝ) :=
      ⟨fun t => F t, hFc.comp_continuous continuous_subtype_val (fun t => t.2)⟩
    refine ⟨G, ?_⟩
    apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
    rw [Metric.tendstoUniformlyOn_iff] at hF
    rw [Metric.tendstoUniformly_iff]
    intro η hη
    filter_upwards [hF η hη] with n hn t
    have h := hn t t.2
    have hMt := hM n q.2 (t : ℝ).toNNReal
    rw [Real.coe_toNNReal _ t.2.1] at hMt
    change dist (F t) (M n (q, (t : ℝ).toNNReal)) < η
    rw [show M n (q, (t : ℝ).toNNReal) = _ from hMt]
    simpa only [A, min_eq_left t.2.2] using h
  apply ae_all_iff.mpr
  intro k
  have hshift := ae_prod_planarBrownianMotion_shift_of_forall_ae P x k S hSm hS
  filter_upwards [hshift, (Measure.quasiMeasurePreserving_fst
    (μ := P) (ν := planarBrownianMotion x)).ae (ae_all_iff.mpr hMae)] with q hq hM
  obtain ⟨F, hF⟩ := hq
  refine ⟨F, ?_⟩
  have hu := ContinuousMap.tendsto_iff_tendstoUniformly.mp hF
  rw [Metric.tendstoUniformly_iff] at hu
  intro η hη
  filter_upwards [hu η hη] with n hn u
  have heq := hM n (ContinuousPath.shift (k : ℝ≥0) q.2) (u : ℝ).toNNReal
  rw [Real.coe_toNNReal _ u.2.1] at heq
  have h := hn u
  change dist (F u) (M n ((q.1, ContinuousPath.shift (k : ℝ≥0) q.2), (u : ℝ).toNNReal)) < η at h
  rw [heq, dist_comm, Real.dist_eq] at h
  simpa only [A, min_eq_left u.2.2] using h

/-- Under the cell moment bound at every start, the bounded exterior clocks converge
locally uniformly on `[0, ∞)` to a continuous, nonnegative and nondecreasing limit,
almost surely under the field-path product law. -/
theorem ae_exists_locally_uniform_limit_bounded_exterior_clock_of_cell_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {R : ℝ} (hR : 0 < R)
    {p a C : ℝ} (hp : 0 < p) (ha : 1 < a)
    (hmom : ∀ y : ℂ, ∀ᶠ n in atTop, ∀ m j : ℕ, j < 2 ^ m →
      ∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc ((j : ℝ) / 2 ^ m) ((j + 1) / 2 ^ m),
        ENNReal.ofReal ({z : ℂ | (1 : ℝ) / 2 < ‖z‖ ∧ ‖z‖ ≤ R}.indicator (fun z =>
          dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z))
          (q.2 s.toNNReal))) ^ p ∂(P.prod (planarBrownianMotion y)) ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ m)⁻¹ ^ a)) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | (1 : ℝ) / 2 < ‖z‖ ∧ ‖z‖ ≤ R}.indicator (fun z =>
            dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z))
            (q.2 s.toNNReal)) - F t| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hA : MeasurableSet {z : ℂ | (1 : ℝ) / 2 < ‖z‖ ∧ ‖z‖ ≤ R} :=
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  filter_upwards [ae_exists_uniform_limit_integer_shift_bounded_exterior_clock_of_cell_moment
    hh hγ0 hγ2 α x hR hp ha hmom, (Measure.quasiMeasurePreserving_fst (μ := P)
      (ν := planarBrownianMotion x)).ae (ae_forall_continuous_inserted_density hh γ α)]
    with q hq hc
  let f (n : ℕ) : ℂ → ℝ := fun z => dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z)
  have hfc (n : ℕ) : Continuous (f n) := hc _ (dyadicScale_pos (n + 1))
  let g (n : ℕ) (t : ℝ) : ℝ :=
    {z : ℂ | (1 : ℝ) / 2 < ‖z‖ ∧ ‖z‖ ≤ R}.indicator (f n) (q.2 t.toNNReal)
  let Acl (n : ℕ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, g n s
  have hblock : ∀ k : ℕ, ∃ F : Icc (0 : ℝ) 1 → ℝ,
      ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ u : Icc (0 : ℝ) 1,
        |(Acl n ((k : ℝ) + u) - Acl n k) - F u| < η := by
    intro k
    obtain ⟨F, hF⟩ := hq k
    refine ⟨F, fun η hη => ?_⟩
    filter_upwards [hF η hη] with n hn u
    have heq := integral_indicator_shift_eq_sub (f n) (hfc n) hA q.2 k u.2.1
    change (∫ s in (0 : ℝ)..(u : ℝ), _) = Acl n (k + u) - Acl n k at heq
    rw [← heq]
    exact hn u
  have hnat := exists_uniform_limit_on_nat_intervals_of_unit_blocks Acl
    (fun n => intervalIntegral.integral_same) hblock
  let B (n : ℕ) (t : ℝ≥0) := Acl n t
  have hBc (n : ℕ) : Continuous (B n) :=
    (intervalIntegral.continuous_primitive (fun u v =>
      intervalIntegrable_indicator_along_path (f n) (hfc n) hA q.2 u v) 0).comp
        continuous_subtype_val
  have hf0 (n : ℕ) (z : ℂ) : 0 ≤ f n z :=
    mul_nonneg (Real.rpow_nonneg (dyadicScale_pos (n + 1)).le _) (Real.exp_pos _).le
  have hg0 (n : ℕ) (t : ℝ) : 0 ≤ g n t := Set.indicator_nonneg (fun z _ => hf0 n z) _
  have hB0 (n : ℕ) (t : ℝ≥0) : 0 ≤ B n t :=
    intervalIntegral.integral_nonneg_of_forall t.coe_nonneg (hg0 n)
  have hBm (n : ℕ) : Monotone (B n) := by
    intro s t hst
    exact intervalIntegral.integral_mono_interval le_rfl s.coe_nonneg hst
      (Eventually.of_forall (hg0 n))
      (intervalIntegrable_indicator_along_path (f n) (hfc n) hA q.2 0 t)
  have hnatB (N : ℕ) : ∃ G : ℝ≥0 → ℝ, ∀ η : ℝ, 0 < η →
      ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ N → |B n t - G t| < η := by
    obtain ⟨G, hG⟩ := hnat N
    refine ⟨fun t => G t, fun η hη => ?_⟩
    filter_upwards [hG η hη] with n hn t ht
    exact hn t ⟨t.coe_nonneg, by exact_mod_cast ht⟩
  exact exists_continuous_monotone_limit_of_uniform_on_nat_intervals B hBc hB0 hBm hnatB

/-- Under the cell moment bound at every start, the exterior clocks stopped at the exit
of a domain contained in the disc of radius `R` converge locally uniformly on `[0, ∞)`
to a continuous, nonnegative and nondecreasing limit, almost surely under the field-path
product law, and the exit time is finite. -/
theorem ae_exists_locally_uniform_limit_stopped_exterior_clock_of_cell_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ)
    {D : Set ℂ} {R : ℝ} (hR : 0 < R) (hDR : ∀ z ∈ D, ‖z‖ ≤ R)
    {p a C : ℝ} (hp : 0 < p) (ha : 1 < a)
    (hmom : ∀ y : ℂ, ∀ᶠ n in atTop, ∀ m j : ℕ, j < 2 ^ m →
      ∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc ((j : ℝ) / 2 ^ m) ((j + 1) / 2 ^ m),
        ENNReal.ofReal ({z : ℂ | (1 : ℝ) / 2 < ‖z‖ ∧ ‖z‖ ≤ R}.indicator (fun z =>
          dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z))
          (q.2 s.toNNReal))) ^ p ∂(P.prod (planarBrownianMotion y)) ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ m)⁻¹ ^ a)) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
      ContinuousPath.exitTime D q.2 < ⊤ ∧
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D q.2).toReal,
            {z : ℂ | (1 : ℝ) / 2 < ‖z‖}.indicator (fun z =>
            dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z))
              (q.2 s.toNNReal)) - F t| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hDb : Bornology.IsBounded D := (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset
    fun z hz => by simpa only [Metric.mem_closedBall, dist_zero_right] using hDR z hz
  filter_upwards [ae_exists_locally_uniform_limit_bounded_exterior_clock_of_cell_moment hh hγ0 hγ2
    α x hR hp ha hmom, (Measure.quasiMeasurePreserving_snd (μ := P)
      (ν := planarBrownianMotion x)).ae (ae_planarBrownian_exitTime_bounded_lt_top x hDb)]
    with q hq hfin
  obtain ⟨F, hFc, hF0, hFm, hF⟩ := hq
  let r : ℝ≥0 → ℝ≥0 := fun t => min t (ContinuousPath.exitTime D q.2).toNNReal
  have hrc : Continuous r := continuous_id.min continuous_const
  have hrm : Monotone r := fun _ _ h => min_le_min_right _ h
  refine ⟨hfin, F ∘ r, hFc.comp hrc, (fun t => hF0 (r t)), hFm.comp hrm, ?_⟩
  intro T η hη
  filter_upwards [hF T η hη] with n hn t ht
  have hrt : r t ≤ T := (min_le_left _ _).trans ht
  have h := hn (r t) hrt
  have heq : ((r t : ℝ≥0) : ℝ) = min (t : ℝ) (ContinuousPath.exitTime D q.2).toReal := by
    simp only [r, NNReal.coe_min, ENNReal.coe_toNNReal_eq_toReal]
  rw [stopped_exterior_clock_eq_bounded _ q.2 D R hDR t]
  simpa only [Function.comp_apply, heq] using h

/-- Conditional exit-stopped clock on finite horizons. Suppose that the closed half-disc
clocks converge locally uniformly on `[0, ∞)` almost surely under the field-path product
law, and that the bounded exterior cell moment bound holds at every start. Then the full
inserted clocks stopped at the exit of a domain contained in the disc of radius `R`
converge locally uniformly on `[0, ∞)` to a continuous, nonnegative and nondecreasing
limit, and the exit time is finite, almost surely. -/
theorem ae_exists_locally_uniform_limit_stopped_domain_clock_of_halfDisc_of_cell_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ)
    {D : Set ℂ} {R : ℝ} (hR : 0 < R) (hDR : ∀ z ∈ D, ‖z‖ ≤ R)
    (hin : ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ),
            {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (j+1)) z))
                  (q.2 s.toNNReal)) - F t| < η)
    {p a C : ℝ} (hp : 0 < p) (ha : 1 < a)
    (hmom : ∀ y : ℂ, ∀ᶠ n in atTop, ∀ m j : ℕ, j < 2 ^ m →
      ∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc ((j : ℝ) / 2 ^ m) ((j + 1) / 2 ^ m),
        ENNReal.ofReal ({z : ℂ | (1 : ℝ) / 2 < ‖z‖ ∧ ‖z‖ ≤ R}.indicator (fun z =>
          dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z))
          (q.2 s.toNNReal))) ^ p ∂(P.prod (planarBrownianMotion y)) ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ m)⁻¹ ^ a)) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)),
      ContinuousPath.exitTime D q.2 < ⊤ ∧
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D q.2).toReal,
            dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1))
                (q.2 s.toNNReal))) - F t| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  filter_upwards [hin, ae_exists_locally_uniform_limit_stopped_exterior_clock_of_cell_moment hh
    hγ0 hγ2 α x hR hDR hp ha hmom, (Measure.quasiMeasurePreserving_fst (μ := P)
      (ν := planarBrownianMotion x)).ae (ae_forall_continuous_inserted_density hh γ α)]
    with q hqi hqe hc
  obtain ⟨Fi, hFic, hFi0, hFim, hFi⟩ := hqi
  obtain ⟨hfin, Fe, hFec, hFe0, hFem, hFe⟩ := hqe
  let r : ℝ≥0 → ℝ≥0 := fun t => min t (ContinuousPath.exitTime D q.2).toNNReal
  have hrc : Continuous r := continuous_id.min continuous_const
  have hrm : Monotone r := fun _ _ h => min_le_min_right _ h
  refine ⟨hfin, fun t => Fi (r t) + Fe t, (hFic.comp hrc).add hFec,
    fun t => add_nonneg (hFi0 (r t)) (hFe0 t), fun s t hst => add_le_add (hFim (hrm hst))
      (hFem hst), ?_⟩
  intro T η hη
  filter_upwards [hFi T (η / 2) (half_pos hη), hFe T (η / 2) (half_pos hη)] with n hi he t ht
  have hrt : r t ≤ T := (min_le_left _ _).trans ht
  have h1 := hi (r t) hrt
  have h2 := he t ht
  have heq : ((r t : ℝ≥0) : ℝ) = min (t : ℝ) (ContinuousPath.exitTime D q.2).toReal := by
    simp only [r, NNReal.coe_min, ENNReal.coe_toNNReal_eq_toReal]
  rw [heq] at h1
  rw [← integral_halfDisc_add_exterior _ (hc _ (dyadicScale_pos (n + 1)))]
  rw [abs_lt] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end HarmonicBalls
