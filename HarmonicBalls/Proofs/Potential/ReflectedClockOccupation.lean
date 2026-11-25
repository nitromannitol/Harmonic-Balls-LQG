import HarmonicBalls.Proofs.Potential.ReflectedTimeChangeSemigroup
import HarmonicBalls.Proofs.Potential.ReflectedRevuzIdentification
import HarmonicBalls.Proofs.Potential.ReflectedNeumannKernel

/-!
# Occupation integrals of a clock in the time of the time-changed process

For a continuous nondecreasing clock `a` from `0` that tends to `∞`, the image of Lebesgue
measure on `(0, ∞)` under the right inverse `u ↦ τ_u = inf {t | u < a t}` is the Stieltjes
measure `da` (`map_volume_clockInverse_eq_stieltjes`), so occupation integrals against `dA_s`
are integrals in the time `u` of the time-changed process:
`∫ F(s, b_s) dA_s = ∫_0^∞ F(τ_u, b_{τ_u}) du`. For a clock `A` of reflected Brownian motion in
`K₀` this gives:

* `clockOccupation A F b = ∫_0^∞ F(τ̄_u, Y_u) du`, with `τ̄` the right inverse of the rational-time
  regularization and `Y_u = b_{τ̄_u}` (a measurable functional of the path);
* the Revuz formula in this form (`lintegral_unitSquareRevuzMeasure_eq_clockOccupation`);
* the shift at a fixed time `t` (`ae_clockOccupation_indicator_Ioi_eq_shift`):
  `∫_{τ_u > t} F(τ_u, Y_u) du` is the occupation integral of `F(t + ·, ·)` along `θ_t b`;
* the stationarity of reflected Brownian motion started from Lebesgue measure on `K₀`
  (`setLIntegral_lintegral_shift_eq`, `setLIntegral_lintegral_mul_shift_eq`).

These are the steps of Revuz–Yor (1999), Chapter X, Section 2, and Fukushima–Oshima–Takeda
(2011), (5.1.11), written for the clock read in the time of the time change.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

namespace HarmonicBalls

/-! ### The right inverse of a deterministic clock -/

section Deterministic

variable {a : ℝ≥0 → ℝ≥0}

/-- `τ_u ≤ t` when `u < a t`. -/
theorem sInf_lt_clock_le {u t : ℝ≥0} (h : u < a t) : sInf {s | u < a s} ≤ t :=
  csInf_le (OrderBot.bddBelow _) h

/-- `a (τ_u) = u` for a continuous nondecreasing clock from `0` exceeding `u`. -/
theorem clock_sInf_eq (h0 : a 0 = 0) (hc : Continuous a) (hm : Monotone a) {u : ℝ≥0}
    (hne : ∃ t, u < a t) : a (sInf {s | u < a s}) = u := by
  have h := apply_pcafClockInverse_eq (A := fun t (_ : ContinuousPath ℂ) => a t) (r := u)
    (ω := 0) h0 hc hm hne
  exact h

/-- `u ≤ a t` when `τ_u ≤ t`. -/
theorem le_clock_of_sInf_le (h0 : a 0 = 0) (hc : Continuous a) (hm : Monotone a) {u t : ℝ≥0}
    (hne : ∃ t, u < a t) (h : sInf {s | u < a s} ≤ t) : u ≤ a t := by
  rw [← clock_sInf_eq h0 hc hm hne]
  exact hm h

/-- The right inverse of a nondecreasing unbounded clock is nondecreasing. -/
theorem monotone_sInf_clock (hU : ∀ u : ℝ≥0, ∃ t, u < a t) :
    Monotone fun u : ℝ => ((sInf {s | u.toNNReal < a s} : ℝ≥0) : ℝ) := by
  intro u v huv
  have h : {s | v.toNNReal < a s} ⊆ {s | u.toNNReal < a s} := fun s hs =>
    lt_of_le_of_lt (Real.toNNReal_mono huv) hs
  exact NNReal.coe_le_coe.2 (csInf_le_csInf (OrderBot.bddBelow _) (hU _) h)

/-- **The image of Lebesgue measure under the right inverse of a clock is its Stieltjes
measure.** -/
theorem map_volume_clockInverse_eq_stieltjes (h0 : a 0 = 0) (hc : Continuous a)
    (hm : Monotone a) (hU : ∀ u : ℝ≥0, ∃ t, u < a t) :
    (volume.restrict (Ioi (0 : ℝ))).map
        (fun u : ℝ => ((sInf {s | u.toNNReal < a s} : ℝ≥0) : ℝ)) =
      (clockStieltjesFunction a).measure := by
  have hmeas : Measurable fun u : ℝ => ((sInf {s | u.toNNReal < a s} : ℝ≥0) : ℝ) :=
    (monotone_sInf_clock hU).measurable
  refine (Measure.ext_of_Ioc _ _ fun l r hlr => ?_).symm
  rw [clockStieltjesFunction_measure_Ioc hm hc, Measure.map_apply hmeas measurableSet_Ioc,
    Measure.restrict_apply (hmeas measurableSet_Ioc)]
  set al : ℝ := ((a l.toNNReal : ℝ≥0) : ℝ) with hal
  set ar : ℝ := ((a r.toNNReal : ℝ≥0) : ℝ) with har
  have hsub1 : Ioo al ar ⊆ (fun u : ℝ => ((sInf {s | u.toNNReal < a s} : ℝ≥0) : ℝ)) ⁻¹'
      Ioc l r ∩ Ioi 0 := by
    intro u hu
    have hu0 : 0 < u := lt_of_le_of_lt (NNReal.coe_nonneg _) hu.1
    have hur : u.toNNReal < a r.toNNReal := by
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hu0.le]
      exact hu.2
    refine ⟨⟨?_, ?_⟩, hu0⟩
    · by_cases hl : l < 0
      · exact lt_of_lt_of_le hl (NNReal.coe_nonneg _)
      · have hl' : 0 ≤ l := not_lt.1 hl
        by_contra hle
        have hle' : sInf {s | u.toNNReal < a s} ≤ l.toNNReal := by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hl']
          exact not_lt.1 hle
        have h1 := le_clock_of_sInf_le h0 hc hm (hU _) hle'
        have h2 : (u.toNNReal : ℝ) ≤ al := by exact_mod_cast h1
        rw [Real.coe_toNNReal _ hu0.le] at h2
        exact absurd hu.1 (not_lt.2 h2)
    · have h1 := sInf_lt_clock_le hur
      have h2 : ((sInf {s | u.toNNReal < a s} : ℝ≥0) : ℝ) ≤ r.toNNReal := by exact_mod_cast h1
      by_cases hr : r < 0
      · exfalso
        have : ar = a 0 := by rw [har, Real.toNNReal_of_nonpos hr.le]
        rw [this, h0] at hu
        have : al = a 0 := by rw [hal, Real.toNNReal_of_nonpos (hlr.trans hr).le]
        rw [this, h0] at hu
        exact lt_irrefl _ (hu.1.trans hu.2)
      · rwa [Real.coe_toNNReal _ (not_lt.1 hr)] at h2
  have hsub2 : (fun u : ℝ => ((sInf {s | u.toNNReal < a s} : ℝ≥0) : ℝ)) ⁻¹' Ioc l r ∩ Ioi 0 ⊆
      Icc al ar := by
    rintro u ⟨⟨h1, h2⟩, hu0⟩
    have hu0' : (0 : ℝ) < u := hu0
    have h2' : sInf {s | u.toNNReal < a s} ≤ r.toNNReal := by
      rw [← NNReal.coe_le_coe]
      exact h2.trans (Real.le_coe_toNNReal r)
    have hur := le_clock_of_sInf_le h0 hc hm (hU _) h2'
    refine ⟨?_, ?_⟩
    · by_contra hlt
      rw [not_le] at hlt
      have hl0 : 0 ≤ l := by
        by_contra hl
        have : al = a 0 := by rw [hal, Real.toNNReal_of_nonpos (not_le.1 hl).le]
        rw [this, h0] at hlt
        exact absurd hlt (not_lt.2 hu0'.le)
      have hlt' : u.toNNReal < a l.toNNReal := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hu0'.le]
        exact hlt
      have h3 := sInf_lt_clock_le hlt'
      have h4 : ((sInf {s | u.toNNReal < a s} : ℝ≥0) : ℝ) ≤ l := by
        rw [← Real.coe_toNNReal _ hl0]
        exact_mod_cast h3
      exact absurd h1 (not_lt.2 h4)
    · have : ((u.toNNReal : ℝ≥0) : ℝ) ≤ ar := by exact_mod_cast hur
      rwa [Real.coe_toNNReal _ hu0'.le] at this
  refine le_antisymm ?_ ?_
  · rw [← Real.volume_Ioo]
    exact measure_mono hsub1
  · rw [← Real.volume_Icc]
    exact measure_mono hsub2

end Deterministic

/-! ### Occupation integrals in the time of the time change -/

/-- The occupation integral `∫_0^∞ F(τ̄_u, Y_u) du` of `F` along the time change of the path `b`
by the rational-time regularization of `A`. -/
noncomputable def clockOccupation (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) (F : ℝ × ℂ → ℝ≥0∞)
    (b : ContinuousPath ℂ) : ℝ≥0∞ :=
  ∫⁻ u in Ioi (0 : ℝ), F ((pcafClockInverse (clockRationalRegularization A) u.toNNReal b : ℝ),
    unitSquareTimeChangeRegularized A u.toNNReal b)

/-- The pair `(τ̄_u, Y_u)` is jointly measurable in `(u, b)`. -/
theorem measurable_clockInverse_timeChange_uncurry {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) :
    Measurable fun p : ContinuousPath ℂ × ℝ =>
      ((pcafClockInverse (clockRationalRegularization A) p.2.toNNReal p.1 : ℝ),
        unitSquareTimeChangeRegularized A p.2.toNNReal p.1) := by
  have hτ : Measurable fun p : ContinuousPath ℂ × ℝ =>
      pcafClockInverse (clockRationalRegularization A) p.2.toNNReal p.1 :=
    (measurable_pcafClockInverse_uncurry (measurable_clockRationalRegularization hA)
      (clockRationalRegularization_monotone A)).comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
  refine (NNReal.continuous_coe.measurable.comp hτ).prodMk ?_
  exact measurable_path_eval_uncurry.comp (hτ.prodMk measurable_fst)

theorem measurable_clockOccupation {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) {F : ℝ × ℂ → ℝ≥0∞} (hF : Measurable F) :
    Measurable (clockOccupation A F) :=
  (hF.comp (measurable_clockInverse_timeChange_uncurry hA)).lintegral_prod_right'

/-- **Occupation integrals in the time of the time change.** Along a path on which `A` is
continuous, nondecreasing, starts at `0` and is unbounded, the Stieltjes integral
`∫ F(s, b_s) dA_s` is `clockOccupation A F b`. -/
theorem clockOccupation_eq_lintegral_stieltjes {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    {b : ContinuousPath ℂ} (h0 : A 0 b = 0) (hc : Continuous fun t => A t b)
    (hm : Monotone fun t => A t b) (hU : ∀ u : ℝ≥0, ∃ t, u < A t b) {F : ℝ × ℂ → ℝ≥0∞}
    (hF : Measurable F) :
    clockOccupation A F b =
      ∫⁻ s, F (s, b s.toNNReal) ∂(clockStieltjesFunction fun t => A t b).measure := by
  have hreg : ∀ t, clockRationalRegularization A t b = A t b :=
    clockRationalRegularization_eq_of_continuous_monotone hc hm
  have hG : Measurable fun s : ℝ => F (s, b s.toNNReal) :=
    hF.comp (measurable_id.prodMk
      ((b.continuous.comp continuous_real_toNNReal).measurable))
  rw [← map_volume_clockInverse_eq_stieltjes (a := fun t => A t b) h0 hc hm hU,
    lintegral_map hG (monotone_sInf_clock hU).measurable]
  unfold clockOccupation unitSquareTimeChangeRegularized pcafClockInverse
  simp only [hreg, Real.toNNReal_coe]

/-- The weight `1_I(s) g(y)` of an occupation integral over the time window `I`. -/
noncomputable def windowWeight (I : Set ℝ) (g : ℂ → ℝ≥0∞) : ℝ × ℂ → ℝ≥0∞ :=
  (I ×ˢ univ).indicator fun p => g p.2

theorem measurable_windowWeight {I : Set ℝ} (hI : MeasurableSet I) {g : ℂ → ℝ≥0∞}
    (hg : Measurable g) : Measurable (windowWeight I g) :=
  (hg.comp measurable_snd).indicator (hI.prod MeasurableSet.univ)

theorem windowWeight_apply (I : Set ℝ) (g : ℂ → ℝ≥0∞) (s : ℝ) (y : ℂ) :
    windowWeight I g (s, y) = I.indicator (fun _ => g y) s := by
  by_cases hs : s ∈ I <;> simp [windowWeight, indicator, hs]

/-- **The Revuz formula in the time of the time change**:
`∫ g d(Rev A) = ∫_{K₀} dz E_z ∫_0^∞ 1_{(0,1]}(τ̄_u) g(Y_u) du`, for a clock unbounded from every
start in `K₀`. -/
theorem lintegral_unitSquareRevuzMeasure_eq_clockOccupation {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A)
    (hU : ∀ z ∈ closedSquare 0 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun t => A t b) atTop atTop) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y, g y ∂unitSquareRevuzMeasure A = ∫⁻ z in closedSquare 0 1, ∫⁻ b,
      clockOccupation A (windowWeight (Ioc 0 1) g) b ∂reflectedPlanarBrownianMotion 0 1 z := by
  rw [lintegral_unitSquareRevuzMeasure_of_isUnitSquarePCAF hA hg]
  refine setLIntegral_congr_fun (isCompact_closedSquare 0 1).isClosed.measurableSet
    fun z hz => lintegral_congr_ae ?_
  filter_upwards [hA.path z hz, hU z hz] with b hp hu
  rw [lintegral_clockOccupationMeasure _ _ hg, clockOccupation_eq_lintegral_stieltjes hp.1
    hp.2.1 hp.2.2 (fun u => (hu.eventually_gt_atTop u).exists)
    (measurable_windowWeight measurableSet_Ioc hg), ← lintegral_indicator measurableSet_Ioc]
  refine lintegral_congr fun s => ?_
  rw [windowWeight_apply]
  by_cases hs : s ∈ Ioc (0 : ℝ) 1 <;> simp [hs]

/-- **The occupation integral after a fixed time.** For a clock unbounded from `z ∈ K₀` and a
time `t`, almost surely, for every measurable `F ≥ 0`, the occupation integral of
`1_{s > t} F(s, y)` along `b` is the occupation integral of `F(t + s, y)` along `θ_t b`. -/
theorem ae_clockOccupation_indicator_Ioi_eq_shift {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {z : ℂ} (hz : z ∈ closedSquare 0 1)
    (hU : ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z, Tendsto (fun t => A t b) atTop atTop)
    (t : ℝ≥0) :
    ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z, ∀ F : ℝ × ℂ → ℝ≥0∞, Measurable F →
      clockOccupation A (fun p => (Ioi (t : ℝ)).indicator (fun _ => F p) p.1) b =
        clockOccupation A (fun p => F ((t : ℝ) + p.1, p.2)) (ContinuousPath.shift t b) := by
  filter_upwards [hA.path z hz, hU, ae_add_clockRationalRegularization_shift hA hz t]
    with b hp hu hadd F hF
  have hreg : ∀ s, clockRationalRegularization A s b = A s b :=
    clockRationalRegularization_eq_of_continuous_monotone hp.2.1 hp.2.2
  have hne : ∀ u : ℝ≥0, ∃ s, u < A s b := fun u => (hu.eventually_gt_atTop u).exists
  set θb := ContinuousPath.shift t b with hθb
  set At : ℝ := (A t b : ℝ) with hAt
  have hτ : ∀ u : ℝ≥0, pcafClockInverse (clockRationalRegularization A) u b =
      pcafClockInverse A u b := by
    intro u
    unfold pcafClockInverse
    simp only [hreg]
  -- the shift of the inverse clock at level `A t + v`
  have hshift : ∀ v : ℝ≥0, pcafClockInverse A (A t b + v) b =
      t + pcafClockInverse (clockRationalRegularization A) v θb := fun v =>
    pcafClockInverse_add_eq_of_shift hp.2.2 hadd (hne _)
  -- below level `A t` the inverse clock is at most `t`
  have hlow : ∀ u : ℝ, 0 < u → u < At →
      ¬ (t : ℝ) < (pcafClockInverse (clockRationalRegularization A) u.toNNReal b : ℝ) := by
    intro u hu0 hut
    rw [hτ, not_lt, NNReal.coe_le_coe]
    refine sInf_lt_clock_le (a := fun s => A s b) ?_
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hu0.le]
    exact hut
  -- above level `A t` it exceeds `t`
  have hhigh : ∀ v : ℝ, 0 < v → (t : ℝ) <
      (pcafClockInverse (clockRationalRegularization A) (At + v).toNNReal b : ℝ) := by
    intro v hv
    rw [hτ]
    by_contra hle
    rw [not_lt, NNReal.coe_le_coe] at hle
    have h := le_clock_of_sInf_le (a := fun s => A s b) hp.1 hp.2.1 hp.2.2 (hne _) hle
    have h' : ((At + v).toNNReal : ℝ) ≤ At := by exact_mod_cast h
    rw [Real.coe_toNNReal _ (by positivity)] at h'
    linarith
  have hlev : ∀ v : ℝ, 0 < v → (At + v).toNNReal = A t b + v.toNNReal := by
    intro v hv
    rw [Real.toNNReal_add (by positivity) hv.le, hAt, Real.toNNReal_coe]
  unfold clockOccupation
  -- split the integral at level `A t`
  have hsplit : ∫⁻ u in Ioi (0 : ℝ), (Ioi (t : ℝ)).indicator (fun _ =>
      F ((pcafClockInverse (clockRationalRegularization A) u.toNNReal b : ℝ),
        unitSquareTimeChangeRegularized A u.toNNReal b))
      (pcafClockInverse (clockRationalRegularization A) u.toNNReal b : ℝ) =
      ∫⁻ u in Ioi At, F ((pcafClockInverse (clockRationalRegularization A) u.toNNReal b : ℝ),
        unitSquareTimeChangeRegularized A u.toNNReal b) := by
    have hAt0 : 0 ≤ At := NNReal.coe_nonneg _
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr_ae ?_
    filter_upwards [(measure_singleton At : volume {At} = 0) |> measure_eq_zero_iff_ae_notMem.1]
      with u hu
    by_cases h1 : At < u
    · have hu0 : 0 < u := lt_of_le_of_lt hAt0 h1
      have h2 := hhigh (u - At) (by linarith)
      rw [show At + (u - At) = u by ring] at h2
      simp [indicator, hu0, h1, h2]
    · by_cases hu0 : 0 < u
      · have hlt : u < At := lt_of_le_of_ne (not_lt.1 h1) hu
        simp [indicator, hu0, h1, hlow u hu0 hlt]
      · simp [indicator, hu0, h1]
  rw [hsplit]
  -- translate by `A t`
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi,
    ← lintegral_add_left_eq_self (μ := volume) _ At]
  refine lintegral_congr fun v => ?_
  by_cases hv : 0 < v
  · have hv' : At < At + v := by linarith
    simp only [indicator, mem_Ioi, hv', hv, if_true]
    rw [hlev v hv, hτ, hshift]
    have hY : unitSquareTimeChangeRegularized A (A t b + v.toNNReal) b =
        unitSquareTimeChangeRegularized A v.toNNReal θb := by
      unfold unitSquareTimeChangeRegularized
      rw [hτ, hshift, hθb, ContinuousPath.shift_apply]
    rw [hY]
    push_cast
    rfl
  · have hv' : ¬ At < At + v := by linarith
    simp only [indicator, mem_Ioi, hv', hv, if_false]

/-- **Stationarity of reflected Brownian motion started from Lebesgue measure on `K₀`**, with a
weight at the time of the shift: `∫_{K₀} dz E_z[h(b_t) Ψ(θ_t b)] = ∫_{K₀} h(z) E_z Ψ dz`. -/
theorem setLIntegral_lintegral_mul_shift_eq {h : ℂ → ℝ≥0∞} (hh : Measurable h)
    {Ψ : ContinuousPath ℂ → ℝ≥0∞} (hΨ : Measurable Ψ) (t : ℝ≥0) :
    ∫⁻ z in closedSquare 0 1, ∫⁻ b, h (b t) * Ψ (ContinuousPath.shift t b)
        ∂reflectedPlanarBrownianMotion 0 1 z =
      ∫⁻ z in closedSquare 0 1, h z * ∫⁻ b, Ψ b ∂reflectedPlanarBrownianMotion 0 1 z := by
  have hφ : Measurable fun y => ∫⁻ b, Ψ b ∂reflectedPlanarBrownianMotion 0 1 y :=
    hΨ.lintegral_kernel
  have hfold : Measurable (squareFold 0 1) := (continuous_squareFold 0 1).measurable
  have h1 : ∀ z, ∫⁻ b, h (b t) * Ψ (ContinuousPath.shift t b) ∂reflectedPlanarBrownianMotion 0 1 z =
      ∫⁻ b, (fun y => h y * ∫⁻ b', Ψ b' ∂reflectedPlanarBrownianMotion 0 1 y) (b t)
        ∂reflectedPlanarBrownianMotion 0 1 z := by
    intro z
    rw [lintegral_reflected_eval_mul_shift hh hΨ t z,
      lintegral_reflected_eval_eq t (v := fun y => h y * ∫⁻ b', Ψ b'
        ∂reflectedPlanarBrownianMotion 0 1 y) (hh.mul hφ) z]
    refine lintegral_congr fun w => ?_
    rw [reflectedPlanarBrownianMotion_zero_one_squareFold]
  simp_rw [h1]
  exact lintegral_lintegral_reflectedPlanarBrownianMotion_eval t (hh.mul hφ)

/-- **Stationarity**: `∫_{K₀} dz E_z Ψ(θ_t b) = ∫_{K₀} dz E_z Ψ(b)`. -/
theorem setLIntegral_lintegral_shift_eq {Ψ : ContinuousPath ℂ → ℝ≥0∞} (hΨ : Measurable Ψ)
    (t : ℝ≥0) :
    ∫⁻ z in closedSquare 0 1, ∫⁻ b, Ψ (ContinuousPath.shift t b)
        ∂reflectedPlanarBrownianMotion 0 1 z =
      ∫⁻ z in closedSquare 0 1, ∫⁻ b, Ψ b ∂reflectedPlanarBrownianMotion 0 1 z := by
  have h := setLIntegral_lintegral_mul_shift_eq (h := fun _ => 1) measurable_const hΨ t
  simpa using h

end HarmonicBalls
