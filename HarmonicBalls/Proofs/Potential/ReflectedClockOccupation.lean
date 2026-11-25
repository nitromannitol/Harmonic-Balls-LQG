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
    simp only [indicator, mem_Ioi, hv', hv, ite_true]
    rw [hlev v hv, hτ, hshift]
    have hY : unitSquareTimeChangeRegularized A (A t b + v.toNNReal) b =
        unitSquareTimeChangeRegularized A v.toNNReal θb := by
      unfold unitSquareTimeChangeRegularized
      rw [hτ, hshift, hθb, ContinuousPath.shift_apply]
    rw [hY]
    push_cast
    rfl
  · have hv' : ¬ At < At + v := by linarith
    simp only [indicator, mem_Ioi, hv', hv, ite_false]

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

/-! ### Additive monotone functions of time -/

/-- An additive nondecreasing function `f : ℝ≥0 → ℝ≥0∞` with `f 1 < ∞` is `t ↦ t f(1)`. -/
theorem eq_mul_of_add_of_monotone {f : ℝ≥0 → ℝ≥0∞} (hadd : ∀ s t, f (s + t) = f s + f t)
    (hmono : Monotone f) (h1 : f 1 ≠ ⊤) (t : ℝ≥0) : f t = t * f 1 := by
  have hnat : ∀ (n : ℕ) (s : ℝ≥0), f (n * s) = n * f s := by
    intro n s
    induction n with
    | zero =>
      have h0 : f 0 = f 0 + f 0 := by rw [← hadd, add_zero]
      have hfin : f 0 ≠ ⊤ := ne_top_of_le_ne_top h1 (hmono zero_le)
      simp only [Nat.cast_zero, zero_mul]
      have h0' : f 0 + f 0 = f 0 + 0 := by rw [add_zero, ← h0]
      exact (ENNReal.add_right_inj hfin).1 h0'
    | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hadd, ih, Nat.cast_succ, add_mul, one_mul]
  have hmn : ∀ m n : ℕ, 0 < n → f ((m : ℝ≥0) / n) = (((m : ℝ≥0) / n : ℝ≥0) : ℝ≥0∞) * f 1 := by
    intro m n hn
    have hn' : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
    have hn'' : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
    have h := hnat n ((m : ℝ≥0) / n)
    rw [mul_div_cancel₀ (m : ℝ≥0) hn'] at h
    have h2 : f m = m * f 1 := by
      have := hnat m 1
      rwa [mul_one] at this
    rw [h2] at h
    calc f ((m : ℝ≥0) / n) = (n : ℝ≥0∞)⁻¹ * (n * f ((m : ℝ≥0) / n)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hn'' (ENNReal.natCast_ne_top n), one_mul]
      _ = (n : ℝ≥0∞)⁻¹ * (m * f 1) := by rw [← h]
      _ = (((m : ℝ≥0) / n : ℝ≥0) : ℝ≥0∞) * f 1 := by
          rw [ENNReal.coe_div hn', ENNReal.coe_natCast, ENNReal.coe_natCast, div_eq_mul_inv]
          ring
  have hrat : ∀ q : ℚ≥0, f q = ((q : ℝ≥0) : ℝ≥0∞) * f 1 := by
    intro q
    have hq : (q : ℝ≥0) = (q.num : ℝ≥0) / q.den := NNRat.cast_def q
    rw [hq]
    exact hmn _ _ q.den_pos
  refine le_antisymm ?_ ?_
  · refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    by_cases hf1 : f 1 = 0
    · obtain ⟨n, hn⟩ := exists_nat_ge t
      calc f t ≤ f (n * 1) := hmono (by rwa [mul_one])
        _ = 0 := by rw [hnat, hf1, mul_zero]
        _ ≤ c := zero_le
    · obtain ⟨q, hq1, hq2⟩ : ∃ q : ℚ≥0, t < (q : ℝ≥0) ∧ ((q : ℝ≥0) : ℝ≥0∞) * f 1 < c := by
        have hlt : (t : ℝ≥0∞) < c / f 1 := by
          rwa [ENNReal.lt_div_iff_mul_lt (Or.inl hf1) (Or.inl h1)]
        obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
        obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn_nnreal (show t < r by exact_mod_cast hr1)
        refine ⟨q, hq1, ?_⟩
        have h3 : ((q : ℝ≥0) : ℝ≥0∞) < c / f 1 :=
          (show ((q : ℝ≥0) : ℝ≥0∞) < r by exact_mod_cast hq2).trans hr2
        rwa [ENNReal.lt_div_iff_mul_lt (Or.inl hf1) (Or.inl h1)] at h3
      calc f t ≤ f q := hmono hq1.le
        _ = (q : ℝ≥0) * f 1 := hrat q
        _ ≤ c := hq2.le
  · refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
    have hf1 : f 1 ≠ 0 := by
      rintro h
      rw [h, mul_zero] at hc
      exact absurd hc (not_lt.2 zero_le)
    obtain ⟨q, hq1, hq2⟩ : ∃ q : ℚ≥0, (q : ℝ≥0) ≤ t ∧ c ≤ ((q : ℝ≥0) : ℝ≥0∞) * f 1 := by
      have hlt : c / f 1 < t := by
        rwa [ENNReal.div_lt_iff (Or.inl hf1) (Or.inl h1)]
      obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
      obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn_nnreal (show r < t by exact_mod_cast hr2)
      refine ⟨q, hq2.le, ?_⟩
      have h3 : c / f 1 ≤ ((q : ℝ≥0) : ℝ≥0∞) :=
        hr1.le.trans (show (r : ℝ≥0∞) ≤ ((q : ℝ≥0) : ℝ≥0∞) by exact_mod_cast hq1.le)
      rwa [ENNReal.div_le_iff hf1 h1] at h3
    calc c ≤ (q : ℝ≥0) * f 1 := hq2
      _ = f q := (hrat q).symm
      _ ≤ f t := hmono hq1

/-! ### The mean occupation measure from Lebesgue measure on `K₀` -/

/-- The occupation measure of the time change along `b` on (time, position):
the image of Lebesgue measure on `(0, ∞)` under `u ↦ (τ̄_u, Y_u)`. -/
noncomputable def pathOccupationMeasure (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0)
    (b : ContinuousPath ℂ) : Measure (ℝ × ℂ) :=
  (volume.restrict (Ioi (0 : ℝ))).map fun u =>
    ((pcafClockInverse (clockRationalRegularization A) u.toNNReal b : ℝ),
      unitSquareTimeChangeRegularized A u.toNNReal b)

theorem lintegral_pathOccupationMeasure {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) {F : ℝ × ℂ → ℝ≥0∞} (hF : Measurable F) (b : ContinuousPath ℂ) :
    ∫⁻ p, F p ∂pathOccupationMeasure A b = clockOccupation A F b :=
  lintegral_map hF ((measurable_clockInverse_timeChange_uncurry hA).comp measurable_prodMk_left)

theorem measurable_pathOccupationMeasure {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) : Measurable (pathOccupationMeasure A) := by
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  have h : (fun b => pathOccupationMeasure A b S) = clockOccupation A (S.indicator 1) := by
    funext b
    rw [← lintegral_indicator_one hS, lintegral_pathOccupationMeasure hA
      (measurable_one.indicator hS)]
  rw [h]
  exact measurable_clockOccupation hA (measurable_one.indicator hS)

/-- The mean occupation measure of the time change under reflected Brownian motion started from
Lebesgue measure on `K₀`. -/
noncomputable def lebesgueOccupationMeasure (A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0) :
    Measure (ℝ × ℂ) :=
  unitSquareLebesguePathLaw.bind (pathOccupationMeasure A)

theorem lintegral_lebesgueOccupationMeasure {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) {F : ℝ × ℂ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂lebesgueOccupationMeasure A = ∫⁻ z in closedSquare 0 1, ∫⁻ b,
      clockOccupation A F b ∂reflectedPlanarBrownianMotion 0 1 z := by
  rw [lebesgueOccupationMeasure, Measure.lintegral_bind
    (measurable_pathOccupationMeasure hA).aemeasurable hF.aemeasurable]
  simp_rw [lintegral_pathOccupationMeasure hA hF]
  exact lintegral_unitSquareLebesguePathLaw (measurable_clockOccupation hA hF).aemeasurable

theorem lebesgueOccupationMeasure_apply {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : ∀ t, Measurable (A t)) {S : Set (ℝ × ℂ)} (hS : MeasurableSet S) :
    lebesgueOccupationMeasure A S = ∫⁻ z in closedSquare 0 1, ∫⁻ b,
      clockOccupation A (S.indicator 1) b ∂reflectedPlanarBrownianMotion 0 1 z := by
  rw [← lintegral_indicator_one hS, lintegral_lebesgueOccupationMeasure hA
    (measurable_one.indicator hS)]

theorem indicator_prod_eq_windowWeight (I : Set ℝ) (B : Set ℂ) :
    (I ×ˢ B).indicator (1 : ℝ × ℂ → ℝ≥0∞) = windowWeight I (B.indicator 1) := by
  funext p
  by_cases h1 : p.1 ∈ I <;> by_cases h2 : p.2 ∈ B <;>
    simp [windowWeight, indicator, h1, h2, mem_prod]

/-- A measure on `ℝ` without mass on `(-∞, 0]` and with `μ(0, t] = t c` is `c` times Lebesgue
measure on `(0, ∞)`. -/
theorem eq_smul_volume_Ioi_of_Ioc {μ : Measure ℝ} {c : ℝ≥0} (hneg : μ (Iic 0) = 0)
    (hpos : ∀ t : ℝ≥0, μ (Ioc 0 (t : ℝ)) = t * c) : μ = c • volume.restrict (Ioi (0 : ℝ)) := by
  refine (Measure.ext_of_Ioc (c • volume.restrict (Ioi (0 : ℝ))) μ fun l r hlr => ?_).symm
  set l' := max l 0 with hl'
  set r' := max r 0 with hr'
  have hl0 : 0 ≤ l' := le_max_right _ _
  have hlr' : l' ≤ r' := max_le_max hlr.le le_rfl
  have hset : Ioc l r ∩ Ioi 0 = Ioc l' r' := by
    ext x
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi, hl', hr', max_lt_iff, le_max_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h3⟩, Or.inl h2⟩
    · rintro ⟨⟨h1, h3⟩, h2 | h2⟩
      · exact ⟨⟨h1, h2⟩, h3⟩
      · exact absurd h3 (not_lt.2 h2)
  have hμ : μ (Ioc l r) = μ (Ioc l' r') := by
    refine le_antisymm ?_ ?_
    · refine (measure_mono fun x hx => ?_).trans ((measure_union_le (Ioc l' r') (Iic 0)).trans
        (by rw [hneg, add_zero]))
      by_cases hx0 : 0 < x
      · exact Or.inl (hset ▸ ⟨hx, hx0⟩)
      · exact Or.inr (not_lt.1 hx0)
    · refine measure_mono fun x hx => ?_
      have hx' := hset.symm ▸ hx
      exact hx'.1
  have hsplit : μ (Ioc 0 r') = μ (Ioc 0 l') + μ (Ioc l' r') := by
    rw [← measure_union (disjoint_left.2 fun x hx1 hx2 => absurd hx2.1 (not_lt.2 hx1.2))
      measurableSet_Ioc, Ioc_union_Ioc_eq_Ioc hl0 hlr']
  have hr'' : μ (Ioc 0 r') = ENNReal.ofReal r' * c := by
    have h := hpos r'.toNNReal
    rwa [Real.coe_toNNReal _ (hl0.trans hlr')] at h
  have hl'' : μ (Ioc 0 l') = ENNReal.ofReal l' * c := by
    have h := hpos l'.toNNReal
    rwa [Real.coe_toNNReal _ hl0] at h
  rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Ioc, hset, Real.volume_Ioc, hμ]
  have hfin : ENNReal.ofReal l' * c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  rw [hr'', hl''] at hsplit
  have h2 : ENNReal.ofReal r' * c = ENNReal.ofReal l' * c + ENNReal.ofReal (r' - l') * c := by
    rw [← add_mul, ← ENNReal.ofReal_add hl0 (sub_nonneg.2 hlr'), add_sub_cancel]
  rw [h2] at hsplit
  have := (ENNReal.add_right_inj hfin).1 hsplit
  show (c : ℝ≥0∞) * ENNReal.ofReal (r' - l') = μ (Ioc l' r')
  rw [← this, mul_comm]

/-- **The mean occupation measure under Lebesgue start is `ds ⊗ Rev A`** (Revuz–Yor (1999),
Chapter X, Section 2; Fukushima–Oshima–Takeda (2011), (5.1.11)): additivity and stationarity make
the mass of `(0, t] × B` additive in `t`, and it is `Rev A (B)` at `t = 1`. -/
theorem lebesgueOccupationMeasure_eq_prod {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A)
    (hU : ∀ z ∈ closedSquare 0 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun t => A t b) atTop atTop) [IsFiniteMeasure (unitSquareRevuzMeasure A)] :
    lebesgueOccupationMeasure A =
      (volume.restrict (Ioi (0 : ℝ))).prod (unitSquareRevuzMeasure A) := by
  set ν := unitSquareRevuzMeasure A with hν
  set M := lebesgueOccupationMeasure A with hM
  have hKm : MeasurableSet (closedSquare 0 1) :=
    (isCompact_closedSquare 0 1).isClosed.measurableSet
  -- no mass at nonpositive times
  have hneg : M (Iic 0 ×ˢ univ) = 0 := by
    rw [hM, lebesgueOccupationMeasure_apply hA.measurable (measurableSet_Iic.prod MeasurableSet.univ)]
    refine (setLIntegral_congr_fun hKm (g := fun _ => 0) fun z hz =>
      (lintegral_congr_ae (g := fun _ => 0) ?_).trans (by simp)).trans (by simp)
    filter_upwards [hA.path z hz, hU z hz] with b hp hu
    unfold clockOccupation
    refine (setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) fun u hu0 => ?_).trans
      (by simp)
    have hreg : ∀ s, clockRationalRegularization A s b = A s b :=
      clockRationalRegularization_eq_of_continuous_monotone hp.2.1 hp.2.2
    have hpos : 0 < (pcafClockInverse (clockRationalRegularization A) u.toNNReal b : ℝ) := by
      by_contra hle
      have hle' : pcafClockInverse (clockRationalRegularization A) u.toNNReal b ≤ 0 := by
        rw [← NNReal.coe_le_coe]
        exact not_lt.1 hle
      unfold pcafClockInverse at hle'
      simp only [hreg] at hle'
      have h := le_clock_of_sInf_le (a := fun s => A s b) hp.1 hp.2.1 hp.2.2
        (hu.eventually_gt_atTop _).exists hle'
      rw [hp.1] at h
      have : (u.toNNReal : ℝ) ≤ 0 := by exact_mod_cast h
      rw [Real.coe_toNNReal _ (le_of_lt hu0)] at this
      exact absurd (hu0 : (0 : ℝ) < u) (not_lt.2 this)
    simp [indicator, mem_prod, not_le.2 hpos]
  -- the mass of `(0, t] × B` is linear in `t`
  have hJ : ∀ B : Set ℂ, MeasurableSet B → ∀ t : ℝ≥0,
      M (Ioc 0 (t : ℝ) ×ˢ B) = t * ν B := by
    intro B hB
    set f : ℝ≥0 → ℝ≥0∞ := fun t => M (Ioc 0 (t : ℝ) ×ˢ B) with hf
    have hf_eq : ∀ I : Set ℝ, MeasurableSet I → M (I ×ˢ B) = ∫⁻ z in closedSquare 0 1, ∫⁻ b,
        clockOccupation A (windowWeight I (B.indicator 1)) b ∂reflectedPlanarBrownianMotion 0 1 z := by
      intro I hI
      rw [hM, lebesgueOccupationMeasure_apply hA.measurable (hI.prod hB),
        indicator_prod_eq_windowWeight]
    have hmeasW : ∀ I : Set ℝ, MeasurableSet I →
        Measurable (windowWeight I (B.indicator (1 : ℂ → ℝ≥0∞))) := fun I hI =>
      measurable_windowWeight hI (measurable_one.indicator hB)
    have hshift : ∀ s t : ℝ≥0, M (Ioc (s : ℝ) (s + t) ×ˢ B) = M (Ioc 0 (t : ℝ) ×ˢ B) := by
      intro s t
      rw [hf_eq _ measurableSet_Ioc, hf_eq _ measurableSet_Ioc]
      have h1 : ∀ z ∈ closedSquare 0 1, ∫⁻ b, clockOccupation A
          (windowWeight (Ioc (s : ℝ) (s + t)) (B.indicator 1)) b ∂reflectedPlanarBrownianMotion 0 1 z =
          ∫⁻ b, clockOccupation A (windowWeight (Ioc 0 (t : ℝ)) (B.indicator 1))
            (ContinuousPath.shift s b) ∂reflectedPlanarBrownianMotion 0 1 z := by
        intro z hz
        refine lintegral_congr_ae ?_
        filter_upwards [ae_clockOccupation_indicator_Ioi_eq_shift hA hz (hU z hz) s] with b hb
        have h := hb (windowWeight (Ioc (s : ℝ) (s + t)) (B.indicator 1))
          (hmeasW _ measurableSet_Ioc)
        have e1 : (fun p : ℝ × ℂ => (Ioi (s : ℝ)).indicator (fun _ =>
            windowWeight (Ioc (s : ℝ) (s + t)) (B.indicator 1) p) p.1) =
            windowWeight (Ioc (s : ℝ) (s + t)) (B.indicator 1) := by
          funext p
          by_cases hp : p.1 ∈ Ioc (s : ℝ) (s + t)
          · simp [indicator, show p.1 ∈ Ioi (s : ℝ) from hp.1]
          · simp [windowWeight, indicator, hp, mem_prod]
        have e2 : (fun p : ℝ × ℂ => windowWeight (Ioc (s : ℝ) (s + t)) (B.indicator 1)
            ((s : ℝ) + p.1, p.2)) = windowWeight (Ioc 0 (t : ℝ)) (B.indicator 1) := by
          funext p
          have : (s : ℝ) + p.1 ∈ Ioc (s : ℝ) (s + t) ↔ p.1 ∈ Ioc (0 : ℝ) t := by
            simp only [mem_Ioc]
            constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
          by_cases hp : p.1 ∈ Ioc (0 : ℝ) t
          · simp [windowWeight, indicator, mem_prod, hp, this.2 hp]
          · simp [windowWeight, indicator, mem_prod, hp, mt this.1 hp]
        rw [e1, e2] at h
        exact h
      rw [setLIntegral_congr_fun hKm h1]
      exact setLIntegral_lintegral_shift_eq (measurable_clockOccupation hA.measurable
        (hmeasW _ measurableSet_Ioc)) s
    have hadd : ∀ s t, f (s + t) = f s + f t := by
      intro s t
      show M (Ioc 0 ((s + t : ℝ≥0) : ℝ) ×ˢ B) = M (Ioc 0 (s : ℝ) ×ˢ B) + M (Ioc 0 (t : ℝ) ×ˢ B)
      rw [← hshift s t, ← measure_union (disjoint_left.2 fun p hp1 hp2 => ?_)
        (measurableSet_Ioc.prod hB), ← union_prod, NNReal.coe_add,
        Ioc_union_Ioc_eq_Ioc (NNReal.coe_nonneg s) (by linarith [NNReal.coe_nonneg t])]
      exact absurd hp2.1.1 (not_lt.2 hp1.1.2)
    have hmono : Monotone f := fun s t hst =>
      measure_mono (prod_mono (Ioc_subset_Ioc le_rfl (by exact_mod_cast hst)) subset_rfl)
    have h1 : f 1 = ν B := by
      rw [hf]
      simp only [NNReal.coe_one]
      rw [hf_eq _ measurableSet_Ioc, hν, ← lintegral_unitSquareRevuzMeasure_eq_clockOccupation hA hU
        (measurable_one.indicator hB), lintegral_indicator_one hB]
    intro t
    rw [show M (Ioc 0 (t : ℝ) ×ˢ B) = f t from rfl, eq_mul_of_add_of_monotone hadd hmono
      (by rw [h1]; exact measure_ne_top _ _) t, h1]
  -- the measures agree on all measurable rectangles
  refine (Measure.prod_eq fun S B hS hB => ?_).symm
  set m : Measure ℝ := (M.restrict (univ ×ˢ B)).map Prod.fst with hm
  have hmS : ∀ S : Set ℝ, MeasurableSet S → m S = M (S ×ˢ B) := by
    intro S hS
    rw [hm, Measure.map_apply measurable_fst hS, Measure.restrict_apply (measurable_fst hS)]
    congr 1
    ext p
    simp [mem_prod]
  have hνB : ν B ≠ ⊤ := measure_ne_top _ _
  have hm_eq : m = (ν B).toNNReal • volume.restrict (Ioi (0 : ℝ)) := by
    refine eq_smul_volume_Ioi_of_Ioc ?_ fun t => ?_
    · rw [hmS _ measurableSet_Iic]
      exact measure_mono_null (prod_mono subset_rfl (subset_univ B)) hneg
    · rw [hmS _ measurableSet_Ioc, hJ B hB t, ENNReal.coe_toNNReal hνB]
  rw [← hmS S hS, hm_eq, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    ENNReal.coe_toNNReal hνB, mul_comm]

end HarmonicBalls
