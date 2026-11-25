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

end HarmonicBalls
