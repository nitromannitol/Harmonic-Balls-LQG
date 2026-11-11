import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proofs.Sec8.ConcentricCircleCovariance

/-!
# Circle averages of a whole-plane GFF at radius `r ∈ (0, 1]`

The circle average `h_r(0)` of the whole-plane GFF (normalized so that `h_1(0) = 0`, `IsWholePlaneGFF`) is
centered with variance `-log r` (Duplantier-Sheffield, arXiv:0808.1560v2, Section 3.1; Bou-Rabee-Gwynne,
arXiv:2208.11795v3, Section 2.1, eq. (2.1), p. 8). It is square integrable, and Chebyshev's inequality gives the
tail bound used for the normalizing shift in the LQG exponent argument. Only the covariance and Gaussian clauses
of `IsWholePlaneGFF` are used; the covariance kernel is `wholePlaneGFFCov` (Proofs/Sec8/ConcentricCircleCovariance).
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set

/-- The covariance of two circle averages of the whole-plane GFF at the same radius `r ∈ (0, 1]` and centre `0`
is `-log r`. -/
theorem wholePlaneGFFCov_circle_zero_of_le_one {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    wholePlaneGFFCov (.circle r 0) (.circle r 0) = -Real.log r := by
  rw [wholePlaneGFFCov_concentric_circles_general hr hr 0]
  have hA : Real.circleAverage wholePlaneNormalization 0 r = 0 := by
    rw [Real.circleAverage_congr_sphere (f₂ := fun _ => (0 : ℝ)), Real.circleAverage_const]
    intro x hx
    have hx' : ‖x‖ = r := by simpa [abs_of_pos hr] using hx
    simp [wholePlaneNormalization, hx', max_eq_right hr1, Real.log_one]
  rw [hA, max_self]
  ring

/-- For a whole-plane GFF, the circle average `hcirc ω r 0` at radius `r ∈ (0, 1]` is centered with variance
`-log r`. -/
theorem wholePlaneGFF_circle_zero_mean_var {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∫ ω, hcirc ω r 0 ∂P = 0 ∧ variance (fun ω => hcirc ω r 0) P = -Real.log r := by
  have hc : cov[fun ω => hcirc ω r 0, fun ω => hcirc ω r 0; P] =
      wholePlaneGFFCov (.circle r 0) (.circle r 0) :=
    h.covariance_eq (.circle r 0) (.circle r 0) hr hr
  refine ⟨h.integral_eq_zero (.circle r 0) hr, ?_⟩
  rw [← covariance_self (h.measurable_circle r 0 hr).aemeasurable, hc,
    wholePlaneGFFCov_circle_zero_of_le_one hr hr1]

/-- The circle average `hcirc ω r 0` of a whole-plane GFF at positive radius is square integrable. -/
theorem wholePlaneGFF_circle_zero_memLp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    {r : ℝ} (hr : 0 < r) : MemLp (fun ω => hcirc ω r 0) 2 P :=
  (h.isGaussianProcess.hasGaussianLaw_eval (⟨.circle r 0, hr⟩ : GFFObservable.Admissible)).memLp_two

/-- Chebyshev bound for a centered square-integrable variable of variance `s > 0`:
`P(Q s < X) ≤ (Q²)⁻¹ s⁻¹` for `Q > 0`. -/
theorem measure_lt_le_inv_of_variance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) (hmean : ∫ ω, X ω ∂P = 0)
    {s Q : ℝ} (hs : 0 < s) (hQ : 0 < Q) (hvar : variance X P = s) :
    P {ω | Q * s < X ω} ≤ ENNReal.ofReal ((Q ^ 2)⁻¹ * s⁻¹) := by
  have hsub : {ω | Q * s < X ω} ⊆ {ω | Q * s ≤ |X ω - P[X]|} := by
    intro ω hω
    have hω' : Q * s < X ω := hω
    have hm : P[X] = 0 := hmean
    show Q * s ≤ |X ω - P[X]|
    rw [hm, sub_zero]
    exact hω'.le.trans (le_abs_self _)
  have hc : 0 < Q * s := mul_pos hQ hs
  have hk : s / (Q * s) ^ 2 = (Q ^ 2)⁻¹ * s⁻¹ := by
    have := hs.ne'
    have := hQ.ne'
    field_simp
  calc P {ω | Q * s < X ω} ≤ P {ω | Q * s ≤ |X ω - P[X]|} := measure_mono hsub
    _ ≤ ENNReal.ofReal (variance X P / (Q * s) ^ 2) :=
        meas_ge_le_variance_div_sq hX hc
    _ = ENNReal.ofReal ((Q ^ 2)⁻¹ * s⁻¹) := by rw [hvar, hk]

end HarmonicBalls
