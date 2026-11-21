import HarmonicBalls.Proofs.Potential.LQGClockStoppedDomainGluing
import HarmonicBalls.Proofs.Potential.LQGClockExteriorClockHorizon
import HarmonicBalls.Proofs.Potential.LQGClockHalfDiscConvergence
import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveHalfDiscConvergence
import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveHalfDiscHorizon

/-! # Exit-stopped clocks from half-disc convergence

For `0 < γ` with `γ ^ 2 < 2`, the closed half-disc clocks converge uniformly on the unit time
interval for nonpositive insertions and for positive insertions in the range of the inner cutoff
estimates. Combined with the exterior cell moment bound, the full inserted clocks stopped at the
exit of a bounded open domain converge uniformly on `[0, 1]` almost surely under the field-path
product law. With the cell moment bound at every start, the same holds locally uniformly on
`[0, ∞)`.

## Main results

* `ae_tendstoUniformlyOn_stopped_domain_clock_nonpositive_of_cell_moment`: nonpositive insertions.
* `ae_tendstoUniformlyOn_stopped_domain_clock_of_cell_moment`: positive insertions with
  `γ ^ 2 / 2 < 2 (2 - γ α) / (2 + γ α)`.
* `ae_exists_locally_uniform_limit_stopped_domain_clock_nonpositive_of_cell_moment` and
  `ae_exists_locally_uniform_limit_stopped_domain_clock_of_cell_moment`: all finite horizons.
-/

open MeasureTheory MarkovProcess Set Filter Topology
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- For a nonpositive insertion and `γ ^ 2 < 2`, the exterior cell moment bound gives almost
sure uniform convergence on `[0, 1]` of the full inserted clocks stopped at the exit of a
bounded open domain, to a continuous, nondecreasing and nonnegative limit. -/
theorem ae_tendstoUniformlyOn_stopped_domain_clock_nonpositive_of_cell_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ ^ 2 < 2) (hα : α ≤ 0) (x : ℂ)
    {D : Set ℂ} (hD : IsOpen D) {R : ℝ} (hR : 0 < R) (hDR : ∀ z ∈ D, ‖z‖ ≤ R)
    {p a C : ℝ} (hp : 0 < p) (ha : 1 < a)
    (hmom : ∀ n m j : ℕ, j < 2 ^ m →
      ∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc ((j : ℝ) / 2 ^ m) ((j + 1) / 2 ^ m),
        ENNReal.ofReal ({z : ℂ | (1 : ℝ) / 2 < ‖z‖ ∧ ‖z‖ ≤ R}.indicator (fun z =>
          dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z))
          (q.2 s.toNNReal))) ^ p ∂(P.prod (planarBrownianMotion x)) ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ m)⁻¹ ^ a)) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), ∃ F : ℝ → ℝ,
      ContinuousOn F (Icc 0 1) ∧ MonotoneOn F (Icc 0 1) ∧ (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ F t) ∧
      TendstoUniformlyOn (fun n (t : ℝ) =>
        ∫ s in (0 : ℝ)..min t (ContinuousPath.exitTime D q.2).toReal,
          dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1))
              (q.2 s.toNNReal))) F atTop (Icc 0 1) :=
  ae_tendstoUniformlyOn_stopped_domain_clock_of_halfDisc_of_cell_moment hh hγ0
    (by nlinarith) α x hD hR hDR
    (ae_prod_exists_regular_uniform_limit_nonpositive_halfDiscClock hh x hγ0 hγ2 hα) hp ha hmom

/-- For a positive insertion with `γ α < 2`, `γ ^ 2 < 2` and
`γ ^ 2 / 2 < 2 (2 - γ α) / (2 + γ α)`, the exterior cell moment bound gives almost sure
uniform convergence on `[0, 1]` of the full inserted clocks stopped at the exit of a bounded
open domain, to a continuous, nondecreasing and nonnegative limit. -/
theorem ae_tendstoUniformlyOn_stopped_domain_clock_of_cell_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hq0 : 0 < γ * α) (hq2 : γ * α < 2) (hγ0 : 0 < γ) (hγ2 : γ ^ 2 < 2)
    (hsub : γ ^ 2 / 2 < 2 * (2 - γ * α) / (2 + γ * α)) (x : ℂ)
    {D : Set ℂ} (hD : IsOpen D) {R : ℝ} (hR : 0 < R) (hDR : ∀ z ∈ D, ‖z‖ ≤ R)
    {p a C : ℝ} (hp : 0 < p) (ha : 1 < a)
    (hmom : ∀ n m j : ℕ, j < 2 ^ m →
      ∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc ((j : ℝ) / 2 ^ m) ((j + 1) / 2 ^ m),
        ENNReal.ofReal ({z : ℂ | (1 : ℝ) / 2 < ‖z‖ ∧ ‖z‖ ≤ R}.indicator (fun z =>
          dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1)) z))
          (q.2 s.toNNReal))) ^ p ∂(P.prod (planarBrownianMotion x)) ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ m)⁻¹ ^ a)) :
    ∀ᵐ q ∂(P.prod (planarBrownianMotion x)), ∃ F : ℝ → ℝ,
      ContinuousOn F (Icc 0 1) ∧ MonotoneOn F (Icc 0 1) ∧ (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ F t) ∧
      TendstoUniformlyOn (fun n (t : ℝ) =>
        ∫ s in (0 : ℝ)..min t (ContinuousPath.exitTime D q.2).toReal,
          dyadicScale (n + 1) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (dyadicScale (n + 1))
              (q.2 s.toNNReal))) F atTop (Icc 0 1) :=
  ae_tendstoUniformlyOn_stopped_domain_clock_of_halfDisc_of_cell_moment hh hγ0
    (by nlinarith) α x hD hR hDR
    (ae_prod_exists_regular_uniform_limit_halfDiscClock hh x hq0 hq2 hγ0 hγ2 hsub) hp ha hmom

/-- For a nonpositive insertion and `γ ^ 2 < 2`, the exterior cell moment bound at every
start gives almost sure locally uniform convergence on `[0, ∞)` of the full inserted clocks
stopped at the exit of a domain contained in the disc of radius `R`, to a continuous,
nonnegative and nondecreasing limit. -/
theorem ae_exists_locally_uniform_limit_stopped_domain_clock_nonpositive_of_cell_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ ^ 2 < 2) (hα : α ≤ 0) (x : ℂ)
    {D : Set ℂ} {R : ℝ} (hR : 0 < R) (hDR : ∀ z ∈ D, ‖z‖ ≤ R)
    {p a C : ℝ} (hp : 0 < p) (ha : 1 < a)
    (hmom : ∀ y : ℂ, ∀ n m j : ℕ, j < 2 ^ m →
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
                (q.2 s.toNNReal))) - F t| < η :=
  ae_exists_locally_uniform_limit_stopped_domain_clock_of_halfDisc_of_cell_moment hh hγ0
    (by nlinarith) α x hR hDR
    (ae_exists_locally_uniform_limit_nonpositive_halfDiscClock hh x hγ0 hγ2 hα) hp ha hmom

/-- For a positive insertion with `γ α < 2`, `γ ^ 2 < 2` and
`γ ^ 2 / 2 < 2 (2 - γ α) / (2 + γ α)`, the exterior cell moment bound at every start gives
almost sure locally uniform convergence on `[0, ∞)` of the full inserted clocks stopped at
the exit of a domain contained in the disc of radius `R`, to a continuous, nonnegative and
nondecreasing limit. -/
theorem ae_exists_locally_uniform_limit_stopped_domain_clock_of_cell_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hq0 : 0 < γ * α) (hq2 : γ * α < 2) (hγ0 : 0 < γ) (hγ2 : γ ^ 2 < 2)
    (hsub : γ ^ 2 / 2 < 2 * (2 - γ * α) / (2 + γ * α)) (x : ℂ)
    {D : Set ℂ} {R : ℝ} (hR : 0 < R) (hDR : ∀ z ∈ D, ‖z‖ ≤ R)
    {p a C : ℝ} (hp : 0 < p) (ha : 1 < a)
    (hmom : ∀ y : ℂ, ∀ n m j : ℕ, j < 2 ^ m →
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
                (q.2 s.toNNReal))) - F t| < η :=
  ae_exists_locally_uniform_limit_stopped_domain_clock_of_halfDisc_of_cell_moment hh hγ0
    (by nlinarith) α x hR hDR
    (ae_exists_locally_uniform_limit_halfDiscClock hh x hq0 hq2 hγ0 hγ2 hsub) hp ha hmom

end HarmonicBalls
