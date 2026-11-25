import HarmonicBalls.Proofs.Potential.LQGClockInsertedEveryStart
import HarmonicBalls.Proofs.Potential.LBMClauseSubcritical
import HarmonicBalls.Proofs.Potential.LBMExpectedExitTimeGreenHolder

/-!
# The Liouville clock from every start on one field event

For every `0 < γ < 2` and every insertion `α < Q`, there is a family `F` of clocks of planar
Brownian motion such that, on one event of full probability for the field, for every start `x`:

* `F ω x` is an LQG clock of the inserted field from `x` (the limit in probability, uniformly on
  compact time intervals, of the circle-average approximations; `exists_ae_forall_isLQGClock`);
* almost surely under the Brownian law from `x`, `F ω x` is a time-change clock: it vanishes at
  time zero, is continuous and strictly increasing, and tends to infinity
  (`ae_forall_isTimeChangeClock_of_isLQGClock_of_lt_two`);
* its speed measure is `μ_h`: for every smooth bounded open `O ∋ x`, the expected exit time of
  Liouville Brownian motion from `O` is `∫_O G_O(x, y) 2 μ_h(dy)`
  (`ae_forall_expectedLBMExitTime_eq_green`).

This is the statement of Garban–Rhodes–Vargas, *Liouville Brownian motion*, Ann. Probab. 44 (2016),
Theorem 2.7, and of Andres–Kajino, Probab. Theory Related Fields 166
(2016), Theorem 2.2 (one field event for all starting points), for every `0 < γ < 2` and with the
insertion, here with the HB clock defined as a limit of the
circle-average approximations instead of the Garban–Rhodes–Vargas construction from the massive
field; the null event of the field is common to all starts.
-/

namespace HarmonicBalls

open MeasureTheory MarkovProcess
open scoped ENNReal NNReal

/-- **The Liouville clock from every start on one field event**: for `0 < γ < 2` and `α < Q` there
is a family of clocks which, for almost every field, is from every start an LQG clock of the
inserted field and almost surely a strictly increasing continuous clock from zero to infinity, with
`E_x[τ_O] = ∫_O G_O(x, y) 2 μ_h(dy)` for every smooth bounded open `O ∋ x`. -/
theorem exists_ae_forall_isLQGClock_isTimeChangeClock {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∃ F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ, ∀ᵐ ω ∂P,
      (∀ x : ℂ, IsLQGClock planarBrownianMotion γ (fieldCircleAverage α (hcirc ω)) x (F ω x) ∧
        ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F ω x b)) ∧
      ∀ O : Set ℂ, IsSmoothBoundedOpen O → ∀ x ∈ O,
        expectedLBMExitTime (F ω x) O x =
          ENNReal.ofReal (∫ y in O, greenFunction O x y * 2 ∂(μ ω)) := by
  obtain ⟨F, hF⟩ := exists_ae_forall_isLQGClock hh hγ hγ2 hα
  have hT := ae_forall_isTimeChangeClock_of_isLQGClock_of_lt_two
    ((LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh) hγ hγ2 hα F hF
  refine ⟨F, ?_⟩
  filter_upwards [hF, hT, ae_forall_expectedLBMExitTime_eq_green hh hγ hγ2 hα hμ F hF hT]
    with ω hFω hTω hGω
  exact ⟨fun x => ⟨hFω x, hTω x⟩, hGω⟩

end HarmonicBalls
