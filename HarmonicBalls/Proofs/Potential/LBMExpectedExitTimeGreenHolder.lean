import HarmonicBalls.Proofs.Potential.LQGSmoothGreenIntegralConvergence
import HarmonicBalls.Proofs.Potential.LQGClockExitAlmostEveryStartSummability
import HarmonicBalls.Proofs.Potential.LQGClockExitShiftLowerBound
import HarmonicBalls.Proofs.Potential.LQGClockExitDomainComparison
import HarmonicBalls.Proofs.Potential.LQGGreenPotentialHolderInput
import HarmonicBalls.Proofs.Potential.LQGClockExpectationLimit
import HarmonicBalls.Proofs.Sec6.FineSupportDisc
import HarmonicBalls.Proofs.Sec6.GreenIntegrability

/-!
# Expected exit times of Liouville Brownian motion: the Green identity and Hölder continuity

For almost every field, for every smooth bounded domain `O` and every start `x ∈ O`, the expected
exit time of Liouville Brownian motion from `O` is the Green potential of the LQG measure,

  `E_x[τ_O] = ∫_O 2 G_O(x, y) μ_h(dy)`,

for every family of LQG clocks from every start that are almost surely time-change clocks,
under summable half-disc increment bounds uniform over the start (which hold for `α ≤ 0` and for
`0 < γ α`, `γ²/2 < 2 - γ α`). The Green clause of Proposition 2.5 then makes `x ↦ E_x[τ_O]`
Hölder continuous on `O`.

The proof, on one field event:

* (upper bound) by Fatou's lemma `E_x[τ_O]` is at most the limit of the Green integrals of the
  approximating measures, which is `∫ 2 G_O(x, y) μ_h(dy)` for every smooth `O` and every pole
  (`IsWholePlaneGFF.ae_tendsto_green_lintegral_smooth`);
* (discs) for the discs `D_n = B(0, n + 1)` the exit-time increments of the clock approximations
  have finite expected sum from Lebesgue almost every start, and the Markov property at a fixed
  time with the continuity of the Green potential gives the lower bound from every start
  (`le_expectedLBMExitTime_of_ae_lintegral_tsum_ne_top`);
* (every domain) for `O ⊆ D_n`, `E_x[τ_{D_n}] ≤ E_x[τ_O] + (V_{D_n}(x) - V_O(x))`
  (`expectedLBMExitTime_le_add_sub_of_subset`), which with the identity for `D_n` gives the
  lower bound for `O`.

With the time-change property from every start supplied by the positivity of the clock increments
from the origin (`ae_forall_isTimeChangeClock_of_dyadicIncrementLiminf_pos`, `γ² < 2`), this is
the LBM clause of Proposition 2.5 (`GreenPotentialLiouvilleHolderStmt`) for fields with
`Ω : Type`, in the stated range of `α`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology Metric
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- **Green identity for expected exit times of Liouville Brownian motion from every start.**
Under summable half-disc increment bounds uniform over the start, for almost every field, for
every smooth bounded domain `O` and every `x ∈ O`, `E_x[τ_O] = ∫_O G_O(x, y) 2 μ_h(dy)`, for every
family of LQG clocks from every start that are almost surely time-change clocks. -/
theorem ae_forall_expectedLBMExitTime_eq_green_of_halfDisc_increments
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < lqgQ γ) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (cI : ℕ → ℝ≥0∞) (hcI : (∑' k, cI k) ≠ ⊤)
    (hI : ∀ (k : ℕ) (y : ℂ) (ν : ContinuousPath ℂ → Measure ℂ),
      (∀ b, ν b ≤ Measure.map (fun t => b t)
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) →
      (∫⁻ p, ENNReal.ofReal |(∫ z, {z : ℂ | ‖z‖ < 1/2}.indicator (fun z =>
          (dyadicScale (k+2)) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+2)) z)) z
            ∂(ν p.2)) -
        ∫ z, {z : ℂ | ‖z‖ < 1/2}.indicator (fun z =>
          (dyadicScale (k+1)) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+1)) z)) z
            ∂(ν p.2)| ∂(P.prod (planarBrownianMotion y))) ≤ cI k)
    (F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ
      (fieldCircleAverage α (hcirc ω)) x (F ω x))
    (hT : ∀ᵐ ω ∂P, ∀ x : ℂ, ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F ω x b)) :
    ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O → ∀ x ∈ O,
      expectedLBMExitTime (F ω x) O x =
        ENNReal.ofReal (∫ y in O, greenFunction O x y * 2 ∂(μ ω)) := by
  have hlp : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc :=
    (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  let D : ℕ → Set ℂ := fun n => ball (0 : ℂ) ((n : ℝ) + 1)
  have hDs (n : ℕ) : IsSmoothBoundedOpen (D n) :=
    Section6.isSmoothBoundedOpen_disc 0 (by positivity)
  have hsum := ae_all_iff.mpr fun n : ℕ =>
    ae_ae_lintegral_tsum_exit_clockApprox_increment_ne_top_of_halfDisc_increments hlp hγ hγ2
      (D := D n) isOpen_ball isBounded_ball cI hcI hI
  filter_upwards [hh.ae_tendsto_green_lintegral_smooth hγ hγ2 hα hμ, hsum,
    HarmonicBalls.ae_continuous_fieldCircleAverage hlp α, hF, hT,
    greenPotentialHolderStmt γ α hγ hγ2 hα Ω P hC hcirc μ hh hμ] with ω hgreen hsω hcω hFω hTω hHω
  intro O hO x hx
  have hcont (k : ℕ) : Continuous (fieldCircleAverage α (hcirc ω) (dyadicScale k)) :=
    hcω _ (dyadicScale_pos k)
  let V : Set ℂ → ℂ → ℝ≥0∞ := fun U y => ENNReal.ofReal (2 * ∫ z, greenFunction U y z ∂(μ ω))
  -- the upper bound from every start
  have hup (U : Set ℂ) (hU : IsSmoothBoundedOpen U) (y : ℂ) (hy : y ∈ U) :
      expectedLBMExitTime (F ω y) U y ≤ V U y := by
    have h := expectedLBMExitTime_le_liminf_clockApprox_green hU hy hcont (hFω y) (hTω y)
    rwa [(hgreen U hU y).liminf_eq] at h
  -- continuity of the Green potentials
  have hVc (U : Set ℂ) (hU : IsSmoothBoundedOpen U) : ContinuousOn (V U) U := by
    obtain ⟨-, C, r, hr, hHol⟩ := hHω U hU (fun _ => (1 : ℝ)) (memLp_top_const 1)
    have hq : ContinuousOn (fun y => ∫ z in U, greenFunction U y z * 1 ∂(μ ω)) U :=
      (hHol.continuousOn hr).mono subset_closure
    have heq (y : ℂ) : (∫ z in U, greenFunction U y z * 1 ∂(μ ω)) =
        ∫ z, greenFunction U y z ∂(μ ω) := by
      simp only [mul_one]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
        greenFunction_of_notMem_right hz y
    simp only [heq] at hq
    exact ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_const.mul hq)
  -- a disc containing `O`
  obtain ⟨R, hR⟩ := hO.1.subset_ball (0 : ℂ)
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hOD : O ⊆ D n := hR.trans (ball_subset_ball (by linarith))
  have hxD : x ∈ D n := hOD hx
  -- the identity on the disc
  have hDlow : V (D n) x ≤ expectedLBMExitTime (F ω x) (D n) x :=
    le_expectedLBMExitTime_of_ae_lintegral_tsum_ne_top hcont (hDs n) (hsω n) (V := V (D n))
      (fun y _ => hgreen (D n) (hDs n) y) hxD ((hVc (D n) (hDs n)) x hxD) (hFω x) (hTω x)
  have hDeq : expectedLBMExitTime (F ω x) (D n) x = V (D n) x :=
    le_antisymm (hup _ (hDs n) x hxD) hDlow
  -- the comparison of `O` with the disc
  have hcomp := expectedLBMExitTime_le_add_sub_of_subset hcont hO (hDs n) hOD hx (hFω x)
    (hTω x) (hgreen (D n) (hDs n) x) (hgreen O hO x) ENNReal.ofReal_ne_top
  have hVle : V O x ≤ V (D n) x :=
    le_of_tendsto_of_tendsto' (hgreen O hO x) (hgreen (D n) (hDs n) x) fun k =>
      lintegral_mono fun z => by
        gcongr
        exact Section6.greenFunction_le_of_subset hOD isBounded_ball x z
  have hVfin : V (D n) x - V O x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top tsub_le_self
  have hlow : V O x ≤ expectedLBMExitTime (F ω x) O x := by
    rw [hDeq] at hcomp
    have h2 : (V (D n) x - V O x) + V O x ≤
        (V (D n) x - V O x) + expectedLBMExitTime (F ω x) O x := by
      rw [tsub_add_cancel_of_le hVle, add_comm]
      exact hcomp
    exact (ENNReal.add_le_add_iff_left hVfin).mp h2
  rw [le_antisymm (hup O hO x hx) hlow]
  rw [integral_mul_const, mul_comm, setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
    greenFunction_of_notMem_right hz x]

/-- **The LBM clause of Proposition 2.5 under half-disc increment bounds.** Under summable
half-disc increment bounds uniform over the start, for almost every field, for every smooth
bounded domain `O`, the expected exit time of Liouville Brownian motion from `O` is finite from
every start in `O` and Hölder continuous on `O`, for every family of LQG clocks from every start
that are almost surely time-change clocks. -/
theorem ae_expectedLBMExitTime_lt_top_and_holder_of_halfDisc_increments
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < lqgQ γ) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (cI : ℕ → ℝ≥0∞) (hcI : (∑' k, cI k) ≠ ⊤)
    (hI : ∀ (k : ℕ) (y : ℂ) (ν : ContinuousPath ℂ → Measure ℂ),
      (∀ b, ν b ≤ Measure.map (fun t => b t)
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) →
      (∫⁻ p, ENNReal.ofReal |(∫ z, {z : ℂ | ‖z‖ < 1/2}.indicator (fun z =>
          (dyadicScale (k+2)) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+2)) z)) z
            ∂(ν p.2)) -
        ∫ z, {z : ℂ | ‖z‖ < 1/2}.indicator (fun z =>
          (dyadicScale (k+1)) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (k+1)) z)) z
            ∂(ν p.2)| ∂(P.prod (planarBrownianMotion y))) ≤ cI k)
    (F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ
      (fieldCircleAverage α (hcirc ω)) x (F ω x))
    (hT : ∀ᵐ ω ∂P, ∀ x : ℂ, ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F ω x b)) :
    ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O →
      (∀ x ∈ O, expectedLBMExitTime (F ω x) O x < ⊤) ∧
        ∃ C r : ℝ≥0, 0 < r ∧
          HolderOnWith C r (fun x => (expectedLBMExitTime (F ω x) O x).toReal) O := by
  filter_upwards [ae_forall_expectedLBMExitTime_eq_green_of_halfDisc_increments hh hγ hγ2 hα hμ
    cI hcI hI F hF hT, greenPotentialHolderStmt γ α hγ hγ2 hα Ω P hC hcirc μ hh hμ] with ω hid hHω
  intro O hO
  refine ⟨fun x hx => by rw [hid O hO x hx]; exact ENNReal.ofReal_lt_top, ?_⟩
  obtain ⟨-, C, r, hr, hHol⟩ := hHω O hO (fun _ => (2 : ℝ)) (memLp_top_const 2)
  refine ⟨C, r, hr, fun x hx y hy => ?_⟩
  have hnn (z : ℂ) : 0 ≤ ∫ w in O, greenFunction O z w * 2 ∂(μ ω) :=
    integral_nonneg fun w => mul_nonneg (greenFunction_nonneg hO.1 z w) (by norm_num)
  simp only [hid O hO x hx, hid O hO y hy, ENNReal.toReal_ofReal (hnn _)]
  exact hHol x (subset_closure hx) y (subset_closure hy)

/-- **The LBM clause of Proposition 2.5 from the positivity of the clock increments at the
origin.** For `0 < γ`, `γ² < 2`, `α < Q` with `α ≤ 0` or `γ²/2 < 2 - γ α`, if for almost every
field the dyadic lower limits `G_{a,b}` of the clock increments are almost surely positive under
Brownian motion from the origin for all rationals `0 < a < b`, then for almost every field, for
every smooth bounded domain `O`, the expected exit time of Liouville Brownian motion from `O` is
finite from every start in `O` and Hölder continuous on `O`, for every family of LQG clocks from
every start. -/
theorem ae_expectedLBMExitTime_lt_top_and_holder_of_dyadicIncrementLiminf_pos
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2)
    (hα : α < lqgQ γ) (hrange : α ≤ 0 ∨ γ ^ 2 / 2 < 2 - γ * α)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hone : ∀ᵐ ω ∂P, ∀ a b : ℚ, 0 < a → a < b → ∀ᵐ w ∂(planarBrownianMotion 0),
      0 < dyadicIncrementLiminf γ (fieldCircleAverage α (hcirc ω)) a b w)
    (F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ
      (fieldCircleAverage α (hcirc ω)) x (F ω x)) :
    ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O →
      (∀ x ∈ O, expectedLBMExitTime (F ω x) O x < ⊤) ∧
        ∃ C r : ℝ≥0, 0 < r ∧
          HolderOnWith C r (fun x => (expectedLBMExitTime (F ω x) O x).toReal) O := by
  have hlp : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc :=
    (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  have hγ2' : γ < 2 := by nlinarith
  have hT := ae_forall_isTimeChangeClock_of_dyadicIncrementLiminf_pos hlp hγ hγ2 hα F hF hone
  by_cases hα0 : α ≤ 0
  · obtain ⟨cI, hcI, hI⟩ := exists_summable_uniform_inner_suboccupation_increment_bound_of_nonpos
      hlp hα0 hγ hγ2' (δ := 1/2) (by norm_num) le_rfl
    exact ae_expectedLBMExitTime_lt_top_and_holder_of_halfDisc_increments hh hγ hγ2' hα hμ cI hcI
      hI F hF hT
  · have hq0 : 0 < γ * α := mul_pos hγ (not_le.mp hα0)
    obtain ⟨cI, hcI, hI⟩ := exists_summable_uniform_inner_suboccupation_increment_bound hlp hq0 hγ
      (hrange.resolve_left hα0) (δ := 1/2) (by norm_num) le_rfl
    exact ae_expectedLBMExitTime_lt_top_and_holder_of_halfDisc_increments hh hγ hγ2' hα hμ cI hcI
      hI F hF hT

end HarmonicBalls
