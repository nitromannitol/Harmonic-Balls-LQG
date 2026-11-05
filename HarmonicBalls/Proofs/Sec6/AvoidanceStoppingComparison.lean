import HarmonicBalls.Proofs.Sec6.AvoidanceDiscRestart

/-! # Avoidance comparison at an interior stopping surface -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology

/-- A bounded-domain exit restarts a measurable avoidance event. If the exit position is
in `C` whenever it precedes the exit from `U`, then the probability from the
starting point is controlled by the uniform bound on `C` and twice the
probability that the outer exit occurs first. -/
theorem planarBrownian_avoidance_le_of_stopping_surface
    {U D Y C : Set ℂ} (hU : IsOpen U) (hD : IsOpen D)
    (hDb : Bornology.IsBounded D)
    (hE : MeasurableSet {p : ContinuousPath ℂ |
      ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Y p}) (x : ℂ) (c : ℝ≥0∞)
    (hpos : ∀ ω : ContinuousPath ℂ, ω 0 = x → ContinuousPath.exitTime D ω ≠ ∞ →
      ContinuousPath.exitTime D ω < ContinuousPath.exitTime U ω →
      ω ((ContinuousPath.exitTime D ω).toNNReal) ∈ C)
    (hbound : ∀ y ∈ C, planarBrownianMotion y
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Y p} ≤ c) :
    planarBrownianMotion x {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime Y ω} ≤
      c + 2 * planarBrownianMotion x
        {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime D ω} := by
  let E : Set (ContinuousPath ℂ) := {ω | ContinuousPath.exitTime U ω ≤
    ContinuousPath.exitTime Y ω}
  let B : Set (ContinuousPath ℂ) := {ω | ContinuousPath.exitTime U ω ≤
    ContinuousPath.exitTime D ω}
  let τ : ContinuousPath ℂ → ℝ≥0∞ := ContinuousPath.exitTime D
  have hτ := ContinuousPath.isStoppingTime_exitTime D hD
  have hB : MeasurableSet B := measurableSet_le
    (ContinuousPath.measurable_exitTime U hU) (ContinuousPath.measurable_exitTime D hD)
  have hfin : ∀ᵐ ω ∂planarBrownianMotion x, τ ω < ⊤ :=
    ae_planarBrownian_exitTime_bounded_lt_top x hDb
  have hrestart :=
    SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime_lt_top
      planarHeatSemigroup isConservative_planarHeatSemigroup
      isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup
      x τ hτ univ (by simp)
  rw [← planarBrownianMotion_eq_continuousProcess] at hrestart
  simp only [univ_inter] at hrestart
  have hre : (planarBrownianMotion x).restrict {ω | (τ ω : WithTop ℝ≥0) < ⊤} =
      planarBrownianMotion x := Measure.restrict_eq_self_of_ae_mem hfin
  change ((planarBrownianMotion x).restrict {ω | τ ω < ⊤}).map
      (fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) =
    Kernel.comap planarBrownianMotion (fun ω => ω ((τ ω).untopD 0))
      (ContinuousPath.measurable_eval_untopD_stoppingTime τ hτ) ∘ₘ
        ((planarBrownianMotion x).restrict {ω | τ ω < ⊤}) at hrestart
  rw [hre] at hrestart
  have happ := congrArg (fun m : Measure (ContinuousPath ℂ) => m E) hrestart
  rw [Measure.map_apply (ContinuousPath.measurable_shift_untopD_stoppingTime τ hτ) hE,
    Measure.bind_apply hE (Kernel.aemeasurable _)] at happ
  simp only [Kernel.comap_apply] at happ
  have hpoint : ∀ᵐ ω ∂planarBrownianMotion x,
      planarBrownianMotion (ω ((τ ω).untopD 0)) E ≤ c + B.indicator (fun _ => 1) ω := by
    filter_upwards [hfin, ae_planarBrownianMotion_eval_zero x] with ω hf h0
    by_cases hb : ω ∈ B
    · simp only [Set.indicator_of_mem hb]
      have hp : planarBrownianMotion (ω ((τ ω).untopD 0)) E ≤ 1 := by simpa using (measure_mono (subset_univ E) :
        planarBrownianMotion (ω ((τ ω).untopD 0)) E ≤ planarBrownianMotion (ω ((τ ω).untopD 0)) univ)
      exact hp.trans (le_add_left le_rfl)
    · have ht : τ ω < ContinuousPath.exitTime U ω := lt_of_not_ge hb
      have hc := hpos ω h0 (ne_of_lt hf) ht
      have hh := hbound _ hc
      simpa [Set.indicator_of_notMem hb, τ, E] using hh
  have hint : (∫⁻ ω, planarBrownianMotion (ω ((τ ω).untopD 0)) E
      ∂planarBrownianMotion x) ≤ c + planarBrownianMotion x B := by
    calc
      _ ≤ ∫⁻ ω, (c + B.indicator (fun _ => 1) ω) ∂planarBrownianMotion x :=
        lintegral_mono_ae hpoint
      _ = c + planarBrownianMotion x B := by
        rw [lintegral_add_left measurable_const, lintegral_const]
        have hi : (∫⁻ ω, B.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂planarBrownianMotion x) =
            planarBrownianMotion x B := by
          change (∫⁻ ω, B.indicator (1 : ContinuousPath ℂ → ℝ≥0∞) ω ∂planarBrownianMotion x) = _
          exact lintegral_indicator_one hB
        rw [hi]
        simp
  have hsplit : planarBrownianMotion x E ≤
      planarBrownianMotion x ((fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) ⁻¹' E) +
        planarBrownianMotion x B := by
    calc
      _ ≤ planarBrownianMotion x (((fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) ⁻¹' E) ∪ B) := by
        apply measure_mono_ae
        filter_upwards [hfin] with ω hf hω
        by_cases hb : ω ∈ B
        · exact Or.inr hb
        · left
          have ht : τ ω < ContinuousPath.exitTime U ω := lt_of_not_ge hb
          have ht' : ((τ ω).toNNReal : ℝ≥0∞) < ContinuousPath.exitTime U ω := by
            rw [ENNReal.coe_toNNReal (ne_of_lt hf)]
            exact ht
          simpa [τ, E] using
            (avoidance_after_shift (U := U) (K := Yᶜ) ω (τ ω).toNNReal ht' (by simpa [E] using hω))
      _ ≤ _ := measure_union_le _ _
  rw [happ] at hsplit
  calc
    _ ≤ (c + planarBrownianMotion x B) + planarBrownianMotion x B :=
      hsplit.trans (add_le_add hint le_rfl)
    _ = c + 2 * planarBrownianMotion x B := by simp [two_mul, add_assoc]

/-- Restarting upon first hitting an interior circle bounds a measurable avoidance event
by the uniform circle bound plus the probability of exiting the domain first.
The starting point is assumed to lie off the circle. -/
theorem planarBrownian_avoidance_le_of_circle_hitting
    {U Y : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hE : MeasurableSet {p : ContinuousPath ℂ |
      ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Y p}) {z x : ℂ} {ρ : ℝ} (hx : x ∈ U \ sphere z ρ)
    (c : ℝ≥0∞) (hbound : ∀ y ∈ sphere z ρ, planarBrownianMotion y
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Y p} ≤ c) :
    planarBrownianMotion x {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime Y ω} ≤
      c + 2 * planarBrownianMotion x
        {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime (U \ sphere z ρ) ω} := by
  let D := U \ sphere z ρ
  have hD : IsOpen D := hU.sdiff isClosed_sphere
  have hDb : Bornology.IsBounded D := hUb.subset sdiff_subset
  apply planarBrownian_avoidance_le_of_stopping_surface hU hD hDb
    hE x c ?_ hbound
  intro ω h0 hfin ht
  have hfront : ω ((ContinuousPath.exitTime D ω).toNNReal) ∈ frontier D :=
    ContinuousPath.coordinate_exitTime_mem_frontier D hD ω (h0 ▸ hx) hfin
  have hinside : ω ((ContinuousPath.exitTime D ω).toNNReal) ∈ U := by
    apply ContinuousPath.mem_of_lt_exitTime
    simpa [ENNReal.coe_toNNReal hfin] using ht
  have houtside : ω ((ContinuousPath.exitTime D ω).toNNReal) ∉ D := by
    rw [hD.frontier_eq] at hfront
    exact hfront.2
  by_contra hnot
  exact houtside ⟨hinside, hnot⟩

end HarmonicBalls.Section6
