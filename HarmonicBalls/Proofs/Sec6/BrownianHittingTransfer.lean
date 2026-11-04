import HarmonicBalls.Proofs.Sec6.BrownianUnitIncrements
import HarmonicBalls.Proofs.Sec6.ShrinkingBrownianExit
import HarmonicBalls.Proofs.Sec6.GreenPotentialStoppedReduction
import HarmonicBalls.Proofs.Sec6.LQGFineSupportReduction
import HarmonicBalls.Proofs.Brownian.PlanarHeatFeller
import HarmonicBalls.Proofs.Brownian.PlanarBrownianMotion
import MarkovProcess.Trajectory.StoppingLtTop

/-! # Transfer of Brownian hitting bounds from a circle

A path shifted before leaving a domain can only lose information about an
obstacle hit before the shift. Thus a hit after the shift implies a hit before
exit for the original path.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal

/-- A hit before exit after a shift remains a hit before exit for the original
path, provided the shift occurs before exit. -/
theorem exitTime_le_of_shift_exitTime_le {U E : Set ℂ} (ω : ContinuousPath ℂ)
    (t : ℝ≥0) (ht : (t : ℝ≥0∞) < ContinuousPath.exitTime U ω)
    (h : ContinuousPath.exitTime E (ContinuousPath.shift t ω) ≤
      ContinuousPath.exitTime U (ContinuousPath.shift t ω)) :
    ContinuousPath.exitTime E ω ≤ ContinuousPath.exitTime U ω := by
  by_cases he : ContinuousPath.exitTime E ω ≤ (t : ℝ≥0∞)
  · exact he.trans ht.le
  · have he' : (t : ℝ≥0∞) < ContinuousPath.exitTime E ω := lt_of_not_ge he
    rw [← ContinuousPath.exitTime_shift_add E ω t he',
      ← ContinuousPath.exitTime_shift_add U ω t ht]
    exact add_le_add h le_rfl

/-- A uniform lower bound from an inner circle transfers to its centre by the
strong Markov property. -/
theorem planarBrownian_hitting_probability_ge_of_circle
    {x : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (K : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n)) (c : ℝ≥0∞)
    (hc : ∀ y ∈ sphere x r, c ≤ planarBrownianMotion y
      {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω ≤
        ContinuousPath.exitTime (ball x R) ω}) :
    c ≤ planarBrownianMotion x
      {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω ≤
        ContinuousPath.exitTime (ball x R) ω} := by
  let U := ball x R
  let E : Set (ContinuousPath ℂ) := {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω ≤
    ContinuousPath.exitTime U ω}
  let τ : ContinuousPath ℂ → ℝ≥0∞ := ContinuousPath.exitTime (ball x r)
  have hτ := ContinuousPath.isStoppingTime_exitTime (ball x r) isOpen_ball
  have hE : MeasurableSet E := measurableSet_le
    (measurable_exitTime_compl_iUnion_compact K hK)
    (ContinuousPath.measurable_exitTime U isOpen_ball)
  have hshift := ContinuousPath.measurable_shift_untopD_stoppingTime τ hτ
  have hfin : ∀ᵐ ω ∂(planarBrownianMotion x), τ ω < ⊤ :=
    ae_planarBrownianMotion_exitTime_ball_lt_top x r
  have hcross := ae_planarBrownian_ball_crossing_unconditional (x := x) hr hrR
  have hrestart :=
    SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_restrict_map_shift_stoppingTime_lt_top
      planarHeatSemigroup isConservative_planarHeatSemigroup
      isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup
      x τ hτ univ (by simp)
  rw [← planarBrownianMotion_eq_continuousProcess] at hrestart
  simp only [univ_inter] at hrestart
  have hre : (planarBrownianMotion x).restrict {ω | (τ ω : WithTop ℝ≥0) < ⊤} = planarBrownianMotion x :=
    Measure.restrict_eq_self_of_ae_mem hfin
  change ((planarBrownianMotion x).restrict {ω | τ ω < ⊤}).map
      (fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) =
    Kernel.comap planarBrownianMotion (fun ω => ω ((τ ω).untopD 0))
      (ContinuousPath.measurable_eval_untopD_stoppingTime τ hτ) ∘ₘ
        ((planarBrownianMotion x).restrict {ω | τ ω < ⊤}) at hrestart
  rw [hre] at hrestart
  have happ := congrArg (fun m : Measure (ContinuousPath ℂ) => m E) hrestart
  rw [Measure.map_apply hshift hE,
    Measure.bind_apply hE (Kernel.aemeasurable _)] at happ
  simp only [Kernel.comap_apply] at happ
  have hbound : c ≤ ∫⁻ ω, planarBrownianMotion (ω ((τ ω).untopD 0)) E
      ∂(planarBrownianMotion x) := by
    have hae : ∀ᵐ ω ∂(planarBrownianMotion x),
        c ≤ planarBrownianMotion (ω ((τ ω).untopD 0)) E := by
      filter_upwards [hfin, hcross] with ω hf ⟨ht, hs⟩
      have ht' : (τ ω).untopD 0 = (ContinuousPath.exitTime (ball x r) ω).toNNReal := by
        simp [τ]
      rw [ht']
      exact hc _ hs
    simpa using lintegral_mono_ae hae
  rw [← happ] at hbound
  apply hbound.trans
  apply measure_mono_ae
  filter_upwards [hfin, hcross] with ω hf ⟨ht, hs⟩ hω
  apply exitTime_le_of_shift_exitTime_le ω ((τ ω).untopD 0) ?_ hω
  simpa [τ, ENNReal.coe_toNNReal (ne_of_lt hf)] using ht


universe u

/-- A stopped Green-potential representation yields the fine-support hitting
bound at the centre. The strong Markov property supplies the passage from the
circle to the centre. -/
theorem ae_lqg_fineSupport_hitting_bound_of_stopped_representation
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hnonatom : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hrep : ∀ᵐ sample ∂P, ∀ c : ℂ, ∀ r : ℝ, 0 < r →
      ∀ L : Set ℂ, IsCompact L → L ⊆ fineSupportAnnulus c r →
      ∀ x ∈ sphere c (r / 4), x ∉ L →
      ENNReal.ofReal (∫ y in L, greenFunction (fineSupportAnnulus c r) x y ∂(μ sample)) ≤ ∫⁻ ω,
        ENNReal.ofReal (∫ y in L, greenFunction (fineSupportAnnulus c r)
          (ω ((ContinuousPath.exitTime (fineSupportAnnulus c r \ L) ω).toNNReal)) y ∂(μ sample))
            ∂(planarBrownianMotion x)) :
    ∀ᵐ sample ∂P, ∀ x : ℂ, ∀ ε : ℝ, 0 < ε →
      ∀ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) → Monotone K →
      (μ sample) (ball x ε \ ⋃ n, K n) = 0 →
      ∀ᶠ n in atTop,
        ENNReal.ofReal (greenPotentialExtremaRatio (fineSupportAnnulus x (fineSupportScale n))
          (sphere x (fineSupportScale n / 4)) (μ sample)) ≤ planarBrownianMotion x
        {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω ≤
          ContinuousPath.exitTime (ball x (fineSupportScale n)) ω} := by
  filter_upwards [ae_fineSupport_circle_hitting_union_of_stopped_representation
    hholder hfull hgrowth hγ hγ2 hα hGFF hμ hnonatom hrep] with sample hcircle
  intro x ε hε K hK hmono hmass
  filter_upwards [tendsto_fineSupportScale_zero.eventually (eventually_lt_nhds hε)] with n hn
  have hr : 0 < fineSupportScale n := by unfold fineSupportScale; positivity
  apply planarBrownian_hitting_probability_ge_of_circle (show 0 < fineSupportScale n / 4 by positivity)
    (show fineSupportScale n / 4 < fineSupportScale n by linarith) K hK
  exact hcircle x (fineSupportScale n) ε hr hn.le K hK hmono hmass

end HarmonicBalls.Section6
