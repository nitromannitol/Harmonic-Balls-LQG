import HarmonicBalls.Proofs.Sec6.BrownianHittingTransfer
import HarmonicBalls.Proofs.Sec6.CollarReturnOuterApprox

/-! # Boundary regularity by restarting Brownian motion

Instantaneous exit from the closure at every boundary point transfers to the
first exit from a bounded open domain by the strong Markov property.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess
open scoped ENNReal NNReal Topology

/-- Instantaneous exit from the closure after the first exit implies equality
of the two exit times for a path. -/
theorem exitTime_closure_eq_of_shift_exitTime_eq_zero
    (U : Set ℂ) (ω : ContinuousPath ℂ)
    (hfin : ContinuousPath.exitTime U ω ≠ ∞)
    (hshift : ContinuousPath.exitTime (closure U)
      (ContinuousPath.shift (ContinuousPath.exitTime U ω).toNNReal ω) = 0) :
    ContinuousPath.exitTime (closure U) ω = ContinuousPath.exitTime U ω := by
  apply le_antisymm _ (ContinuousPath.exitTime_mono subset_closure ω)
  by_contra h
  have ht : ((ContinuousPath.exitTime U ω).toNNReal : ℝ≥0∞) <
      ContinuousPath.exitTime (closure U) ω := by
    rw [ENNReal.coe_toNNReal hfin]
    exact lt_of_not_ge h
  have heq := ContinuousPath.exitTime_shift_add (closure U) ω
    (ContinuousPath.exitTime U ω).toNNReal ht
  rw [hshift, zero_add, ENNReal.coe_toNNReal hfin] at heq
  exact (ne_of_lt ht) (by simpa only [ENNReal.coe_toNNReal hfin] using heq)

/-- Instantaneous exit from a closed subset of the plane is measurable. -/
theorem measurableSet_exitTime_closed_eq_zero (F : Set ℂ) (hF : IsClosed F) :
    MeasurableSet {ω : ContinuousPath ℂ | ContinuousPath.exitTime F ω = 0} := by
  let : LocallyCompactSpace (Fᶜ : Set ℂ) := hF.isOpen_compl.locallyCompactSpace
  have hσ : IsSigmaCompact Fᶜ := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  obtain ⟨K, hK, hcover⟩ := hσ
  have heq : (⋃ n, K n)ᶜ = F := by rw [hcover, compl_compl]
  have hm := measurable_exitTime_compl_iUnion_compact K hK
  rw [heq] at hm
  exact measurableSet_eq_fun hm measurable_const

/-- The strong Markov property transfers instantaneous exit at all boundary
points to equality of exit times from a bounded open domain and its closure.
The instantaneous-exit event is measurable. -/
theorem ae_exitTime_closure_eq_of_boundary_instant_exit
    {U : Set ℂ} (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    {x : ℂ} (hx : x ∈ U)
    (hregular : ∀ y ∈ frontier U, ∀ᵐ ω ∂planarBrownianMotion y,
      ContinuousPath.exitTime (closure U) ω = 0) :
    ∀ᵐ ω ∂planarBrownianMotion x,
      ContinuousPath.exitTime (closure U) ω = ContinuousPath.exitTime U ω := by
  let E : Set (ContinuousPath ℂ) := {ω | ContinuousPath.exitTime (closure U) ω = 0}
  have hE : MeasurableSet E := measurableSet_exitTime_closed_eq_zero _ isClosed_closure
  let τ : ContinuousPath ℂ → ℝ≥0∞ := ContinuousPath.exitTime U
  have hτ := ContinuousPath.isStoppingTime_exitTime U hU
  have hfin : ∀ᵐ ω ∂planarBrownianMotion x, τ ω < ⊤ :=
    ae_planarBrownian_exitTime_bounded_lt_top x hbounded
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
  have hfront : ∀ᵐ ω ∂planarBrownianMotion x,
      ω ((τ ω).untopD 0) ∈ frontier U := by
    filter_upwards [hfin, ae_planarBrownianMotion_eval_zero x] with ω hf h0
    simpa [τ] using ContinuousPath.coordinate_exitTime_mem_frontier U hU ω (h0 ▸ hx) (ne_of_lt hf)
  have hone : planarBrownianMotion x ((fun ω => ContinuousPath.shift ((τ ω).untopD 0) ω) ⁻¹' E) = 1 := by
    rw [happ]
    have hae : ∀ᵐ ω ∂planarBrownianMotion x,
        planarBrownianMotion (ω ((τ ω).untopD 0)) E = 1 := by
      filter_upwards [hfront] with ω hω
      exact (MeasureTheory.mem_ae_iff_prob_eq_one hE).mp (hregular _ hω)
    simpa using lintegral_congr_ae hae
  have hshift : ∀ᵐ ω ∂planarBrownianMotion x,
      ContinuousPath.exitTime (closure U) (ContinuousPath.shift ((τ ω).untopD 0) ω) = 0 :=
    (MeasureTheory.mem_ae_iff_prob_eq_one
      (hE.preimage (ContinuousPath.measurable_shift_untopD_stoppingTime τ hτ))).mpr hone
  filter_upwards [hfin, hshift] with ω hf hs
  apply exitTime_closure_eq_of_shift_exitTime_eq_zero U ω (ne_of_lt hf)
  simpa [τ] using hs

end HarmonicBalls.Section6
