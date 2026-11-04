import HarmonicBalls.Proofs.Sec6.StoppedPotentialIntegrability
import Mathlib.Probability.Martingale.Basic

/-!
# Stopped submartingales and exit expectations

A bounded potential whose stopped process is a submartingale satisfies the
exit expectation inequality needed for the Green-potential hitting estimate.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology

/-- A bounded measurable function whose truncated exit values form a
submartingale is bounded above by its expectation at the full exit time. -/
theorem le_integral_exitTime_of_submartingale
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    {q : ℂ → ℝ} (hq : Measurable q) {M : ℝ} (hM : ∀ y, ‖q y‖ ≤ M)
    (x : ℂ) (ℱ : Filtration ℕ (inferInstance : MeasurableSpace (ContinuousPath ℂ)))
    (hsub : Submartingale (fun (n : ℕ) (ω : ContinuousPath ℂ) =>
      q (ω (ContinuousPath.exitTimeTrunc D n ω))) ℱ (planarBrownianMotion x)) :
    q x ≤ ∫ ω : ContinuousPath ℂ,
      q (ω ((ContinuousPath.exitTime D ω).toNNReal)) ∂(planarBrownianMotion x) := by
  apply integral_exitTime_lower_of_truncations hD hDb hq hM x
  intro n
  have hzero : (∫ ω : ContinuousPath ℂ,
      q (ω (ContinuousPath.exitTimeTrunc D (0 : ℕ) ω)) ∂(planarBrownianMotion x)) = q x := by
    have hae : (fun ω : ContinuousPath ℂ => q (ω (ContinuousPath.exitTimeTrunc D (0 : ℕ) ω)))
        =ᵐ[planarBrownianMotion x] fun _ => q x := by
      filter_upwards [ae_planarBrownianMotion_eval_zero x] with ω hω
      have ht : ContinuousPath.exitTimeTrunc D (0 : ℕ) ω = 0 :=
        le_antisymm (by simpa only [Nat.cast_zero] using
          ContinuousPath.exitTimeTrunc_le D (0 : ℕ) ω) bot_le
      rw [ht, hω]
    rw [integral_congr_ae hae, integral_const]
    simp
  rw [← hzero]
  calc
    _ ≤ ∫ ω, (planarBrownianMotion x)[(fun ω =>
        q (ω (ContinuousPath.exitTimeTrunc D n ω))) | ℱ 0] ω ∂(planarBrownianMotion x) :=
      integral_mono_ae (hsub.integrable 0) integrable_condExp (hsub.ae_le_condExp (Nat.zero_le n))
    _ = _ := integral_condExp (ℱ.le 0)

/-- Compact support and continuity on the closure provide the boundedness and
measurability required for the stopped-submartingale argument. -/
theorem le_integral_exitTime_of_submartingale_of_continuousOn
    {U D : Set ℂ} (hUb : Bornology.IsBounded U) (hD : IsOpen D)
    (hDU : D ⊆ U) {q : ℂ → ℝ} (hcont : ContinuousOn q (closure U))
    (hzero : ∀ y ∉ closure U, q y = 0)
    (x : ℂ) (ℱ : Filtration ℕ (inferInstance : MeasurableSpace (ContinuousPath ℂ)))
    (hsub : Submartingale (fun (n : ℕ) (ω : ContinuousPath ℂ) =>
      q (ω (ContinuousPath.exitTimeTrunc D n ω))) ℱ (planarBrownianMotion x)) :
    q x ≤ ∫ ω : ContinuousPath ℂ,
      q (ω ((ContinuousPath.exitTime D ω).toNNReal)) ∂(planarBrownianMotion x) := by
  obtain ⟨M, hM⟩ := (hUb.isCompact_closure).exists_bound_of_continuousOn hcont
  apply le_integral_exitTime_of_submartingale hD (hUb.subset hDU)
    (measurable_of_continuousOn_closure_of_zero hcont hzero) (M := max M 0) ?_ x ℱ hsub
  intro y
  by_cases hy : y ∈ closure U
  · exact (hM y hy).trans (le_max_left _ _)
  · rw [hzero y hy, norm_zero]
    exact le_max_right _ _

/-- The compact-union hitting estimate follows when every restricted Green
potential stopped on leaving the punctured domain is a submartingale. -/
theorem greenPotentialExtremaRatio_hitting_union_of_submartingale
    {μ : Measure ℂ} {U S : Set ℂ} {K : ℕ → Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hS : IsCompact S) (hSU : S ⊆ closure U)
    (hK : ∀ n, IsCompact (K n)) (hKmono : Monotone K)
    (hfull : μ (U \ ⋃ n, K n) = 0)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure U)) →
      (∀ x ∈ closure U, IntegrableOn (fun y => greenFunction U x y * f y) U μ) ∧
      ∃ C t : ℝ≥0, 0 < t ∧
        HolderOnWith C t (fun x => ∫ y in U, greenFunction U x y * f y ∂μ) (closure U))
    (hpos : 0 < greenPotentialExtremaRatio U S μ)
    (hsub : ∀ L : Set ℂ, IsCompact L → L ⊆ U → ∀ x ∈ S, x ∉ L →
      ∃ ℱ : Filtration ℕ (inferInstance : MeasurableSpace (ContinuousPath ℂ)),
        Submartingale (fun (n : ℕ) (ω : ContinuousPath ℂ) =>
          ∫ y in L, greenFunction U (ω (ContinuousPath.exitTimeTrunc (U \ L) n ω)) y ∂μ)
          ℱ (planarBrownianMotion x)) :
    ∀ x ∈ S, ENNReal.ofReal (greenPotentialExtremaRatio U S μ) ≤
      planarBrownianMotion x {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω ≤
        ContinuousPath.exitTime U ω} := by
  apply greenPotentialExtremaRatio_hitting_union_of_real_stopped_representation
    hU hUb hS hSU hK hKmono hfull hholder hpos
  intro L hL hLU x hx hxL
  obtain ⟨ℱ, hmart⟩ := hsub L hL hLU x hx hxL
  obtain ⟨_, C, t, ht, hcont⟩ := hholder (L.indicator (fun _ => 1))
    ((memLp_top_const (1 : ℝ)).indicator hL.measurableSet)
  have heq : (fun z => ∫ y in U, greenFunction U z y * L.indicator (fun _ => 1) y ∂μ) =
      (fun z => ∫ y in L, greenFunction U z y ∂μ) := by
    funext z
    have hind : (fun y => greenFunction U z y * L.indicator (fun _ => 1) y) =
        L.indicator (greenFunction U z) := by
      funext y
      by_cases hy : y ∈ L <;> simp [hy]
    rw [hind, integral_indicator hL.measurableSet, Measure.restrict_restrict_of_subset hLU]
  rw [heq] at hcont
  apply le_integral_exitTime_of_submartingale_of_continuousOn hUb
    (hU.sdiff hL.isClosed) sdiff_subset (hcont.continuousOn ht) ?_ x ℱ hmart
  intro z hz
  have hzU : z ∉ U := fun hzU => hz (subset_closure hzU)
  simp only [greenFunction_of_notMem_left hzU, integral_zero]

end HarmonicBalls.Section6
