import HarmonicBalls.Proofs.Sec6.HarmonicCompactExtension
import HarmonicBalls.Proofs.Sec6.PlanarBrownianGenerator

/-! # Brownian exit representation for bounded harmonic functions

A bounded continuous function harmonic on a bounded open domain is represented
by its values at the Brownian exit point. The proof uses compact-local smooth
extensions and the planar Brownian generator.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric InnerProductSpace
open scoped NNReal ENNReal Topology ZeroAtInfty

/-- A bounded continuous harmonic function is dominated by its Brownian exit
expectation. -/
theorem harmonic_le_integral_planarBrownian_exitTime
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    {q : ℂ → ℝ} (hq : Continuous q) (hharm : HarmonicOnNhd q D)
    {M : ℝ} (hM : ∀ y, ‖q y‖ ≤ M) {x : ℂ} (hx : x ∈ D) :
    q x ≤ ∫ ω : ContinuousPath ℂ,
      q (ω ((ContinuousPath.exitTime D ω).toNNReal)) ∂(planarBrownianMotion x) := by
  obtain ⟨U, hopen, hmono, hcompact, hnext, hunion⟩ :=
    exists_relativelyCompact_open_exhaustion hD
  have hbounded : Bornology.IsBounded (⋃ n, U n) := by rw [hunion]; exact hDb
  have hx' : x ∈ ⋃ n, U n := by rw [hunion]; exact hx
  have h := le_integral_exitTime_of_local_generator_approximation
    hopen hmono hbounded hq hM hx' (by
      intro n ε hε
      have hsub : closure (U n) ⊆ D := by
        rw [← hunion]
        exact (hnext n).trans (subset_iUnion U (n + 1))
      obtain ⟨f, hf, hfgen⟩ := compact_generator_extensions_of_harmonic hD hharm
        exists_planarBrownian_generator_eq_zero_of_harmonic (closure (U n)) (hcompact n) hsub
      refine ⟨f, ?_, ?_⟩
      · intro z hz
        rw [hf z hz, sub_self, abs_zero]
        exact hε.le
      · intro z hz
        exact hfgen z (subset_closure hz))
  simpa only [hunion] using h

/-- A bounded continuous function harmonic on a bounded open set equals its
expected value at the Brownian exit point. -/
theorem harmonic_eq_integral_planarBrownian_exitTime
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    {q : ℂ → ℝ} (hq : Continuous q) (hharm : HarmonicOnNhd q D)
    {M : ℝ} (hM : ∀ y, ‖q y‖ ≤ M) {x : ℂ} (hx : x ∈ D) :
    q x = ∫ ω : ContinuousPath ℂ,
      q (ω ((ContinuousPath.exitTime D ω).toNNReal)) ∂(planarBrownianMotion x) := by
  apply le_antisymm (harmonic_le_integral_planarBrownian_exitTime hD hDb hq hharm hM hx)
  have hn := harmonic_le_integral_planarBrownian_exitTime hD hDb hq.neg hharm.neg
    (fun y => by simpa only [Pi.neg_apply, norm_neg] using hM y) hx
  simpa only [Pi.neg_apply, integral_neg, neg_neg] using (neg_le_neg hn)

end HarmonicBalls.Section6
