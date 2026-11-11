import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.UniversalRealization

/-! # Route (A) codes of the canonical circle-average profile: measurability

The
reconstruction `R` of the whole-plane field from its positive-radius circle averages `c` is built from the countable
family of limits `lim_n ∫ c(2^{-n}, z) ψ(z) d²z` against test functions `ψ` (the codes). This file proves that the
codes are Borel functions of the canonical profile `c ∈ CanonicalProfile`; the convergence locus is Borel and the
limit is zero off it, as in the paper ("the convergence locus and the limit map are Borel").
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set

noncomputable section

/-- The integral `∫ c(2^{-n}, z) ψ(z) d²z` of the canonical profile at radius `2^{-n}` against `ψ`. -/
def circleTestIntegral (ψ : ℂ → ℝ) (n : ℕ) (c : CanonicalProfile) : ℝ :=
  ∫ z, c.1 ((1 / 2 : ℝ) ^ n, z) * ψ z

open scoped Classical in
/-- The code `lim_n ∫ c(2^{-n}, z) ψ(z) d²z` where the limit exists, and `0` where it does not. -/
def circleTestLimit (ψ : ℂ → ℝ) (c : CanonicalProfile) : ℝ :=
  if ∃ l : ℝ, Tendsto (fun n => circleTestIntegral ψ n c) atTop (𝓝 l) then
    limUnder atTop (fun n => circleTestIntegral ψ n c) else 0

/-- Measurability of the integral at a fixed radius `2^{-n}`: the integrand is continuous in `z` and measurable
in `c` for each `z`, hence jointly measurable (`measurable_uncurry_of_continuous_of_measurable`). -/
theorem measurable_circleTestIntegral {ψ : ℂ → ℝ} (hψ : Continuous ψ) (n : ℕ) :
    Measurable (circleTestIntegral ψ n) := by
  have hr : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hu : Measurable (Function.uncurry fun (z : ℂ) (c : CanonicalProfile) => c.1 ((1 / 2 : ℝ) ^ n, z) * ψ z) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun c => ?_) (fun z => ?_)
    · have hc : Continuous (fun z : ℂ => c.1 ((1 / 2 : ℝ) ^ n, z)) :=
        c.2.comp_continuous (continuous_const.prodMk continuous_id) fun z => ⟨hr, mem_univ z⟩
      exact hc.mul hψ
    · exact ((measurable_pi_apply ((1 / 2 : ℝ) ^ n, z)).comp measurable_subtype_coe).mul measurable_const
  have hf : Measurable (Function.uncurry fun (c : CanonicalProfile) (z : ℂ) =>
      c.1 ((1 / 2 : ℝ) ^ n, z) * ψ z) := hu.comp measurable_swap
  exact (StronglyMeasurable.integral_prod_right (ν := volume) hf.stronglyMeasurable).measurable

/-- The set of canonical profiles at which the codes against `ψ` converge is Borel. -/
theorem measurableSet_circleTestConverges {ψ : ℂ → ℝ} (hψ : Continuous ψ) :
    MeasurableSet {c : CanonicalProfile | ∃ l : ℝ, Tendsto (fun n => circleTestIntegral ψ n c) atTop (𝓝 l)} :=
  measurableSet_exists_tendsto fun n => measurable_circleTestIntegral hψ n

/-- **Borel measurability of the codes** (route (A)): for continuous `ψ`, the map
`c ↦ lim_n ∫ c(2^{-n}, z) ψ(z) d²z` (zero off the convergence locus) is measurable on the canonical profiles. -/
theorem measurable_circleTestLimit {ψ : ℂ → ℝ} (hψ : Continuous ψ) :
    Measurable (circleTestLimit ψ) := by
  classical
  set S : Set CanonicalProfile :=
    {c : CanonicalProfile | ∃ l : ℝ, Tendsto (fun n => circleTestIntegral ψ n c) atTop (𝓝 l)} with hSdef
  have hS : MeasurableSet S := measurableSet_circleTestConverges hψ
  have hm : ∀ m : ℕ, Measurable (S.indicator (circleTestIntegral ψ m)) :=
    fun m => (measurable_circleTestIntegral hψ m).indicator hS
  refine measurable_of_tendsto_metrizable hm (tendsto_pi_nhds.mpr fun c => ?_)
  by_cases hex : ∃ l : ℝ, Tendsto (fun n => circleTestIntegral ψ n c) atTop (𝓝 l)
  · obtain ⟨l, hl⟩ := hex
    have hex' : ∃ l : ℝ, Tendsto (fun n => circleTestIntegral ψ n c) atTop (𝓝 l) := ⟨l, hl⟩
    have hval : circleTestLimit ψ c = l := by
      simp only [circleTestLimit, hex', ↓reduceIte]
      exact hl.limUnder_eq
    have hcS : c ∈ S := ⟨l, hl⟩
    simp only [indicator_of_mem hcS]
    rw [hval]
    exact hl
  · have hval : circleTestLimit ψ c = 0 := by
      simp only [circleTestLimit, hex, ↓reduceIte]
    have hcS : c ∉ S := hex
    simp only [indicator_of_notMem hcS]
    rw [hval]
    exact tendsto_const_nhds

end

end HarmonicBalls
