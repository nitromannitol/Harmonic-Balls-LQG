import Mathlib
import HarmonicBalls.Defs.GFF

/-! # Route (A), Palm identity: joint measurability of a circle average at a fixed radius

For the whole-plane GFF, the circle average `ω ↦ hcirc ω r z` is measurable for each `z`, and `z ↦ hcirc ω r z` is
continuous for almost every `ω` (`IsWholePlaneGFF.ae_continuousOn_circle`). Hence there is a jointly measurable
version `g` of `(ω, z) ↦ hcirc ω r z`: it is continuous in `z` for every `ω` and equal to `hcirc ω r ·` off a
measurable `P`-null set of samples. This is the measurability input of the Fubini identity for the marked first
moment `E μ_ε(η) = ∫ η` (r10 `l:r9-marked`, "First moments and the required `L¹` convergence").
-/

noncomputable section

open MeasureTheory
open scoped Classical

namespace HarmonicBalls

/-- A jointly measurable version of the circle averages at a fixed positive radius: continuous in `z` for every
sample, and equal to `hcirc ω r ·` for every sample outside a measurable `P`-null set `N`. -/
theorem exists_measurable_circleAverage_version {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {r : ℝ} (hr : 0 < r) :
    ∃ g : Ω → ℂ → ℝ, Measurable (fun p : Ω × ℂ => g p.1 p.2) ∧ (∀ ω, Continuous (g ω)) ∧
      ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ ∀ ω, ω ∉ N → ∀ z, g ω z = hcirc ω r z := by
  have hae : ∀ᵐ ω ∂P, Continuous (fun z => hcirc ω r z) := by
    filter_upwards [hG.ae_continuousOn_circle] with ω hω
    exact hω.comp_continuous (continuous_const.prodMk continuous_id) (fun z => ⟨hr, Set.mem_univ z⟩)
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hae)
  have hcontN : ∀ ω, ω ∉ N → Continuous (fun z => hcirc ω r z) := fun ω hω => by
    by_contra hn
    exact hω (hsub (show ω ∈ {a | ¬ Continuous (fun z => hcirc a r z)} from hn))
  refine ⟨fun ω z => if ω ∈ N then 0 else hcirc ω r z, ?_, ?_, N, hNm, hN0, ?_⟩
  · have hu : Measurable (Function.uncurry
        (fun (z : ℂ) (ω : Ω) => if ω ∈ N then (0 : ℝ) else hcirc ω r z)) := by
      refine measurable_uncurry_of_continuous_of_measurable (fun ω => ?_) (fun z => ?_)
      · by_cases h : ω ∈ N
        · simp only [h]
          exact continuous_const
        · simp [h]
          exact hcontN ω h
      · exact Measurable.ite (p := fun ω => ω ∈ N) hNm measurable_const (hG.measurable_circle r z hr)
    exact hu.comp measurable_swap
  · intro ω
    by_cases h : ω ∈ N
    · simp only [h]
      exact continuous_const
    · simp [h]
      exact hcontN ω h
  · intro ω hω z
    simp [hω]

end HarmonicBalls

end
