import HarmonicBalls.Steps.Sec11.InternalMetricContinuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Sequences

/-! # Continuous internal metric versions

Countably many local distance observables determine every internal distance
when the underlying metric induces the Euclidean topology.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Topology
open scoped ENNReal

/-- A common measurable version on countably many pairs extends to all pairs
in an open domain, simultaneously on one full-measure event. -/
theorem exists_internalMetric_version_of_countable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (m : MeasurableSpace Ω)
    {D : Ω → ℂ → ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U) (hne : U.Nonempty)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hcount : ∀ p : ℕ → ℂ × ℂ, (∀ n, (p n).1 ∈ U ∧ (p n).2 ∈ U) →
      ∃ H : Ω → ℕ → ℝ≥0∞, Measurable[m] H ∧
        ∀ᵐ ω ∂P, ∀ n, internalMetric (D ω) U (p n).1 (p n).2 = H ω n) :
    ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ x y, Measurable[m] (fun ω => G ω x y)) ∧
      ∀ᵐ ω ∂P, ∀ x ∈ U, ∀ y ∈ U, internalMetric (D ω) U x y = G ω x y := by
  classical
  let : Nonempty U := hne.to_subtype
  let d : ℕ → U × U := TopologicalSpace.denseSeq (U × U)
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq (U × U)
  have hseq (a : U × U) : ∃ k : ℕ → ℕ, Tendsto (fun n => d (k n)) atTop (𝓝 a) := by
    obtain ⟨s, hs, ht⟩ := mem_closure_iff_seq_limit.mp (hd a)
    choose k hk using hs
    exact ⟨k, by simpa only [hk] using ht⟩
  choose k hk using hseq
  let p : ℕ → ℂ × ℂ := fun n => ((d n).1.1, (d n).2.1)
  obtain ⟨H, hH, hHeq⟩ := hcount p (fun n => ⟨(d n).1.2, (d n).2.2⟩)
  let G : Ω → ℂ → ℂ → ℝ≥0∞ := fun ω x y =>
    if hx : x ∈ U then if hy : y ∈ U then
      liminf (fun n => H ω (k (⟨x, hx⟩, ⟨y, hy⟩) n)) atTop
    else 0 else 0
  refine ⟨G, ?_, ?_⟩
  · intro x y
    by_cases hx : x ∈ U <;> by_cases hy : y ∈ U <;> simp only [G, hx, hy, ↓reduceDIte]
    · exact Measurable.liminf (fun n => (measurable_pi_apply _).comp hH)
    all_goals exact measurable_const
  · filter_upwards [hmetric, hHeq] with ω hD hEq x hx y hy
    have hnonneg (x y : ℂ) : 0 ≤ D ω x y := by
      have ht := hD.triangle x y x
      rw [hD.self_eq_zero, hD.symm y x] at ht
      linarith
    have hconv : Tendsto (fun n => p (k (⟨x, hx⟩, ⟨y, hy⟩) n)) atTop (𝓝 (x, y)) := by
      have hc : Continuous (fun a : U × U => (a.1.1, a.2.1)) :=
        (continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)
      exact hc.continuousAt.tendsto.comp (hk (⟨x, hx⟩, ⟨y, hy⟩))
    have ht := (hD.continuousAt_internalMetric_pair hnonneg hU hx hy).tendsto.comp hconv
    have heq := ht.liminf_eq
    change liminf (fun n => internalMetric (D ω) U
      (p (k (⟨x, hx⟩, ⟨y, hy⟩) n)).1 (p (k (⟨x, hx⟩, ⟨y, hy⟩) n)).2) atTop = _ at heq
    simp only [hEq] at heq
    simpa only [G, hx, hy, ↓reduceDIte] using heq.symm


end HarmonicBalls
