import HarmonicBalls.Steps.Sec11.ContinuousMetricVersions

/-! # Extension of internal metric observables from a dense set -/

namespace HarmonicBalls

open MeasureTheory Filter Set Topology
open scoped ENNReal

/-- A simultaneously valid, coordinatewise measurable internal metric version
on a dense subset of an open domain extends to every pair in that domain. -/
theorem exists_internalMetric_version_of_dense
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (m : MeasurableSpace Ω)
    {D : Ω → ℂ → ℂ → ℝ} {U Q : Set ℂ} (hU : IsOpen U)
    (hdense : U ⊆ closure Q)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (G : Ω → ℂ → ℂ → ℝ≥0∞)
    (hG : ∀ x y, Measurable[m] (fun ω => G ω x y))
    (hGeq : ∀ᵐ ω ∂P, ∀ x ∈ Q, ∀ y ∈ Q,
      internalMetric (D ω) U x y = G ω x y) :
    ∃ H : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ x y, Measurable[m] (fun ω => H ω x y)) ∧
      ∀ᵐ ω ∂P, ∀ x ∈ U, ∀ y ∈ U,
        internalMetric (D ω) U x y = H ω x y := by
  classical
  have hseq (x : U) : ∃ q : ℕ → ℂ, (∀ n, q n ∈ Q) ∧
      Tendsto q atTop (𝓝 x.1) := mem_closure_iff_seq_limit.mp (hdense x.2)
  choose q hq hqt using hseq
  let H : Ω → ℂ → ℂ → ℝ≥0∞ := fun ω x y =>
    if hx : x ∈ U then if hy : y ∈ U then
      liminf (fun n => G ω (q ⟨x, hx⟩ n) (q ⟨y, hy⟩ n)) atTop
    else 0 else 0
  refine ⟨H, ?_, ?_⟩
  · intro x y
    by_cases hx : x ∈ U <;> by_cases hy : y ∈ U <;> simp only [H, hx, hy, ↓reduceDIte]
    · exact Measurable.liminf (fun n => hG _ _)
    all_goals exact measurable_const
  · filter_upwards [hmetric, hGeq] with ω hD heq x hx y hy
    have hnonneg (x y : ℂ) : 0 ≤ D ω x y := by
      have ht := hD.triangle x y x
      rw [hD.self_eq_zero, hD.symm y x] at ht
      linarith
    have ht := (hD.continuousAt_internalMetric_pair hnonneg hU hx hy).tendsto.comp
      ((hqt ⟨x, hx⟩).prodMk_nhds (hqt ⟨y, hy⟩))
    have hl := ht.liminf_eq
    change liminf (fun n => internalMetric (D ω) U (q ⟨x, hx⟩ n) (q ⟨y, hy⟩ n))
      atTop = _ at hl
    simp only [fun n => heq _ (hq ⟨x, hx⟩ n) _ (hq ⟨y, hy⟩ n)] at hl
    simpa only [H, hx, hy, ↓reduceDIte] using hl.symm


end HarmonicBalls
