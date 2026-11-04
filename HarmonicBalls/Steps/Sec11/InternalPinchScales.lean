import HarmonicBalls.Draft.Section11
import HarmonicBalls.Proofs.Sec8.BlockFrequency

/-!
# Pinch events with internal-metric bounds

The strengthened event replaces the two upper bounds involving the global
metric by upper bounds involving the internal metric of the disk `B_{6r}`.
Its two set-distance terms remain global: their locality requires separate
proof. This isolates the internal-metric part of the locality issue in the
proof of Lemma 11.13.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Finset
open scoped ENNReal Topology BigOperators

/-- The strengthened pinch event with internal-metric upper bounds. -/
def pinchPointEventWithInternalBounds
    (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M r : ℝ) (z : ℂ) : Prop :=
  (⨆ x ∈ sphere z (5 * r), internalMetric D (ball z (6 * r)) z x) <
      ENNReal.ofReal (setDist D (rescaledSet Q' r z) (frontier (rescaledSet Q r z))) ∧
    (⨆ x ∈ rescaledSet T r z, ⨆ y ∈ rescaledSet T r z,
      internalMetric D (ball z (6 * r)) x y) <
      ENNReal.ofReal (setDist D {z} (sphere z (5 * r))) ∧
    ENNReal.ofReal M * annulusGreenPotentialSup μ z (3 * r) (6 * r) < μ (rescaledSet U r z)

/-- Internal-metric bounds imply the global-metric pinch event. -/
theorem pinchPointEvent_of_internalBounds
    {μ : Measure ℂ} {D : ℂ → ℂ → ℝ} {U T Q' Q : Set ℂ} {M r : ℝ} {z : ℂ}
    (hD : IsEuclideanLengthMetric D)
    (h : pinchPointEventWithInternalBounds μ D U T Q' Q M r z) :
    pinchPointEvent μ D U T Q' Q M r z := by
  have hle (x y : ℂ) : ENNReal.ofReal (D x y) ≤ internalMetric D (ball z (6 * r)) x y := by
    rw [hD.ofReal_eq_internalMetric]
    exact internalMetric_anti D (subset_univ _) x y
  refine ⟨lt_of_le_of_lt ?_ h.1, lt_of_le_of_lt ?_ h.2.1, h.2.2⟩
  · exact iSup_le fun x => iSup_le fun _ => le_iSup_of_le x (le_iSup_of_le ‹_› (hle _ _))
  · refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
    exact le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy (hle _ _))))

/-- Positive lower block density of the strengthened event transfers to the
original pinch event. -/
theorem eventually_pinchPointEvent_block_ncard_of_internalBounds
    {μ : Measure ℂ} {D : ℂ → ℂ → ℝ} {U T Q' Q : Set ℂ} {M : ℝ} {z : ℂ} {δ : ℝ}
    (hD : IsEuclideanLengthMetric D)
    (h : ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEventWithInternalBounds μ D U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ)) :
    ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEvent μ D U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ) := by
  filter_upwards [h] with N hN
  have hsub : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
      pinchPointEventWithInternalBounds μ D U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z} ⊆
      {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
      pinchPointEvent μ D U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z} := by
    intro n hn
    exact ⟨hn.1, hn.2.1, pinchPointEvent_of_internalBounds hD hn.2.2⟩
  have hfinite : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
      pinchPointEvent μ D U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.Finite :=
    (Set.finite_Icc (N + 1) (2 * N)).subset (fun _ hn => ⟨hn.1, hn.2.1⟩)
  exact hN.trans (by exact_mod_cast Set.ncard_le_ncard hsub hfinite)

open Classical in
/-- A positive limiting frequency of the strengthened pinch event implies the
block-density conclusion for the original event. -/
theorem eventually_pinchPointEvent_block_ncard_of_internalFrequency
    {μ : Measure ℂ} {D : ℂ → ℂ → ℝ} {U T Q' Q : Set ℂ} {M : ℝ} {z : ℂ} {q δ : ℝ}
    (hD : IsEuclideanLengthMetric D) (hδ : δ < q)
    (h : Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N,
        if pinchPointEventWithInternalBounds μ D U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z
        then (1 : ℝ) else 0) / (N : ℝ)) atTop (𝓝 q)) :
    ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEvent μ D U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ) := by
  classical
  apply eventually_pinchPointEvent_block_ncard_of_internalBounds hD
  have hf := eventually_goodScale_block_ncard
    (fun n => pinchPointEventWithInternalBounds μ D U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z) h hδ
  filter_upwards [hf] with N hN
  simpa only [Set.mem_Icc, and_assoc] using hN

end HarmonicBalls
