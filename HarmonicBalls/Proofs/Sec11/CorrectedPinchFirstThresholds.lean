import HarmonicBalls.Proofs.Sec11.CorrectedPinchCorridor
import HarmonicBalls.Steps.Sec11.PinchDistancePositivity
import HarmonicBalls.Steps.Sec11.PinchThresholdSelection
import HarmonicBalls.Steps.Sec11.PinchAnnulusConnected

/-! # Deterministic thresholds for the first pinch certificate

The connectivity of the outer auxiliary piece is a separate geometric
obligation for the chosen keyhole.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- A connected outer auxiliary piece has finite internal diameter. -/
theorem IsPinchPointProofConfiguration.outer_piece_internalDiam_lt_top
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hconn : IsConnected (T \ thickening (3 * δ) W))
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) :
    internalDiam D δ (T \ thickening (3 * δ) W) < ∞ := by
  have hbounded : Bornology.IsBounded (T \ thickening (3 * δ) W) :=
    isBounded_ball.subset (sdiff_subset.trans (h.T_subset.trans (fun _ hx => hx.1)))
  exact hD.internalDiam_lt_top_of_connected_thickening hnonneg h.δ₀_mem.1 hbounded
    (IsConnected.thickening_complex hconn h.δ₀_mem.1)

/-- Select deterministic strict bounds for the four quantities used by the
first two Weyl bumps. The upper path bound uses the radius-six corridor. -/
theorem IsCorrectedPinchConfiguration.exists_first_certificate_thresholds
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (D : Ω → ℂ → ℂ → ℝ) (hA : 0 < P A)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hconn : IsConnected (T \ thickening (3 * δ) W)) :
    ∃ n m k l : ℕ, 0 < n ∧ 0 < k ∧ 0 < P {ω | ω ∈ A ∧
      (n : ℝ≥0∞)⁻¹ < ENNReal.ofReal (setDist (D ω) Q' (frontier Q)) ∧
      (⨆ y ∈ sphere (0 : ℂ) 5,
        internalMetric (D ω) ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 y) < m ∧
      (k : ℝ≥0∞)⁻¹ < ENNReal.ofReal (setDist (D ω) {0} (sphere 0 (δ / 2))) ∧
      internalDiam (D ω) δ (T \ thickening (3 * δ) W) < l} := by
  have hdiam : ∀ᵐ ω ∂P, internalDiam (D ω) δ (T \ thickening (3 * δ) W) < ∞ := by
    filter_upwards [hmetric] with ω hm
    have hn : ∀ x y, 0 ≤ D ω x y := by
      intro x y
      have ht := hm.triangle x y x
      rw [hm.self_eq_zero, hm.symm y x] at ht
      linarith
    exact h.toIsPinchPointProofConfiguration.outer_piece_internalDiam_lt_top hconn hm hn
  let G : Set Ω := {ω | IsEuclideanLengthMetric (D ω) ∧
    internalDiam (D ω) δ (T \ thickening (3 * δ) W) < ∞}
  have hG : ∀ᵐ ω ∂P, ω ∈ G := hmetric.and hdiam
  have heq : A =ᵐ[P] A ∩ G := by
    filter_upwards [hG] with ω hω
    simp only [mem_inter_iff, hω, and_true]
  have hAG : 0 < P (A ∩ G) := by rwa [← measure_congr heq]
  let f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (setDist (D ω) Q' (frontier Q))
  let g : Ω → ℝ≥0∞ := fun ω => ⨆ y ∈ sphere (0 : ℂ) 5,
    internalMetric (D ω) ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 y
  have hfg : ∀ ω ∈ A ∩ G, f ω ≠ 0 ∧ g ω ≠ ∞ := by
    intro ω hω
    have hm : IsEuclideanLengthMetric (D ω) := hω.2.1
    have hn : ∀ x y, 0 ≤ D ω x y := by
      intro x y
      have ht := hm.triangle x y x
      rw [hm.self_eq_zero, hm.symm y x] at ht
      linarith
    exact ⟨(ENNReal.ofReal_pos.mpr
      (h.toIsPinchPointProofConfiguration.toIsPinchPointConfiguration.setDist_frontier_pos hm)).ne',
      (h.six_corridor_internalMetric_lt_top hm hn).ne⟩
  obtain ⟨n, m, hn, hp⟩ := exists_positive_measure_uniform_thresholds P (A ∩ G) f g hAG hfg
  let B : Set Ω := {ω | ω ∈ A ∩ G ∧ (n : ℝ≥0∞)⁻¹ < f ω ∧ g ω < m}
  let j : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (setDist (D ω) {0} (sphere 0 (δ / 2)))
  let d : Ω → ℝ≥0∞ := fun ω => internalDiam (D ω) δ (T \ thickening (3 * δ) W)
  have hjd : ∀ ω ∈ B, j ω ≠ 0 ∧ d ω ≠ ∞ := by
    intro ω hω
    have hm : IsEuclideanLengthMetric (D ω) := hω.1.2.1
    have hδ : 0 < δ / 2 := by linarith [h.δ₀_mem.1]
    have hsep : 0 < setDist (D ω) {0} (sphere 0 (δ / 2)) := by
      apply hm.setDist_pos_of_compact_subset_open isCompact_singleton (singleton_nonempty 0)
        isOpen_ball
      · exact singleton_subset_iff.mpr (mem_ball_self hδ)
      · exact NormedSpace.sphere_nonempty.mpr hδ.le
      · intro x hx hxball
        rw [mem_sphere] at hx
        rw [mem_ball] at hxball
        linarith
    exact ⟨(ENNReal.ofReal_pos.mpr hsep).ne', hω.1.2.2.ne⟩
  obtain ⟨k, l, hk, hp'⟩ := exists_positive_measure_uniform_thresholds P B j d hp hjd
  refine ⟨n, m, k, l, hn, hk, hp'.trans_le (measure_mono ?_)⟩
  intro ω hω
  exact ⟨hω.1.1.1, hω.1.2.1, hω.1.2.2, hω.2.1, hω.2.2⟩

#print axioms IsCorrectedPinchConfiguration.exists_first_certificate_thresholds

end HarmonicBalls
