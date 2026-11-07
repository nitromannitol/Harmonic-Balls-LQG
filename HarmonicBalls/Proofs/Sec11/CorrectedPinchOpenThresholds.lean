import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstThresholds
import HarmonicBalls.Steps.Sec11.WeylAnnulusBounds
import HarmonicBalls.Steps.Sec11.MetricArcLength

/-! # Open corridor thresholds for the first Weyl shift -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- The radius-six open obstacle complement has uniformly finite internal
metric distances to the radius-five sphere. -/
theorem IsCorrectedPinchConfiguration.six_open_corridor_internalMetric_lt_top
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) :
    (⨆ y ∈ sphere (0 : ℂ) 5,
      internalMetric D (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
        closure (thickening (2 * δ) W))) 0 y) < ∞ := by
  let F : Set ℂ := ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
    closure (thickening (2 * δ) W))
  let C := connectedComponentIn F (0 : ℂ)
  have hsphere : sphere (0 : ℂ) 5 ⊆ C := h.sphere_subset_six_component
  obtain ⟨y, hy⟩ := NormedSpace.sphere_nonempty (x := (0 : ℂ)) |>.mpr (by norm_num : (0 : ℝ) ≤ 5)
  have hzeroF : (0 : ℂ) ∈ F := connectedComponentIn_nonempty_iff.mp ⟨y, hsphere hy⟩
  have hzero : (0 : ℂ) ∈ C := mem_connectedComponentIn hzeroF
  have hopen : IsOpen C :=
    (isOpen_ball.sdiff (isClosed_closure.union isClosed_closure)).connectedComponentIn
  have hconn : IsConnected C := ⟨⟨0, hzero⟩, isPreconnected_connectedComponentIn⟩
  apply lt_of_le_of_lt _ (hD.iSup_internalMetric_lt_top_of_isCompact hnonneg hopen hconn
    (isCompact_sphere (0 : ℂ) 5) hsphere hzero)
  exact iSup_le fun y => iSup_le fun hy =>
    le_iSup_of_le y (le_iSup_of_le hy (internalMetric_anti D (connectedComponentIn_subset F 0) 0 y))

/-- Select deterministic strict bounds for the four quantities used by the
first two Weyl bumps. The upper path bound uses an open radius-six corridor. -/
theorem IsCorrectedPinchConfiguration.exists_open_first_certificate_thresholds
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (D : Ω → ℂ → ℂ → ℝ) (hA : 0 < P A)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hconn : IsConnected (T \ thickening (3 * δ) W)) :
    ∃ n m k l : ℕ, 0 < n ∧ 0 < k ∧ 0 < P {ω | ω ∈ A ∧
      (n : ℝ≥0∞)⁻¹ < ENNReal.ofReal (setDist (D ω) Q' (frontier Q)) ∧
      (⨆ y ∈ sphere (0 : ℂ) 5,
        internalMetric (D ω) (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0 y) < m ∧
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
    internalMetric (D ω) (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0 y
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
      (h.six_open_corridor_internalMetric_lt_top hm hn).ne⟩
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

/-- A Weyl exponent bounded on the open corridor controls the constrained
radius-six distances needed for the first pinch certificate. -/
theorem IsEuclideanLengthMetric.six_corridor_weyl_upper_bound
    {Q W : Set ℂ} {δ ξ B : ℝ} {f : ℂ → ℝ} {D E : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) (hE : IsEuclideanLengthMetric E)
    (hEnonneg : ∀ x y, 0 ≤ E x y)
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hweight : ∀ z ∈ ball (0 : ℂ) 6 \
      (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W)), ξ * f z ≤ B) :
    (⨆ y ∈ sphere (0 : ℂ) 5,
      internalMetric E ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 y) ≤
      ENNReal.ofReal (Real.exp B) * (⨆ y ∈ sphere (0 : ℂ) 5,
        internalMetric D (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
          closure (thickening (2 * δ) W))) 0 y) := by
  let F : Set ℂ := ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
    closure (thickening (2 * δ) W))
  have hopen : IsOpen F := isOpen_ball.sdiff (isClosed_closure.union isClosed_closure)
  have hsub : F ⊆ (thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6 := by
    intro x hx
    refine ⟨?_, hx.1⟩
    rw [thickening_union]
    intro hmem
    exact hx.2 (hmem.elim (fun hq => Or.inl (subset_closure hq))
      (fun hw => Or.inr (subset_closure hw)))
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  calc
    internalMetric E _ 0 y ≤ internalMetric E F 0 y := internalMetric_anti E hsub 0 y
    _ ≤ ENNReal.ofReal (Real.exp B) * internalMetric D F 0 y :=
      hD.internalMetric_weylScaling_le hE hEnonneg hopen (hD.weylScaling_zero ξ)
        hscale hweight 0 y
    _ ≤ ENNReal.ofReal (Real.exp B) * (⨆ z ∈ sphere (0 : ℂ) 5,
        internalMetric D F 0 z) := by
      gcongr
      exact le_iSup_of_le y (le_iSup_of_le hy le_rfl)

#print axioms IsCorrectedPinchConfiguration.exists_open_first_certificate_thresholds
#print axioms IsEuclideanLengthMetric.six_corridor_weyl_upper_bound

end HarmonicBalls
