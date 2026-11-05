import HarmonicBalls.Proofs.Sec6.DenseNearbyGoodAnnulusTransfer

/-! # Good annuli at relatively dense centres -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Good annuli at a family accumulating at the reference centre transfer to
that centre after strict relaxation of the thresholds. -/
theorem goodAnnulus_of_mem_closure_range
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] {q : ℕ → ℂ} {z : ℂ}
    (hz : z ∈ closure (range q)) {r a a' b b' : ℝ}
    (hr : 0 < r) (ha' : 0 ≤ a') (ha : a' < a) (hb : 0 ≤ b) (hbb : b < b')
    (h3 : μ (sphere z (3*r)) = 0) (h5 : μ (sphere z (5*r)) = 0)
    (hpos : 0 < μ (annulus z (3*r) (5*r)))
    (hgood : ∀ i, IsGoodAnnulus μ r (q i) a b) :
    IsGoodAnnulus μ r z a' b' := by
  have hfin : μ (annulus z (3*r) (5*r)) ≠ ∞ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono sdiff_subset)
  obtain ⟨δ, hδ, hnear⟩ := exists_reverse_nearby_goodAnnulus μ z hr h3 h5 hpos hfin
    ha' ha hb hbb
  obtain ⟨w, ⟨i, rfl⟩, hi⟩ := (Metric.mem_closure_iff.mp hz) δ hδ
  exact hnear (q i) (by simpa only [dist_comm] using hi) (hgood i)

/-- For mass-typical centres, a count of radii good at every member of a
radius-dependent accumulating family is bounded by the relaxed root count.
The scale function may differ from the radius used to index the count. -/
theorem ae_relative_dense_goodAnnuli_count_le_root_count
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] [NullSingletonClass μ] :
    ∀ᵐ z ∂μ, ∀ (S : Set ℝ), S.Finite → ∀ (R : ℝ → ℝ) (q : ℝ → ℕ → ℂ),
      ∀ {a a' b b' : ℝ}, 0 ≤ a' → a' < a → 0 ≤ b → b < b' →
      (∀ r ∈ S, 0 < R r ∧ z ∈ closure (range (q r)) ∧
        0 < μ (annulus z (3 * R r) (5 * R r))) →
      {r ∈ S | ∀ i, IsGoodAnnulus μ (R r) (q r i) a b}.ncard ≤
        {r ∈ S | IsGoodAnnulus μ (R r) z a' b'}.ncard := by
  filter_upwards [ae_spheres_null_of_atomless μ] with z hz
  intro S hS R q a a' b b' ha' ha hb hbb hreg
  apply Set.ncard_le_ncard ?_ (hS.subset (by intro r hr; exact hr.1))
  intro r hr
  obtain ⟨hrpos, hq, hp⟩ := hreg r hr.1
  exact ⟨hr.1, goodAnnulus_of_mem_closure_range μ hq hrpos ha' ha hb hbb
    (hz _) (hz _) hp hr.2⟩

universe u

/-- Under all-scales LQG volume growth, the relative dense-family count
comparison holds at mass-typical centres. -/
theorem ae_lqg_ae_relative_dense_goodAnnuli_count_le_root_count
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ (S : Set ℝ), S.Finite →
      ∀ (R : ℝ → ℝ) (q : ℝ → ℕ → ℂ),
      ∀ {a a' b b' : ℝ}, 0 ≤ a' → a' < a → 0 ≤ b → b < b' →
      (∀ r ∈ S, 0 < R r ∧ z ∈ closure (range (q r)) ∧
        0 < μ ω (annulus z (3 * R r) (5 * R r))) →
      {r ∈ S | ∀ i, IsGoodAnnulus (μ ω) (R r) (q r i) a b}.ncard ≤
        {r ∈ S | IsGoodAnnulus (μ ω) (R r) z a' b'}.ncard := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hV
  let : IsLocallyFiniteMeasure (μ ω) := hV.1
  let : NullSingletonClass (μ ω) := ⟨fun x => by
    have hR : 0 < ‖x‖ + 1 := by positivity
    have hx : x ∈ ball (0 : ℂ) (‖x‖ + 1) := by
      simp only [mem_ball, dist_zero_right]
      linarith
    exact (hV.2 _ hR).measure_singleton hx⟩
  exact ae_relative_dense_goodAnnuli_count_le_root_count (μ ω)

end HarmonicBalls.Section6
