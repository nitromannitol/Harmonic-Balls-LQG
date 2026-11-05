import HarmonicBalls.Proofs.Sec6.RootedReverseGoodAnnulusContinuity

/-! # Dense-centre transfer to mass-typical centres -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Good annuli at a dense set of centres transfer to any regular reference
centre in an open set after strict relaxation of the thresholds. -/
theorem goodAnnulus_of_dense_centres
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] {U : Set ℂ} (hU : IsOpen U)
    {q : ℕ → ℂ} (hq : DenseRange q) {z : ℂ} (hz : z ∈ U)
    {r a a' b b' : ℝ} (hr : 0 < r) (ha' : 0 ≤ a') (ha : a' < a)
    (hb : 0 ≤ b) (hbb : b < b')
    (h3 : μ (sphere z (3*r)) = 0) (h5 : μ (sphere z (5*r)) = 0)
    (hpos : 0 < μ (annulus z (3*r) (5*r)))
    (hgood : ∀ i, q i ∈ U → IsGoodAnnulus μ r (q i) a b) :
    IsGoodAnnulus μ r z a' b' := by
  have hfin : μ (annulus z (3*r) (5*r)) ≠ ∞ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono sdiff_subset)
  obtain ⟨δ, hδ, hnear⟩ := exists_reverse_nearby_goodAnnulus μ z hr h3 h5 hpos hfin
    ha' ha hb hbb
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  obtain ⟨i, hi⟩ := (Metric.denseRange_iff.mp hq) z (min δ ρ) (lt_min hδ hρ)
  have hi' : dist (q i) z < min δ ρ := by simpa only [dist_comm] using hi
  have hiU : q i ∈ U := hρU (mem_ball.mpr (lt_of_lt_of_le hi' (min_le_right _ _)))
  exact hnear (q i) (lt_of_lt_of_le hi' (min_le_left _ _)) (hgood i hiU)

/-- At mass-typical reference centres, dense-centre transfer holds for every
positive radius with positive annular mass and every strict threshold slack. -/
theorem ae_goodAnnulus_of_dense_centres
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] [NullSingletonClass μ]
    {U : Set ℂ} (hU : IsOpen U) {q : ℕ → ℂ} (hq : DenseRange q) :
    ∀ᵐ z ∂μ, z ∈ U → ∀ {r a a' b b' : ℝ}, 0 < r → 0 ≤ a' → a' < a →
      0 ≤ b → b < b' → 0 < μ (annulus z (3*r) (5*r)) →
      (∀ i, q i ∈ U → IsGoodAnnulus μ r (q i) a b) →
      IsGoodAnnulus μ r z a' b' := by
  filter_upwards [ae_spheres_null_of_atomless μ] with z hz
  intro hzU r a a' b b' hr ha' ha hb hbb hp hgood
  exact goodAnnulus_of_dense_centres μ hU hq hzU hr ha' ha hb hbb (hz _) (hz _) hp hgood

/-- At mass-typical centres, the number of radii good at every dense-family
centre in an open set is bounded by the good-radius count at the root. -/
theorem ae_dense_goodAnnuli_count_le_root_count
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] [NullSingletonClass μ]
    {U : Set ℂ} (hU : IsOpen U) {q : ℕ → ℂ} (hq : DenseRange q) :
    ∀ᵐ z ∂μ, z ∈ U → ∀ (S : Set ℝ), S.Finite →
      ∀ {a a' b b' : ℝ}, 0 ≤ a' → a' < a → 0 ≤ b → b < b' →
      (∀ r ∈ S, 0 < r ∧ 0 < μ (annulus z (3*r) (5*r))) →
      {r ∈ S | ∀ i, q i ∈ U → IsGoodAnnulus μ r (q i) a b}.ncard ≤
        {r ∈ S | IsGoodAnnulus μ r z a' b'}.ncard := by
  filter_upwards [ae_goodAnnulus_of_dense_centres μ hU hq] with z htransfer
  intro hz S hS a a' b b' ha' ha hb hbb hreg
  apply Set.ncard_le_ncard ?_ (hS.subset (by intro r hr; exact hr.1))
  intro r hr
  obtain ⟨hrpos, hp⟩ := hreg r hr.1
  exact ⟨hr.1, htransfer hz hrpos ha' ha hb hbb hp hr.2⟩

/-- A radius-dependent dense family gives the same count comparison when its
open centre neighbourhood and its enumeration vary with the radius. -/
theorem ae_dense_goodAnnuli_varying_count_le_root_count
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] [NullSingletonClass μ]
    {U : ℝ → Set ℂ} {q : ℝ → ℕ → ℂ} :
    ∀ᵐ z ∂μ, ∀ (S : Set ℝ), S.Finite →
      ∀ {a a' b b' : ℝ}, 0 ≤ a' → a' < a → 0 ≤ b → b < b' →
      (∀ r ∈ S, IsOpen (U r) ∧ DenseRange (q r) ∧ z ∈ U r ∧
        0 < r ∧ 0 < μ (annulus z (3*r) (5*r))) →
      {r ∈ S | ∀ i, q r i ∈ U r → IsGoodAnnulus μ r (q r i) a b}.ncard ≤
        {r ∈ S | IsGoodAnnulus μ r z a' b'}.ncard := by
  filter_upwards [ae_spheres_null_of_atomless μ] with z hz
  intro S hS a a' b b' ha' ha hb hbb hreg
  apply Set.ncard_le_ncard ?_ (hS.subset (by intro r hr; exact hr.1))
  intro r hr
  obtain ⟨hU, hq, hzU, hrpos, hp⟩ := hreg r hr.1
  exact ⟨hr.1, goodAnnulus_of_dense_centres μ hU hq hzU hrpos ha' ha hb hbb
    (hz _) (hz _) hp hr.2⟩

universe u

/-- Under the all-scales volume-growth input, the dense-family count is a
lower bound for the relaxed count at LQG-mass-typical centres. -/
theorem ae_lqg_ae_dense_goodAnnuli_count_le_root_count
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {U : Set ℂ} (hU : IsOpen U) {q : ℕ → ℂ} (hq : DenseRange q) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ U → ∀ (S : Set ℝ), S.Finite →
      ∀ {a a' b b' : ℝ}, 0 ≤ a' → a' < a → 0 ≤ b → b < b' →
      (∀ r ∈ S, 0 < r ∧ 0 < μ ω (annulus z (3*r) (5*r))) →
      {r ∈ S | ∀ i, q i ∈ U → IsGoodAnnulus (μ ω) r (q i) a b}.ncard ≤
        {r ∈ S | IsGoodAnnulus (μ ω) r z a' b'}.ncard := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hV
  let : IsLocallyFiniteMeasure (μ ω) := hV.1
  let : NullSingletonClass (μ ω) := ⟨fun x => by
    have hR : 0 < ‖x‖ + 1 := by positivity
    have hx : x ∈ ball (0 : ℂ) (‖x‖ + 1) := by
      simp only [mem_ball, dist_zero_right]
      linarith
    exact (hV.2 _ hR).measure_singleton hx⟩
  exact ae_dense_goodAnnuli_count_le_root_count (μ ω) hU hq

end HarmonicBalls.Section6
