import HarmonicBalls.Proofs.Sec6.SpatialUniformGoodAnnulus

/-! # Good-annulus thresholds on compact centre and radius sets

The fine-support assembly uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess Metric
open scoped ENNReal Topology

/-- Local fine support provides a common threshold in a neighbourhood of
both a centre and a positive radius. -/
theorem uniform_goodAnnulus_threshold_near_center_radius
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    (hloc : ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
      ∀ E : Set ℂ, MeasurableSet E → μ (ball x ε \ E) = 0 →
      ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω = 0)
    (z₀ : ℂ) {r b : ℝ} (hr : 0 < r) (hb : 0 < b) :
    ∃ a : ℝ, 0 < a ∧ ∀ z ∈ ball z₀ (r / 32), ∀ s ∈ Ioo (r * (127 / 128)) (r * (129 / 128)),
      IsGoodAnnulus μ s z a b := by
  let U := annulus z₀ (3 * r + r / 8) (5 * r - r / 8)
  let A := ball z₀ (6 * r + 1)
  let ν : Measure ℂ := volume.restrict U
  let ι := {p : ℂ × ℝ // p.1 ∈ ball z₀ (r / 32) ∧ p.2 ∈ Ioo (r * (127 / 128)) (r * (129 / 128))}
  let center : ι → ℂ := fun i => i.1.1
  let radius : ι → ℝ := fun i => i.1.2
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_closedBall
  have hνfin : volume U ≠ ∞ := ne_top_of_le_ne_top
    (measure_ball_lt_top (μ := volume)).ne (measure_mono sdiff_subset)
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hνfin
  have hUsub : U ⊆ A := by
    intro x hx
    change dist x z₀ < 6 * r + 1
    have hx' : dist x z₀ < 5 * r - r / 8 := hx.1
    linarith
  have hinner : ∀ i, U ⊆ annulus (center i) (3 * radius i) (5 * radius i) := by
    intro i x hx
    have hi : dist (center i) z₀ < r / 32 := i.property.1
    have hslo : r * (127 / 128) < radius i := i.property.2.1
    have hshi : radius i < r * (129 / 128) := i.property.2.2
    have hx' : dist x z₀ < 5 * r - r / 8 ∧ 3 * r + r / 8 < dist x z₀ := by
      simpa only [U, annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] using hx
    have ht1 := dist_triangle x z₀ (center i)
    have ht2 := dist_triangle x (center i) z₀
    have hs : dist z₀ (center i) = dist (center i) z₀ := dist_comm _ _
    change dist x (center i) < 5 * radius i ∧ ¬ dist x (center i) ≤ 3 * radius i
    constructor <;> linarith
  have hball : ∀ i, ∀ u ∈ sphere (center i) (4 * radius i), ball u (r / 8) ⊆ U := by
    intro i u hu x hx
    have hi : dist (center i) z₀ < r / 32 := i.property.1
    have hslo : r * (127 / 128) < radius i := i.property.2.1
    have hshi : radius i < r * (129 / 128) := i.property.2.2
    have hu' : dist u (center i) = 4 * radius i := hu
    have hx' : dist x u < r / 8 := hx
    have ht1 := dist_triangle x u (center i)
    have ht2 := dist_triangle u x z₀
    have ht3 := dist_triangle x (center i) z₀
    have ht6 := dist_triangle u z₀ (center i)
    have hsz : dist z₀ (center i) = dist (center i) z₀ := dist_comm _ _
    have hsu : dist u x = dist x u := dist_comm _ _
    change dist x z₀ < 5 * r - r / 8 ∧ ¬ dist x z₀ ≤ 3 * r + r / 8
    constructor <;> linarith
  have hball2 : ∀ i, ∀ u ∈ sphere (center i) (4 * radius i),
      ball u (2 * (r / 8)) ⊆ annulus (center i) (3 * radius i) (5 * radius i) := by
    intro i u hu
    have hslo : r * (127 / 128) < radius i := i.property.2.1
    have hpos : 0 < radius i := by linarith
    apply (ball_subset_ball (by linarith : 2 * (r / 8) ≤ radius i / 2)).trans
    exact middleCircle_half_disc_subset_annulus hpos hu
  obtain ⟨C, hC0, hCt, hmean⟩ :=
    uniform_goodAnnulus_family_avoidance_submean center radius (by positivity) hinner hball hball2
  obtain ⟨a, ha, hgood⟩ := exists_uniform_goodAnnulus_threshold_family μ ν
    (A := A) (U := U) isOpen_ball.measurableSet (measure_ball_ne_top (μ := μ)) hU
    (ae_restrict_mem hU.measurableSet) (by
      intro E hE hmass
      exact ae_instant_hit_of_ae_local_fine_support μ isOpen_ball hU.measurableSet hUsub
        hloc hE hmass) center radius hb (by
      intro i x hx
      have hi : dist (center i) z₀ < r / 32 := i.property.1
      have hshi : radius i < r * (129 / 128) := i.property.2.2
      have hx' : dist x (center i) < 5 * radius i := hx.1
      have ht := dist_triangle x (center i) z₀
      change dist x z₀ < 6 * r + 1
      linarith) hC0 hCt hmean
  exact ⟨a, ha, fun z hz s hs => hgood ⟨(z, s), hz, hs⟩⟩

/-- Local fine support gives a single positive threshold over arbitrary
compact sets of centres and positive radii. -/
theorem uniform_goodAnnulus_threshold_on_compact_centers_radii
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    (hloc : ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
      ∀ E : Set ℂ, MeasurableSet E → μ (ball x ε \ E) = 0 →
      ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω = 0)
    {K : Set ℂ} (hK : IsCompact K) {R : Set ℝ} (hR : IsCompact R)
    (hRpos : R ⊆ Ioi 0) {b : ℝ} (hb : 0 < b) :
    ∃ a : ℝ, 0 < a ∧ ∀ z ∈ K, ∀ r ∈ R, IsGoodAnnulus μ r z a b := by
  classical
  let ι := {p : ℂ × ℝ // p ∈ K ×ˢ R}
  let V : ι → Set (ℂ × ℝ) := fun i =>
    ball i.1.1 (i.1.2 / 32) ×ˢ Ioo (i.1.2 * (127 / 128)) (i.1.2 * (129 / 128))
  have hpos (i : ι) : 0 < i.1.2 := hRpos i.property.2
  have hVopen (i : ι) : IsOpen (V i) := isOpen_ball.prod isOpen_Ioo
  have hcover : K ×ˢ R ⊆ ⋃ i : ι, V i := by
    intro p hp
    refine mem_iUnion.mpr ⟨⟨p, hp⟩, ?_⟩
    change p.1 ∈ ball p.1 (p.2 / 32) ∧ p.2 ∈ Ioo (p.2 * (127 / 128)) (p.2 * (129 / 128))
    have hp2 : 0 < p.2 := hRpos hp.2
    constructor
    · exact mem_ball_self (by positivity)
    · constructor <;> linarith
  obtain ⟨T, hT⟩ := (hK.prod hR).elim_finite_subcover V hVopen hcover
  have hex (i : ι) : ∃ a : ℝ, 0 < a ∧ ∀ p ∈ V i, IsGoodAnnulus μ p.2 p.1 a b := by
    obtain ⟨a, ha, hg⟩ := uniform_goodAnnulus_threshold_near_center_radius μ hloc i.1.1 (hpos i) hb
    exact ⟨a, ha, fun p hp => hg p.1 hp.1 p.2 hp.2⟩
  choose a ha hg using hex
  let F : Finset ℝ := insert 1 (T.image a)
  have hF : F.Nonempty := Finset.insert_nonempty _ _
  let d := F.inf' hF id
  have hd : 0 < d := by
    apply (Finset.lt_inf'_iff _).2
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · norm_num
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
      exact ha i
  refine ⟨d, hd, ?_⟩
  intro z hz r hr
  have hp := hT (show (z, r) ∈ K ×ˢ R from ⟨hz, hr⟩)
  simp only [mem_iUnion] at hp
  obtain ⟨i, hi, hp⟩ := hp
  have hmem : a i ∈ F := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  exact isGoodAnnulus_mono_mass (hg i (z, r) hp) (Finset.inf'_le id hmem)

universe u

/-- One whole-plane LQG full-measure event works for every compact set of
centres and every compact set of positive radii. -/
theorem ae_compact_goodAnnulus_thresholds_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (K : Set ℂ), IsCompact K → ∀ (R : Set ℝ), IsCompact R → R ⊆ Ioi 0 →
      ∀ b : ℝ, 0 < b → ∃ a : ℝ, 0 < a ∧
        ∀ z ∈ K, ∀ r ∈ R, IsGoodAnnulus (μ ω) r z a b := by
  let := h.isProbabilityMeasure
  have hloc := ae_ae_lqg_fine_support_of_disc_dyadic hgrowth hγ hγ2 h hμ
    (wholePlaneGFFAffineInvariance_proved P hC hcirc)
  filter_upwards [hμ, hloc] with ω hμω hlocω
  let : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
  intro K hK R hR hRpos b hb
  exact uniform_goodAnnulus_threshold_on_compact_centers_radii (μ ω) hlocω hK hR hRpos hb

/-- Under zero-strength existence, one full-measure event works for every
existing singular limit, compact centre set and compact positive radius set. -/
theorem ae_all_singular_compact_goodAnnulus_thresholds_of_zero_existence
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α : ℝ, ∀ μ : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
      ∀ (K : Set ℂ), IsCompact K → ∀ (R : Set ℝ), IsCompact R → R ⊆ Ioi 0 →
      ∀ b : ℝ, 0 < b → ∃ a : ℝ, 0 < a ∧
        ∀ z ∈ K, ∀ r ∈ R, IsGoodAnnulus μ r z a b := by
  filter_upwards [ae_all_singular_fine_support_of_zero_existence
    hgrowth P γ hγ hγ2 hC hcirc hG hE0] with ω hloc α μ hμ
  let : IsLocallyFiniteMeasure μ := hμ.isLocallyFiniteMeasure
  intro K hK R hR hRpos b hb
  exact uniform_goodAnnulus_threshold_on_compact_centers_radii μ (hloc α μ hμ) hK hR hRpos hb

end HarmonicBalls.Section6
