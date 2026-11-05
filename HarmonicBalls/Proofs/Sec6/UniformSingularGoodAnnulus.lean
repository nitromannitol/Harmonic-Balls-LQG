import HarmonicBalls.Proofs.Sec6.CompactUniformCountableProbability
import HarmonicBalls.Proofs.Sec6.SingularWeight
import HarmonicBalls.Proofs.Sec6.SimultaneousPrevalenceZeroExistence

/-! # Good annuli for bounded singularity strengths

The underlying fine-support argument uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The zero-strength existence
input is staged pending source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

universe u

/-- On an admissible annulus, a singular power weight transfers the
whole-plane good-annulus condition with a controlled threshold loss. -/
theorem isGoodAnnulus_of_singular_weight
    {μ ν : Measure ℂ} {r e a b : ℝ} {z : ℂ} (hr : 0 < r)
    (hd : r / 100 ≤ infDist (0 : ℂ) (annulus z (3 * r) (5 * r)))
    (hμ : μ.restrict {0}ᶜ =
      (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ)
    (hg : IsGoodAnnulus ν r z a b) :
    IsGoodAnnulus μ r z (a / ((1001 : ℝ) ^ |e|) ^ 2) b := by
  obtain ⟨p, hp⟩ := admissible_annulus_nonempty (z := z) hr
  let t : ℝ := (1001 : ℝ) ^ |e|
  let c : ℝ≥0∞ := ENNReal.ofReal (‖p‖ ^ e / t)
  have ht : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
  have hp0 : 0 < ‖p‖ := (norm_le_of_mem_admissible_annulus hr hd hp hp).1
  have hc : 0 < ‖p‖ ^ e / t := div_pos (Real.rpow_pos_of_pos hp0 e) ht
  have hsub : annulus z (3 * r) (5 * r) ⊆ ({0} : Set ℂ)ᶜ := by
    intro x hx h0
    have hx0 := (norm_le_of_mem_admissible_annulus hr hd hx hp).1
    have : x = 0 := by simpa using h0
    simp [this] at hx0
  have hrestrict : μ.restrict (annulus z (3 * r) (5 * r)) =
      (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict (annulus z (3 * r) (5 * r)) := by
    rw [← Measure.restrict_restrict_of_subset hsub, hμ, Measure.restrict_restrict_of_subset hsub]
  apply isGoodAnnulus_of_withDensity_bounds (c := c)
    (ENNReal.ofReal_ne_zero_iff.2 hc) ENNReal.ofReal_ne_top (sq_pos_of_pos ht) hrestrict _ hg
  intro x hx
  have hxp := rpow_norm_le_of_mem_admissible_annulus (e := e) hr hd hx hp
  have hpx := rpow_norm_le_of_mem_admissible_annulus (e := e) hr hd hp hx
  constructor
  · apply ENNReal.ofReal_le_ofReal
    apply (div_le_iff₀ ht).2
    simpa [t, mul_comm] using hpx
  · rw [← ENNReal.ofReal_mul (sq_nonneg t)]
    apply ENNReal.ofReal_le_ofReal
    have hId : t ^ 2 * (‖p‖ ^ e / t) = t * ‖p‖ ^ e := by field_simp
    change ‖x‖ ^ e ≤ t * ‖p‖ ^ e at hxp
    simpa only [hId] using hxp

/-- A single loss works for all singular power exponents of bounded absolute
value. -/
theorem isGoodAnnulus_of_bounded_singular_weight
    {μ ν : Measure ℂ} {r e a b E : ℝ} {z : ℂ} (hr : 0 < r)
    (hd : r / 100 ≤ infDist (0 : ℂ) (annulus z (3 * r) (5 * r)))
    (hμ : μ.restrict {0}ᶜ =
      (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ)
    (ha : 0 ≤ a) (he : |e| ≤ E) (hg : IsGoodAnnulus ν r z a b) :
    IsGoodAnnulus μ r z (a / ((1001 : ℝ) ^ E) ^ 2) b := by
  have ht : (1001 : ℝ) ^ |e| ≤ (1001 : ℝ) ^ E :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) he
  have hsq : ((1001 : ℝ) ^ |e|) ^ 2 ≤ ((1001 : ℝ) ^ E) ^ 2 :=
    pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) ht 2
  apply isGoodAnnulus_mono_mass (isGoodAnnulus_of_singular_weight hr hd hμ hg)
  exact div_le_div_of_nonneg_left ha (sq_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _)) hsq

/-- On any countable family of admissible annuli in compact parameter sets,
one threshold controls all existing singular limits of bounded strength. -/
theorem exists_uniform_singular_goodAnnulus_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc)
    {K : Set ℂ} (hK : IsCompact K) {R : Set ℝ} (hR : IsCompact R) (hRpos : R ⊆ Ioi 0)
    {b E : ℝ} (hb : 0 < b) (hE : 0 ≤ E) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (z : ℕ → ℂ) (r : ℕ → ℝ),
      (∀ i, z i ∈ K) → (∀ i, r i ∈ R) →
      (∀ i, r i / 100 ≤ infDist (0 : ℂ) (annulus (z i) (3 * r i) (5 * r i))) →
      P {ω | ∃ (i : ℕ) (α : ℝ) (μ : Measure ℂ), |γ * α| ≤ E ∧
        IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ ∧
        ¬ IsGoodAnnulus μ (r i) (z i) a b} ≤ δ := by
  let := h.isProbabilityMeasure
  obtain ⟨μ₀, hμ₀, hrepr⟩ :=
    exists_ae_singular_limits_restrict_eq_weight_of_zero_existence P γ hγ hγ2 hC hcirc h hE0
  obtain ⟨a, ha, hbound⟩ := exists_compact_uniform_countable_goodAnnulus_probability
    hgrowth hγ hγ2 h hμ₀ hK hR hRpos hb hδ
  let t : ℝ := ((1001 : ℝ) ^ E) ^ 2
  have ht : 0 < t := sq_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _)
  have ht1 : 1 ≤ t := by
    have hbase : 1 ≤ (1001 : ℝ) ^ E := Real.one_le_rpow (by norm_num) hE
    dsimp only [t]
    nlinarith
  refine ⟨a / t, ⟨div_pos ha.1 ht, (div_le_self ha.1.le ht1).trans_lt ha.2⟩, ?_⟩
  intro z r hz hr hd
  apply (measure_mono_ae ?_).trans (hbound z r hz hr)
  filter_upwards [hrepr] with ω hreprω hbad
  obtain ⟨i, α, μ, hα, hlim, hbad⟩ := hbad
  refine ⟨i, ?_⟩
  intro hgood
  apply hbad
  apply isGoodAnnulus_of_bounded_singular_weight (hRpos (hr i)) (hd i)
    (hreprω α μ hlim) ha.1.le ?_ hgood
  simpa only [abs_neg] using hα

/-- The singularity strength and the index may both depend arbitrarily on
the field, provided the strengths are almost surely bounded. -/
theorem exists_uniform_selected_singular_goodAnnulus_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc)
    {K : Set ℂ} (hK : IsCompact K) {R : Set ℝ} (hR : IsCompact R) (hRpos : R ⊆ Ioi 0)
    {b E : ℝ} (hb : 0 < b) (hE : 0 ≤ E) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (z : ℕ → ℂ) (r : ℕ → ℝ),
      (∀ i, z i ∈ K) → (∀ i, r i ∈ R) →
      (∀ i, r i / 100 ≤ infDist (0 : ℂ) (annulus (z i) (3 * r i) (5 * r i))) →
      ∀ (choice : Ω → ℕ) (α : Ω → ℝ) (μ : Ω → Measure ℂ),
        (∀ᵐ ω ∂P, |γ * α ω| ≤ E ∧ IsLQGLimit γ (fieldCircleAverage (α ω) (hcirc ω)) (μ ω)) →
        P {ω | ¬ IsGoodAnnulus (μ ω) (r (choice ω)) (z (choice ω)) a b} ≤ δ := by
  obtain ⟨a, ha, hbound⟩ := exists_uniform_singular_goodAnnulus_probability
    hgrowth hγ hγ2 h hE0 hK hR hRpos hb hE hδ
  refine ⟨a, ha, ?_⟩
  intro z r hz hr hd choice α μ hlim
  apply (measure_mono_ae ?_).trans (hbound z r hz hr hd)
  filter_upwards [hlim] with ω hω hbad
  exact ⟨choice ω, α ω, μ ω, hω.1, hω.2, hbad⟩

end HarmonicBalls.Section6
