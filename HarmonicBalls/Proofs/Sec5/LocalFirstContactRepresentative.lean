import HarmonicBalls.Proofs.Sec5.OpenHorizonPositivity
import HarmonicBalls.Proofs.Sec5.ClusterMeasurability

/-! # Field-local regularized family at first contact -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

universe u

/-- An increasing Hausdorff-continuous family is determined at a positive
 time, up to closure, by its earlier positive rational members. -/
theorem closure_eq_closure_iUnion_earlier_rat_of_hausdorffContinuousOn
    {A : ℝ → Set ℂ} {T : ℝ} (hT : 0 < T)
    (hmono : ∀ s, 0 < s → ∀ t, 0 < t → s ≤ t → A s ⊆ A t)
    (hcont : HausdorffContinuousOn A (Ioi 0)) :
    closure (A T) = closure (⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < T}, A q) := by
  let B := ⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < T}, A q
  have hsub : B ⊆ A T := by
    intro x hx
    obtain ⟨q, hq⟩ := mem_iUnion.mp hx
    exact hmono q q.property.1 T hT q.property.2.le hq
  apply Subset.antisymm
  · apply closure_minimal _ isClosed_closure
    intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hnear : ∀ᶠ s in 𝓝 T, hausdorffEDist (A T) (A s) < ENNReal.ofReal ε := by
      have h := hcont T hT (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
      rw [nhdsWithin_eq_nhds.mpr (isOpen_Ioi.mem_nhds hT)] at h
      filter_upwards [h] with s hs
      simpa only [hausdorffEDist_comm] using hs
    obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hnear
    have hmin : 0 < min T δ := lt_min hT hδ
    obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn (show T - min T δ / 2 < T by linarith)
    have hqpos : 0 < (q : ℝ) := by have := min_le_left T δ; linarith
    have hqnear : dist (q : ℝ) T < δ := by
      rw [Real.dist_eq, abs_of_neg (by linarith : (q : ℝ) - T < 0)]
      have := min_le_right T δ
      linarith
    obtain ⟨y, hy, hxy⟩ := exists_edist_lt_of_hausdorffEDist_lt hx (hδbound hqnear)
    exact ⟨y, mem_iUnion.mpr ⟨⟨q, hqpos, hqhi⟩, hy⟩,
      by simpa only [edist_dist, ENNReal.ofReal_lt_ofReal_iff hε, dist_comm] using hxy⟩
  · exact closure_mono hsub

/-- First-contact family members have a field-local representative on an
arbitrary open domain. The locality input is proposed and awaits source review.
The identification holds simultaneously for all centres with positive finite
contact horizon. -/
theorem exists_fieldLocal_open_firstContact_family
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ H : Ω → (U → ℝ≥0∞), ∃ C : Ω → (U → Set ℂ),
      Measurable[fieldSigmaAlgebra α₀ hC U] H ∧
      Measurable[fieldSigmaAlgebra α₀ hC U] C ∧
      ∀ᵐ ω ∂P, ∀ z : U,
        (∀ t : ℝ, 0 < t →
          (ENNReal.ofReal t < H ω z ↔ closure (Λ ω z t) ⊆ U)) ∧
        (0 < H ω z → H ω z < ⊤ →
          C ω z = Λ ω z (H ω z).toReal ∧
          (closure (Λ ω z (H ω z).toReal) ∩ frontier U).Nonempty) := by
  classical
  obtain ⟨H, hH, hchar⟩ := exists_fieldLocal_open_horizons_with_conditional_boundary_contact
    hI2 hγ hγ2 hα hGFF hμ hloc hU hΛ
  obtain ⟨E, G, hE, hG, heq⟩ := exists_local_lqg_open_stoppedFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc hU hΛ
  let Q := {q : ℚ // 0 < (q : ℝ)}
  let A : Ω → U → Set ℂ := fun ω z =>
    {x | ∃ q : Q, E ω (z, ⟨q, q.property⟩) ∧ x ∈ G ω (z, ⟨q, q.property⟩)}
  have hA : Measurable[fieldSigmaAlgebra α₀ hC U] A := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    apply Measurable.of_eval
    intro z
    apply Measurable.of_eval
    intro x
    change Measurable (fun ω => ∃ q : Q,
      E ω (z, ⟨q, q.property⟩) ∧ x ∈ G ω (z, ⟨q, q.property⟩))
    apply Measurable.exists
    intro q
    exact ((measurable_pi_apply (z, ⟨(q : ℚ), q.property⟩)).comp hE).and
      ((measurable_pi_apply x).comp
        ((measurable_pi_apply (z, ⟨(q : ℚ), q.property⟩)).comp hG))
  refine ⟨H, (fun ω z => denseSequenceRegularization (A ω z)), hH,
    measurable_denseSequenceRegularization_family.comp hA, ?_⟩
  filter_upwards [hchar, heq, hΛ] with ω hcharω heqω hΛω
  intro z
  refine ⟨(hcharω z).1, ?_⟩
  intro hpos hfin
  have hT : 0 < (H ω z).toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  let B := ⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < (H ω z).toReal}, Λ ω z q
  have hBopen : IsOpen B := isOpen_iUnion fun q =>
    ((hΛω z).1.isRegularOpen q q.property.1).isOpen
  have hEchar (q : Q) : E ω (z, ⟨q, q.property⟩) ↔ (q : ℝ) < (H ω z).toReal := by
    rw [(heqω _).1, ← (hcharω z).1 q q.property]
    constructor
    · intro hq
      apply (ENNReal.ofReal_lt_ofReal_iff hT).mp
      simpa only [ENNReal.ofReal_toReal hfin.ne] using hq
    · intro hq
      have h := (ENNReal.ofReal_lt_ofReal_iff hT).mpr hq
      simpa only [ENNReal.ofReal_toReal hfin.ne] using h
  have hAB : A ω z = B := by
    ext x
    change (∃ q : Q, E ω (z, ⟨q, q.property⟩) ∧ x ∈ G ω (z, ⟨q, q.property⟩)) ↔ x ∈ B
    simp only [B, mem_iUnion]
    constructor
    · rintro ⟨q, hq, hx⟩
      exact ⟨⟨q, q.property, (hEchar q).mp hq⟩, (heqω _).2.1 hq ▸ hx⟩
    · rintro ⟨q, hx⟩
      let q' : Q := ⟨q, q.property.1⟩
      have hq : E ω (z, ⟨q', q'.property⟩) := (hEchar q').mpr q.property.2
      exact ⟨q', hq, (heqω _).2.1 hq ▸ hx⟩
  have hcl := closure_eq_closure_iUnion_earlier_rat_of_hausdorffContinuousOn hT
    (fun s hs t ht hst => (hΛω z).1.monotoneOn hs ht hst)
    (hΛω z).1.hausdorffContinuousOn
  constructor
  · rw [hAB, denseSequenceRegularization_eq hBopen, ← hcl,
      (hΛω z).1.isRegularOpen _ hT]
  · exact (hcharω z).2 hpos hfin

/-- On a bounded open domain, the field determines the regularized family
at the positive finite boundary-contact horizon, simultaneously for all
centres. The locality, affine invariance and coordinate change inputs are
proposed and await source review. -/
theorem exists_fieldLocal_bounded_open_firstContact_family
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ H : Ω → (U → ℝ≥0∞), ∃ C : Ω → (U → Set ℂ),
      Measurable[fieldSigmaAlgebra α₀ hC U] H ∧
      Measurable[fieldSigmaAlgebra α₀ hC U] C ∧
      ∀ᵐ ω ∂P, ∀ z : U, 0 < H ω z ∧ H ω z ≤ μ ω U ∧ H ω z < ⊤ ∧
        (∀ t : ℝ, 0 < t →
          (ENNReal.ofReal t < H ω z ↔ closure (Λ ω z t) ⊆ U)) ∧
        C ω z = Λ ω z (H ω z).toReal ∧
        (closure (Λ ω z (H ω z).toReal) ∩ frontier U).Nonempty := by
  obtain ⟨H, C, hH, hCmeas, hchar⟩ := exists_fieldLocal_open_firstContact_family
    hI2 hγ hγ2 hα hGFF hμ hloc hU hΛ
  obtain ⟨r, hr⟩ := hUb.subset_ball (0 : ℂ)
  refine ⟨H, C, hH, hCmeas, ?_⟩
  filter_upwards [hchar, hΛ, hμ, ae_regularizedFamily_small_open_neighborhoods_all_centres
    hI2 h71 hAff hCC hγ hγ2 hα hGFF hμ hΛ] with ω hcharω hΛω hμω hsmall
  let : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
  have hμfin : μ ω U < ⊤ := lt_of_le_of_lt (measure_mono hr) measure_ball_lt_top
  intro z
  obtain ⟨t, ht, hsub⟩ := hsmall z U hU z.property
  have hpos : 0 < H ω z :=
    lt_trans (ENNReal.ofReal_pos.mpr ht) ((hcharω z).1 t ht |>.mpr hsub)
  have hbound : H ω z ≤ μ ω U := by
    by_contra hn
    obtain ⟨q, hqlo, hqhi⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge hn)
    have hqpos : 0 < (q : ℝ) := by
      have hqpos' : 0 < (q : ℝ≥0∞) := lt_of_le_of_lt bot_le hqlo
      exact_mod_cast hqpos'
    have hqhi' : ENNReal.ofReal (q : ℝ) < H ω z := by simpa using hqhi
    have hsub := (hcharω z).1 q hqpos |>.mp hqhi'
    have hmass : μ ω (Λ ω z q) = ENNReal.ofReal q := (hΛω z).1.measure_eq q hqpos
    have hle : ENNReal.ofReal (q : ℝ) ≤ μ ω U := by
      rw [← hmass]
      exact measure_mono (subset_closure.trans hsub)
    have hlo : μ ω U < ENNReal.ofReal (q : ℝ) := by simpa using hqlo
    exact (not_lt_of_ge hle) hlo
  have hfin : H ω z < ⊤ := lt_of_le_of_lt hbound hμfin
  exact ⟨hpos, hbound, hfin, (hcharω z).1, (hcharω z).2 hpos hfin⟩

end HarmonicBalls
