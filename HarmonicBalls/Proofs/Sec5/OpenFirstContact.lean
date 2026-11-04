import HarmonicBalls.Proofs.Sec5.OpenStoppedFamilyLocality

/-! # Contact of regularized families with open-domain boundaries -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

universe u

/-- Hausdorff continuity preserves containment in the closure of an open set
at the endpoint of an increasing interval of containment. -/
theorem closure_subset_closure_of_hausdorffContinuousOn_before
    {A : ℝ → Set ℂ} {U : Set ℂ} {T : ℝ} (hT : 0 < T)
    (hcont : HausdorffContinuousOn A (Ioi 0))
    (hbefore : ∀ t ∈ Ioo (0 : ℝ) T, closure (A t) ⊆ U) :
    closure (A T) ⊆ closure U := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hnear : ∀ᶠ s in 𝓝 T, hausdorffEDist (A T) (A s) < ENNReal.ofReal ε := by
    have h := hcont T hT (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
    rw [nhdsWithin_eq_nhds.mpr (isOpen_Ioi.mem_nhds hT)] at h
    filter_upwards [h] with s hs
    simpa only [hausdorffEDist_comm] using hs
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hnear
  let s := T - min T δ / 2
  have hs0 : 0 < s := by
    have h := min_le_left T δ
    dsimp [s]
    linarith
  have hsT : s < T := by dsimp [s]; have := lt_min hT hδ; linarith
  have hsnear : dist s T < δ := by
    dsimp [s, Real.dist_eq]
    rw [sub_sub_cancel_left, abs_neg, abs_of_pos (half_pos (lt_min hT hδ))]
    have h := min_le_right T δ
    linarith
  have hdist : hausdorffEDist (closure (A T)) (closure (A s)) < ENNReal.ofReal ε := by
    simpa only [hausdorffEDist_closure] using hδbound hsnear
  obtain ⟨y, hy, hxy⟩ := exists_edist_lt_of_hausdorffEDist_lt hx hdist
  exact ⟨y, hbefore s ⟨hs0, hsT⟩ hy,
    by simpa only [edist_dist, ENNReal.ofReal_lt_ofReal_iff hε, dist_comm] using hxy⟩

/-- A finite positive exact containment horizon is a boundary-contact time for
any Hausdorff-continuous family. -/
theorem boundary_contact_of_exact_containment_horizon
    {A : ℝ → Set ℂ} {U : Set ℂ} (hU : IsOpen U) {H : ℝ≥0∞}
    (hpos : 0 < H) (hfin : H < ⊤) (hcont : HausdorffContinuousOn A (Ioi 0))
    (hchar : ∀ t : ℝ, 0 < t → (ENNReal.ofReal t < H ↔ closure (A t) ⊆ U)) :
    (closure (A H.toReal) ∩ frontier U).Nonempty := by
  have hT : 0 < H.toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hbefore : ∀ t ∈ Ioo (0 : ℝ) H.toReal, closure (A t) ⊆ U := by
    intro t ht
    apply (hchar t ht.1).mp
    rw [← ENNReal.ofReal_toReal hfin.ne]
    exact (ENNReal.ofReal_lt_ofReal_iff hT).mpr ht.2
  have hcl : closure (A H.toReal) ⊆ closure U :=
    closure_subset_closure_of_hausdorffContinuousOn_before hT hcont hbefore
  have hnot : ¬ closure (A H.toReal) ⊆ U := by
    intro hsub
    have hlt := (hchar H.toReal hT).mpr hsub
    rw [ENNReal.ofReal_toReal hfin.ne] at hlt
    exact (lt_irrefl _ hlt)
  obtain ⟨x, hx, hxu⟩ := Set.not_subset.mp hnot
  refine ⟨x, hx, ?_⟩
  rw [frontier, hU.interior_eq]
  exact ⟨hcl hx, hxu⟩

/-- In any open domain, the field-local containment horizon is a boundary
contact time whenever it is finite and positive. -/
theorem exists_fieldLocal_open_horizons_with_conditional_boundary_contact
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ H : Ω → (U → ℝ≥0∞), Measurable[fieldSigmaAlgebra α₀ hC U] H ∧
      ∀ᵐ ω ∂P, ∀ z : U,
        (∀ t : ℝ, 0 < t →
          (ENNReal.ofReal t < H ω z ↔ closure (Λ ω z t) ⊆ U)) ∧
        (0 < H ω z → H ω z < ⊤ →
          (closure (Λ ω z (H ω z).toReal) ∩ frontier U).Nonempty) := by
  obtain ⟨H, hH, hchar⟩ := exists_fieldLocal_open_exact_containment_horizons
    hI2 hγ hγ2 hα hGFF hμ hloc hU hΛ
  refine ⟨H, hH, ?_⟩
  filter_upwards [hchar, hΛ] with ω hcharω hΛω
  intro z
  exact ⟨hcharω z, fun hpos hfin => boundary_contact_of_exact_containment_horizon
    hU hpos hfin (hΛω z).1.hausdorffContinuousOn (hcharω z)⟩

/-- On a bounded open domain, a field-local containment horizon is bounded by
the domain mass. At a positive horizon, the regularized family reaches the
boundary. The field locality input is proposed and awaits source review. -/
theorem exists_fieldLocal_open_horizons_with_boundary_contact
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ H : Ω → (U → ℝ≥0∞), Measurable[fieldSigmaAlgebra α₀ hC U] H ∧
      ∀ᵐ ω ∂P, ∀ z : U, H ω z ≤ μ ω U ∧ H ω z < ⊤ ∧
        (∀ t : ℝ, 0 < t →
          (ENNReal.ofReal t < H ω z ↔ closure (Λ ω z t) ⊆ U)) ∧
        (0 < H ω z →
          (closure (Λ ω z (H ω z).toReal) ∩ frontier U).Nonempty) := by
  obtain ⟨H, hH, hchar⟩ := exists_fieldLocal_open_exact_containment_horizons
    hI2 hγ hγ2 hα hGFF hμ hloc hU hΛ
  obtain ⟨r, hr⟩ := hUb.subset_ball (0 : ℂ)
  refine ⟨H, hH, ?_⟩
  filter_upwards [hchar, hΛ, hμ] with ω hcharω hΛω hμω
  let : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
  have hμfin : μ ω U < ⊤ := lt_of_le_of_lt (measure_mono hr) measure_ball_lt_top
  intro z
  have hbound : H ω z ≤ μ ω U := by
    by_contra hn
    obtain ⟨q, hqlo, hqhi⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge hn)
    have hqpos : 0 < (q : ℝ) := by
      have hqpos' : 0 < (q : ℝ≥0∞) := lt_of_le_of_lt bot_le hqlo
      exact_mod_cast hqpos'
    have hqhi' : ENNReal.ofReal (q : ℝ) < H ω z := by simpa using hqhi
    have hsub := (hcharω z q hqpos).mp hqhi'
    have hmass : μ ω (Λ ω z q) = ENNReal.ofReal q := (hΛω z).1.measure_eq q hqpos
    have hle : ENNReal.ofReal (q : ℝ) ≤ μ ω U := by
      rw [← hmass]
      exact measure_mono (subset_closure.trans hsub)
    have hlo : μ ω U < ENNReal.ofReal (q : ℝ) := by simpa using hqlo
    exact (not_lt_of_ge hle) hlo
  have hfin : H ω z < ⊤ := lt_of_le_of_lt hbound hμfin
  refine ⟨hbound, hfin, hcharω z, ?_⟩
  intro hpos
  exact boundary_contact_of_exact_containment_horizon hU hpos hfin
    (hΛω z).1.hausdorffContinuousOn (hcharω z)

end HarmonicBalls
