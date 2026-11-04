import HarmonicBalls.Proofs.Sec5.FieldLocalExactHorizon
import HarmonicBalls.Proofs.Sec5.UniformContainment

/-! # Exact uniform containment at arbitrary horizons -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- Uniform compact containment in the unit disc before a given time. -/
def unitClusterContainmentUntil (T : ℝ) : Set (Measure ℂ) :=
  {ν | ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t ∈ Ioo (0 : ℝ) T,
    closure (cluster ν 1 z t) ⊆ ball 0 1}

/-- Uniform containment failure has an analytic representation in the
continuous Green potential, for every real horizon. -/
theorem exists_analyticSet_unitClusterContainmentUntil_compl
    (Q : Measure ℂ → C(closedBall (0 : ℂ) 1, ℝ))
    (hQeq : ∀ ν, ContinuousOn (greenPotentialBall ν 1) (closedBall 0 1) →
      ∀ y, Q ν y = greenPotentialBall ν 1 y) (T : ℝ) :
    ∃ S : Set C(closedBall (0 : ℂ) 1, ℝ), AnalyticSet S ∧
      ∀ ν : Measure ℂ, IsLocallyFiniteMeasure ν →
        (∃ βm βp, VolumeGrowth ν 1 βm βp) →
        (Q ν ∈ S ↔ ν ∉ unitClusterContainmentUntil T) := by
  let J := {q : ℚ // (q : ℝ) ∈ Ioo (0 : ℝ) T}
  choose S hS hgood using fun q : J =>
    exists_analyticSet_cluster_boundary_contact_potential q.property.1 Q hQeq
  refine ⟨⋃ q : J, S q, AnalyticSet.iUnion hS, ?_⟩
  intro ν hloc hvol
  have hmono : ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ s t : ℝ, 0 < s → s ≤ t →
      cluster ν 1 z s ⊆ cluster ν 1 z t := by
    intro z hz s t hs hst
    obtain ⟨βm, βp, hv⟩ := hvol
    exact cluster_subset_of_general obstacleMonotoneGeneral_holds obstacleCompatibilityShiftStep_holds
      hloc zero_lt_one hv (ball_subset_ball (by norm_num) hz) hs hst
  simp only [mem_iUnion]
  constructor
  · rintro ⟨q, hq⟩ hc
    obtain ⟨z, hz⟩ := (hgood q ν hloc hvol).mp hq
    exact hz (hc z z.property q q.property)
  · intro hc
    change ¬ (∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t ∈ Ioo (0 : ℝ) T,
      closure (cluster ν 1 z t) ⊆ ball 0 1) at hc
    push Not at hc
    obtain ⟨z, hz, t, ht, hfail⟩ := hc
    obtain ⟨q, htq, hqT⟩ := exists_rat_btwn ht.2
    let q' : J := ⟨q, ⟨lt_trans ht.1 htq, hqT⟩⟩
    refine ⟨q', (hgood q' ν hloc hvol).mpr ⟨⟨z, hz⟩, ?_⟩⟩
    intro hcontained
    exact hfail ((closure_mono (hmono z hz t q ht.1 htq.le)).trans hcontained)

/-- All rational containment horizons admit field-local representatives,
simultaneously almost surely. -/
theorem exists_local_lqg_rational_containment_events
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) :
    ∃ E : ℚ → Set Ω, (∀ q, MeasurableSet[fieldSigmaAlgebra α₀ hC (ball 0 1)] (E q)) ∧
      ∀ᵐ ω ∂P, ∀ q : ℚ, μ ω ∈ unitClusterContainmentUntil q ↔ ω ∈ E q := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (greenPotentialBall (μ ω) 1) (closedBall 0 1) := by
    filter_upwards [hae] with ω hω
    exact greenPotentialBallContinuousStep_holds _ hω.1 1 βm βp zero_lt_one (hω.2 1 zero_lt_one)
  obtain ⟨Qloc, hQloc, hQlocEq⟩ := exists_local_lqg_greenPotentialBall_continuous_representative
    hγ hγ2 hα hGFF hμ hloc zero_lt_one hcont
  have hQambient : Measurable Qloc := hQloc.mono (hGFF.fieldSigmaAlgebra_le α₀ (ball 0 1)) le_rfl
  obtain ⟨Q, _hQ, hQeq⟩ := exists_measurable_greenPotentialBall_decoder zero_lt_one
  choose S hSa hScorrect using fun q : ℚ =>
    exists_analyticSet_unitClusterContainmentUntil_compl Q hQeq q
  choose B hBS hBm hBae using fun q : ℚ =>
    (AnalyticSet.nullMeasurableSet_of_finite (Measure.map Qloc P) (hSa q)).exists_measurable_subset_ae_eq
  refine ⟨fun q => (Qloc ⁻¹' B q)ᶜ, fun q => (hQloc (hBm q)).compl, ?_⟩
  have hpre : ∀ q, (Qloc ⁻¹' B q) =ᵐ[P] (Qloc ⁻¹' S q) :=
    fun q => (hQambient.quasiMeasurePreserving P).preimage_ae_eq (hBae q)
  filter_upwards [hae, hcont, hQlocEq, ae_all_iff.mpr hpre] with ω hω hc hq hb
  have heq : Qloc ω = Q (μ ω) := by
    apply ContinuousMap.ext
    intro x
    exact (hq x).trans (hQeq (μ ω) hc x).symm
  intro q
  have hs := hScorrect q (μ ω) hω.1 ⟨βm, βp, hω.2 1 zero_lt_one⟩
  change (μ ω ∈ unitClusterContainmentUntil q) ↔ Qloc ω ∉ B q
  have hb' : (Qloc ω ∈ B q) ↔ Qloc ω ∈ S q := propext_iff.mp (hb q)
  rw [heq] at hb' ⊢
  tauto

/-- The exact uniform containment threshold is field-local. Its value may be
infinite; the strict sublevel characterization is valid for every positive time. -/
theorem exists_fieldLocal_exact_containment_threshold
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) :
    ∃ H : Ω → ℝ≥0∞, Measurable[fieldSigmaAlgebra α₀ hC (ball 0 1)] H ∧
      ∀ᵐ ω ∂P, 0 < H ω ∧ ∀ t : ℝ, 0 < t →
        (ENNReal.ofReal t < H ω ↔
          ∃ T : ℝ, t < T ∧ μ ω ∈ unitClusterContainmentUntil T) := by
  classical
  obtain ⟨E, hE, heq⟩ := exists_local_lqg_rational_containment_events
    hI2 hγ hγ2 hα hGFF hμ hloc
  obtain ⟨H₀, _, hH₀⟩ := exists_fieldLocal_exact_dyadic_containment_horizon
    hI2 h71 hγ hγ2 hα hGFF hμ hloc
  let H : Ω → ℝ≥0∞ := fun ω => ⨆ q : ℚ,
    if 0 < (q : ℝ) ∧ ω ∈ E q then ENNReal.ofReal q else 0
  have hH : Measurable[fieldSigmaAlgebra α₀ hC (ball 0 1)] H := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC (ball 0 1)
    dsimp only [H]
    apply Measurable.iSup
    intro q
    apply Measurable.ite _ measurable_const measurable_const
    by_cases hq : 0 < (q : ℝ)
    · simpa [hq] using hE q
    · simp [hq]
  refine ⟨H, hH, ?_⟩
  filter_upwards [heq, hH₀] with ω heqω h₀
  have hle : ∀ q : ℚ, 0 < (q : ℝ) → μ ω ∈ unitClusterContainmentUntil q →
      ENNReal.ofReal q ≤ H ω := by
    intro q hq hc
    exact le_iSup_of_le q (by simp [hq, (heqω q).mp hc])
  have hpos : 0 < H ω := by
    obtain ⟨q, hq, hqH⟩ := exists_rat_btwn h₀.1
    have hc : μ ω ∈ unitClusterContainmentUntil q := by
      intro z hz t ht
      exact h₀.2.2.1 z hz t ⟨ht.1, lt_trans ht.2 hqH⟩
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hq) (hle q hq hc)
  refine ⟨hpos, ?_⟩
  intro t ht
  constructor
  · intro htH
    change ENNReal.ofReal t < ⨆ q : ℚ,
      if 0 < (q : ℝ) ∧ ω ∈ E q then ENNReal.ofReal q else 0 at htH
    obtain ⟨q, hq⟩ := lt_iSup_iff.mp htH
    by_cases hqgood : 0 < (q : ℝ) ∧ ω ∈ E q
    · rw [ite_eq_left hqgood] at hq
      have htq : t < (q : ℝ) := (ENNReal.ofReal_lt_ofReal_iff hqgood.1).mp hq
      exact ⟨q, htq, (heqω q).mpr hqgood.2⟩
    · rw [ite_eq_right hqgood] at hq
      exact False.elim ((not_lt_of_ge bot_le) hq)
  · rintro ⟨T, htT, hc⟩
    obtain ⟨q, htq, hqT⟩ := exists_rat_btwn htT
    have hq : 0 < (q : ℝ) := lt_trans ht htq
    have hcq : μ ω ∈ unitClusterContainmentUntil q := by
      intro z hz s hs
      exact hc z hz s ⟨hs.1, lt_trans hs.2 hqT⟩
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hq).mpr htq) (hle q hq hcq)

end HarmonicBalls
