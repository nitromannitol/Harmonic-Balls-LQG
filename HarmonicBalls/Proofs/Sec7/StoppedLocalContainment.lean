import HarmonicBalls.Proofs.Sec7.StoppedLocalRegularization
import HarmonicBalls.Proofs.Sec5.RestrictedContainmentTest

/-! # Local containment at a random time

A regularized family is compactly contained at a positive time exactly when
it is compactly contained at some later rational time. This uses the
Hausdorff continuity explicitly required of the existing family.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

universe u

/-- Compact containment persists to a later time for a bounded family that
is Hausdorff continuous at the given time. -/
theorem exists_later_containment_of_hausdorffContinuous
    {A : ℝ → Set ℂ} {U : Set ℂ} (hU : IsOpen U) {t : ℝ} (ht : 0 < t)
    (hbound : Bornology.IsBounded (A t))
    (hcont : HausdorffContinuousOn A (Ioi 0))
    (hin : closure (A t) ⊆ U) :
    ∃ s : ℝ, t < s ∧ closure (A s) ⊆ U := by
  have hK : IsCompact (closure (A t)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hbound.closure
  obtain ⟨ε, hε, hεsub⟩ := hK.exists_thickening_subset_open hU hin
  have hnear := (hcont t ht (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)).filter_mono
    (nhdsWithin_mono t (Ioi_subset_Ioi ht.le))
  have hgt : ∀ᶠ s in 𝓝[>] t, t < s := self_mem_nhdsWithin
  obtain ⟨s, hst, hdist⟩ := (hgt.and hnear).exists
  refine ⟨s, hst, ?_⟩
  intro x hx
  apply hεsub
  have hdist' : hausdorffEDist (closure (A s)) (A t) < ENNReal.ofReal ε := by
    simpa only [hausdorffEDist_closure_left] using hdist
  obtain ⟨y, hy, hxy⟩ := exists_edist_lt_of_hausdorffEDist_lt hx hdist'
  apply mem_thickening_iff.2
  refine ⟨y, subset_closure hy, ?_⟩
  rw [edist_dist] at hxy
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp hxy

/-- A field-local containment event and a field-local stopped family member
at any positive field-measurable time. The construction uses the continuity
of the assumed regularized family, including no continuity assertion about
the original disc cluster after boundary contact. -/
theorem exists_fieldLocal_stopped_containment_and_family
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z)
    (z : U) (τ : Ω → Ioi (0 : ℝ))
    (hτ : Measurable[fieldSigmaAlgebra α₀ hC U] τ) :
    ∃ E : Set Ω, ∃ F : Ω → Set ℂ,
      MeasurableSet[fieldSigmaAlgebra α₀ hC U] E ∧
      Measurable[fieldSigmaAlgebra α₀ hC U] F ∧
      ∀ᵐ ω ∂P, (ω ∈ E ↔ closure (Λ ω z (τ ω)) ⊆ U) ∧
        (ω ∈ E → F ω = Λ ω z (τ ω)) := by
  classical
  obtain ⟨G, hG, hGeq⟩ := exists_local_lqg_bounded_compactContainmentFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc hU hUb hΛ
  obtain ⟨F, hF, hFeq⟩ := exists_fieldLocal_stopped_regularizedFamily_of_fullSupport
    hI2 hfull hγ hγ2 hα hGFF hμ hloc hU hUb hΛ z τ hτ
  let Q := {q : ℚ // 0 < (q : ℝ)}
  let E : Set Ω := {ω | ∃ q : Q, (τ ω : ℝ) < q ∧ G ω (z, ⟨q, q.property⟩)}
  have hE : MeasurableSet[fieldSigmaAlgebra α₀ hC U] E := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    apply measurableSet_setOfPred.mpr
    apply Measurable.exists
    intro q
    apply Measurable.and
    · exact measurableSet_setOfPred.mp
        (measurableSet_lt (measurable_subtype_coe.comp hτ) measurable_const)
    · exact (measurable_pi_apply (z, (⟨(q : ℚ), q.property⟩ : Ioi (0 : ℝ)))).comp hG
  refine ⟨E, F, hE, hF, ?_⟩
  filter_upwards [hGeq, hFeq, hΛ] with ω heq hFω hfamily
  have hevent : ω ∈ E ↔ closure (Λ ω z (τ ω)) ⊆ U := by
    constructor
    · rintro ⟨q, htq, hq⟩
      have hqU := (heq (z, ⟨q, q.property⟩)).mp hq
      exact (closure_mono ((hfamily z).1.monotoneOn (τ ω).property q.property htq.le)).trans hqU
    · intro hin
      obtain ⟨s, hts, hs⟩ := exists_later_containment_of_hausdorffContinuous hU
        (τ ω).property ((hfamily z).1.isBounded _ (τ ω).property)
        (hfamily z).1.hausdorffContinuousOn hin
      obtain ⟨q, htq, hqs⟩ := exists_rat_btwn hts
      let q' : Q := ⟨q, lt_trans (τ ω).property htq⟩
      have hqU := (closure_mono ((hfamily z).1.monotoneOn q'.property
        (lt_trans (τ ω).property hts) hqs.le)).trans hs
      exact ⟨q', htq, (heq (z, ⟨q', q'.property⟩)).mpr hqU⟩
  exact ⟨hevent, fun h => hFω (hevent.mp h)⟩

#print axioms exists_later_containment_of_hausdorffContinuous
#print axioms exists_fieldLocal_stopped_containment_and_family

end HarmonicBalls
