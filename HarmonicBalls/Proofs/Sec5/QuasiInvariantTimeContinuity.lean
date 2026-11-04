import HarmonicBalls.Proofs.Sec5.CountableContinuityExceptions
import Mathlib.MeasureTheory.Measure.Prod

/-! # Time rescaling and fixed-time continuity

The abstract criterion records the measure-theoretic step. Applying it to
LQG requires separate proofs of the stated measurability and quasi-invariance
properties. -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped Pointwise

/-- A jointly measurable random set of countable time sections has no fixed
positive-time atom when a quasi-invariant rescaling transports exceptions. -/
theorem ae_not_mem_of_countable_time_sections_and_quasiInvariant_scaling
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (E : Set (Ω × ℝ)) (hE : MeasurableSet E)
    (hcount : ∀ᵐ ω ∂P, {s : ℝ | (ω, s) ∈ E}.Countable)
    (T : ℝ → Ω → Ω)
    (hquasi : ∀ c : ℝ, 0 < c → Measure.QuasiMeasurePreserving (T c) P P)
    (htransport : ∀ c : ℝ, 0 < c → ∀ᵐ ω ∂P, ∀ t : ℝ,
      (ω, t) ∈ E → (T c ω, c * t) ∈ E)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, (ω, t) ∉ E := by
  have hinj : Function.Injective (fun c : ℝ => c * t) := by
    intro a b hab
    exact mul_right_cancel₀ (ne_of_gt ht) hab
  have hsections : ∀ᵐ ω ∂P, ∀ᵐ c : ℝ ∂volume, (ω, c * t) ∉ E := by
    filter_upwards [hcount] with ω hω
    have hc : {c : ℝ | (ω, c * t) ∈ E}.Countable := hω.preimage hinj
    apply ae_iff.mpr
    simpa only [not_not] using hc.measure_zero volume
  have hmeas : MeasurableSet {p : Ω × ℝ | (p.1, p.2 * t) ∉ E} := by
    exact (hE.preimage (measurable_fst.prodMk (measurable_snd.mul_const t))).compl
  have hsections' : ∀ᵐ c : ℝ ∂volume, ∀ᵐ ω ∂P, (ω, c * t) ∉ E :=
    (Measure.ae_ae_comm hmeas).mp hsections
  obtain ⟨c, hc, hgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (μ := volume) (s := Ioi (0 : ℝ)) (ne_of_gt (Measure.measure_Ioi_pos (μ := volume) (0 : ℝ)))
    (ae_restrict_of_ae hsections')
  filter_upwards [(hquasi c hc).ae hgood, htransport c hc] with ω hgood' htrans
  exact fun hbad => hgood' (htrans t hbad)

/-- Right continuity is transported through a positive time rescaling. -/
theorem right_continuity_of_time_rescaling
    {F G : ℝ → Set ℂ} {c t : ℝ} (hc : 0 < c) (ht : 0 < t)
    (hscale : ∀ s : ℝ, 0 < s → G (c * s) = F s)
    (hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Icc (c * t) (c * t + δ), closure (G s) ⊆ G (c * t) + ball (0 : ℂ) ε) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Icc t (t + δ), closure (F s) ⊆ F t + ball (0 : ℂ) ε := by
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hcont ε hε
  refine ⟨δ / c, div_pos hδ hc, ?_⟩
  intro s hs
  have hspos : 0 < s := ht.trans_le hs.1
  have hs' : c * s ∈ Icc (c * t) (c * t + δ) := by
    constructor
    · exact mul_le_mul_of_nonneg_left hs.1 hc.le
    · have := mul_le_mul_of_nonneg_left hs.2 hc.le
      have hdiv : c * (δ / c) = δ := mul_div_cancel₀ δ hc.ne'
      nlinarith
  simpa only [hscale s hspos, hscale t ht] using hbound (c * s) hs'

/-- Under joint measurability and a quasi-invariant time-rescaling action,
a monotone family of subsets of the unit disc is right-continuous at each
fixed positive time almost surely. -/
theorem ae_right_continuous_at_fixed_time_of_quasiInvariant_scaling
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (F : Ω → ℝ → Set ℂ)
    (hmono : ∀ᵐ ω ∂P, ∀ s s', 0 < s → s ≤ s' → F ω s ⊆ F ω s')
    (hbound : ∀ᵐ ω ∂P, ∀ s, 0 < s → F ω s ⊆ ball (0 : ℂ) 1)
    (hmeas : MeasurableSet {p : Ω × ℝ | 0 < p.2 ∧
      ¬ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s ∈ Icc p.2 (p.2 + δ), closure (F p.1 s) ⊆ F p.1 p.2 + ball (0 : ℂ) ε})
    (T : ℝ → Ω → Ω)
    (hquasi : ∀ c : ℝ, 0 < c → Measure.QuasiMeasurePreserving (T c) P P)
    (hscale : ∀ c : ℝ, 0 < c → ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s →
      F (T c ω) (c * s) = F ω s)
    {t : ℝ} (ht : 0 < t) : ∀ᵐ ω ∂P,
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s ∈ Icc t (t + δ), closure (F ω s) ⊆ F ω t + ball (0 : ℂ) ε := by
  let E : Set (Ω × ℝ) := {p | 0 < p.2 ∧
      ¬ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s ∈ Icc p.2 (p.2 + δ), closure (F p.1 s) ⊆ F p.1 p.2 + ball (0 : ℂ) ε}
  have hcount : ∀ᵐ ω ∂P, {s : ℝ | (ω, s) ∈ E}.Countable := by
    filter_upwards [hmono, hbound] with ω hm hb
    exact countable_not_rightContinuous_of_monotone hm hb
  have htransport : ∀ c : ℝ, 0 < c → ∀ᵐ ω ∂P, ∀ s : ℝ,
      (ω, s) ∈ E → (T c ω, c * s) ∈ E := by
    intro c hc
    filter_upwards [hscale c hc] with ω hs s hbad
    refine ⟨mul_pos hc hbad.1, ?_⟩
    intro hcont
    exact hbad.2 (right_continuity_of_time_rescaling hc hbad.1 hs hcont)
  have hgood := ae_not_mem_of_countable_time_sections_and_quasiInvariant_scaling
    P E hmeas hcount T hquasi htransport ht
  filter_upwards [hgood] with ω hω
  by_contra hfail
  exact hω ⟨ht, hfail⟩

#print axioms ae_not_mem_of_countable_time_sections_and_quasiInvariant_scaling
#print axioms right_continuity_of_time_rescaling
#print axioms ae_right_continuous_at_fixed_time_of_quasiInvariant_scaling

end HarmonicBalls
