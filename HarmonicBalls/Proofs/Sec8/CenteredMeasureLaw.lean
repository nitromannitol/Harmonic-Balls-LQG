import HarmonicBalls.Proofs.Sec8.UniversalPhaseProbability
import HarmonicBalls.Proofs.Sec6.DiscPotentialTranslation

/-! # Measurable recentering of locally finite random measures -/

open MeasureTheory Filter Set

namespace HarmonicBalls

/-- Absolute continuity of subtype-valued laws follows from absolute
continuity of their pushforwards to the ambient measurable space. -/
theorem absolutelyContinuous_subtype_of_map
    {A : Type*} [MeasurableSpace A] {p : A → Prop}
    {μ ν : Measure {x // p x}}
    (h : μ.map Subtype.val ≪ ν.map Subtype.val) : μ ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  obtain ⟨t, ht, heq⟩ := MeasurableSpace.measurableSet_comap.mp hs
  have hν : (ν.map Subtype.val) t = 0 := by
    rw [Measure.map_apply measurable_subtype_coe ht, heq]
    exact hzero
  have hμ := h hν
  rwa [Measure.map_apply measurable_subtype_coe ht, heq] at hμ

/-- A random locally finite measure has a jointly measurable recentered
version which agrees simultaneously at every center almost surely. -/
theorem exists_jointlyMeasurable_centeredMeasure
    {Ω : Type*} [MeasurableSpace Ω] (S : Measure Ω) {μ : Ω → Measure ℂ}
    (hμ : AEMeasurable μ S) (hloc : ∀ᵐ ω ∂S, IsLocallyFiniteMeasure (μ ω)) :
    ∃ F : ℂ × Ω → {ν : Measure ℂ // IsLocallyFiniteMeasure ν}, Measurable F ∧
      ∀ᵐ ω ∂S, ∀ z : ℂ, (μ ω).map (fun v : ℂ => v - z) = (F (z, ω)).val := by
  obtain ⟨ν, hν, hνloc, heq⟩ := Section6.exists_measurable_locallyFinite_rep hμ hloc
  let F : ℂ × Ω → {ν : Measure ℂ // IsLocallyFiniteMeasure ν} := fun p =>
    ⟨(ν p.2).map (fun v : ℂ => v - p.1),
      Section6.isLocallyFiniteMeasure_map_sub_right (hνloc p.2) p.1⟩
  have hF : Measurable F := by
    apply Measurable.subtype_mk
    exact Section6.measurable_map_of_locallyFinite (hν.comp measurable_snd)
      (fun p => hνloc p.2) (measurable_snd.sub (measurable_fst.comp measurable_fst))
  refine ⟨F, hF, ?_⟩
  filter_upwards [heq] with ω hω z
  exact congrArg (fun m : Measure ℂ => m.map (fun v : ℂ => v - z)) hω

/-- A recentered ambient measure-law comparison implies the corresponding
comparison for locally finite-measure-valued versions. -/
theorem centeredSubtypeLaw_absolutelyContinuous_of_measureLaw
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (R : Measure Ω) (P : Measure Ξ) {μ : Ω → Measure ℂ} {ν : Ξ → Measure ℂ}
    (z : ℂ) (F : Ω → {m : Measure ℂ // IsLocallyFiniteMeasure m}) (hF : Measurable F)
    (U : Ξ → {m : Measure ℂ // IsLocallyFiniteMeasure m}) (hU : Measurable U)
    (hcenter : ∀ᵐ ω ∂(R), (μ ω).map (fun v : ℂ => v - z) = (F ω).val)
    (hUeq : ∀ᵐ ω ∂P, (U ω).val = ν ω)
    (hlaw : R.map (fun ω => (μ ω).map (fun v : ℂ => v - z)) ≪ P.map ν) :
    R.map F ≪ P.map U := by
  apply absolutelyContinuous_subtype_of_map
  rw [Measure.map_map measurable_subtype_coe hF,
    Measure.map_map measurable_subtype_coe hU]
  have heq₁ : R.map (Subtype.val ∘ F) =
      R.map (fun ω => (μ ω).map (fun v : ℂ => v - z)) := Measure.map_congr (by
        filter_upwards [hcenter] with ω hω
        exact hω.symm)
  have heq₂ : P.map (Subtype.val ∘ U) = P.map ν := Measure.map_congr hUeq
  rwa [heq₁, heq₂]

end HarmonicBalls
