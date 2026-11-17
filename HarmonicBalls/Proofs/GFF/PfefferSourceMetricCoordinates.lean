import HarmonicBalls.Proofs.GFF.PfefferSourceAroundBridge
import HarmonicBalls.Proofs.GFF.PfefferSourceDistanceMeasurable
import HarmonicBalls.Proofs.GFF.MetricAnnulusScaleLaw

/-! # Open-infimum coordinates of the LQG metric

For a whole-plane GFF plus a random continuous function, the open-infimum
coordinates of its LQG metric are almost everywhere measurable. The Euclidean
topology condition supplies the continuity needed for countable approximation.
-/

namespace HarmonicBalls

open Set MeasureTheory
open scoped ENNReal

/-- A continuous distance has the same infimum on a set and a dense subset. -/
theorem sInf_ofReal_image_eq_iInf_of_dense {D : ℂ → ℂ → ℝ}
    (hD : Continuous fun p : ℂ × ℂ => D p.1 p.2)
    {U S : Set (ℂ × ℂ)} (hSU : S ⊆ U) (hUS : U ⊆ closure S) :
    sInf (Set.image (fun p : ℂ × ℂ => ENNReal.ofReal (D p.1 p.2)) U) =
      ⨅ p ∈ S, ENNReal.ofReal (D p.1 p.2) := by
  apply le_antisymm
  · exact le_iInf₂ fun p hp => sInf_le ⟨p, hSU hp, rfl⟩
  · apply le_sInf
    rintro _ ⟨p, hp, rfl⟩
    refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    have ho : IsOpen {q : ℂ × ℂ | ENNReal.ofReal (D q.1 q.2) < c} :=
      isOpen_lt (ENNReal.continuous_ofReal.comp hD) continuous_const
    obtain ⟨q, hqc, hqS⟩ := mem_closure_iff.1 (hUS hp) _ ho hc
    exact (iInf₂_le q hqS).trans hqc.le

/-- The source metric of a whole-plane GFF plus a random continuous function
has almost everywhere measurable infima on every set of point pairs. -/
theorem IsLQGMetric.aemeasurable_pfefferField_sInf
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) {f : Ω → ℂ → ℝ}
    (hfcont : ∀ ω, Continuous (f ω)) (hfmeas : ∀ z, Measurable fun ω => f ω z)
    (U : Set (ℂ × ℂ)) :
    AEMeasurable (fun ω => sInf (Set.image (fun p : ℂ × ℂ =>
      ENNReal.ofReal (𝔇 (pfefferField hC f ω) p.1 p.2)) U)) P := by
  obtain ⟨S, hSc, hSU, hUS⟩ := TopologicalSpace.exists_countable_dense_subset U
  have hm : Measurable fun ω => ⨅ p ∈ S,
      ENNReal.ofReal (𝔇 (pfefferField hC f ω) p.1 p.2) :=
    Measurable.biInf S hSc fun p _ =>
      (hgff.measurable_pfefferField_distance hfcont hfmeas h𝔇.measurable_apply p.1 p.2).ennreal_ofReal
  apply hm.aemeasurable.congr
  filter_upwards [(h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc f hgff hfcont hfmeas).ae_isEuclideanLengthMetric] with ω hω
  exact (sInf_ofReal_image_eq_iInf_of_dense (isEuclideanLengthMetric_continuous hω) hSU hUS).symm

end HarmonicBalls
