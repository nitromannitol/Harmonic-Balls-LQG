import HarmonicBalls.Steps.Sec11.InternalDiameterDecoder
import HarmonicBalls.Proofs.Metric.InternalDistanceCompactBounds

/-!
# Countable evaluation of internal diameters

For a Euclidean length metric, internal distance is jointly continuous on an
open domain, including between different components where it may be infinite.
Fixed dense sequences therefore determine the internal diameter. Measurability
requires measurable internal-distance evaluations (or measurable versions).
-/

namespace HarmonicBalls

open Set MeasureTheory Filter Topology
open scoped ENNReal

/-- Joint continuity on an open set, including infinite distances. -/
theorem IsEuclideanLengthMetric.continuousOn_internalDistance_pair
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U : Set ℂ} (hU : IsOpen U) :
    ContinuousOn (fun p : ℂ × ℂ => internalMetric D U p.1 p.2) (U ×ˢ U) :=
  hD.continuousOn_internalMetric_pair hD.distance_nonneg hU

/-- The internal distance supremum on two fixed subsets of an open set is
computed on any two fixed dense sequences. -/
theorem IsEuclideanLengthMetric.iSup_internalDistance_eq_dense_seq
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U K L : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U) (hLU : L ⊆ U)
    (u : ℕ → K) (v : ℕ → L) (hu : DenseRange u) (hv : DenseRange v) :
    (⨆ x ∈ K, ⨆ y ∈ L, internalMetric D U x y) =
      ⨆ n, ⨆ m, internalMetric D U (u n) (v m) := by
  have hc : Continuous (fun p : K × L => internalMetric D U p.1 p.2) :=
    hD.continuousOn_internalDistance_pair hU |>.comp_continuous
      (continuous_subtype_val.prodMap continuous_subtype_val)
      (fun p => ⟨hKU p.1.property, hLU p.2.property⟩)
  have h := (hu.prodMap hv).ciSup hc
    (show BddAbove (Set.range (fun p : K × L => internalMetric D U p.1 p.2)) from
      ⟨⊤, fun _ _ => le_top⟩)
  change (⨆ p : Set.range (Prod.map u v),
    (fun q : K × L => internalMetric D U q.1 q.2) p) = _ at h
  have hseq := (iSup_range' (fun q : K × L => internalMetric D U q.1 q.2)
    (Prod.map u v)).symm.trans h
  calc
    (⨆ x ∈ K, ⨆ y ∈ L, internalMetric D U x y) =
        ⨆ p : K × L, internalMetric D U p.1 p.2 := by
          simp only [iSup_subtype, iSup_prod]
    _ = ⨆ p : ℕ × ℕ, internalMetric D U (u p.1) (v p.2) := hseq.symm
    _ = ⨆ n, ⨆ m, internalMetric D U (u n) (v m) := by
      rw [iSup_prod]

/-- A compact subset of a connected open set has finite internal diameter,
with the same value as the supremum over a fixed dense sequence. -/
theorem IsEuclideanLengthMetric.compact_internalDiameter_eq_dense_seq_lt_top
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U K : Set ℂ} (hU : IsOpen U) (hconn : IsConnected U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (u : ℕ → K) (hu : DenseRange u) :
    (⨆ x ∈ K, ⨆ y ∈ K, internalMetric D U x y) =
        (⨆ n, ⨆ m, internalMetric D U (u n) (u m)) ∧
      (⨆ n, ⨆ m, internalMetric D U (u n) (u m)) < ∞ := by
  have heq := hD.iSup_internalDistance_eq_dense_seq hU hKU hKU u u hu hu
  exact ⟨heq, heq ▸ hD.internalDistance_compact_uniform_lt_top hU hconn hK hKU⟩

/-- Measurable internal-distance evaluations on fixed dense sequences yield
a measurable supremum when every sample is a Euclidean length metric. -/
theorem measurable_iSup_internalDistance_of_dense_seq
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ}
    {U K L : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U) (hLU : L ⊆ U)
    (u : ℕ → K) (v : ℕ → L) (hu : DenseRange u) (hv : DenseRange v)
    (hmetric : ∀ ω, IsEuclideanLengthMetric (D ω))
    (hmeas : ∀ n m, Measurable fun ω => internalMetric (D ω) U (u n) (v m)) :
    Measurable fun ω => ⨆ x ∈ K, ⨆ y ∈ L, internalMetric (D ω) U x y := by
  have hm : Measurable (fun ω => ⨆ n, ⨆ m, internalMetric (D ω) U (u n) (v m)) :=
    Measurable.iSup fun n => Measurable.iSup (hmeas n)
  convert hm using 1
  funext ω
  exact (hmetric ω).iSup_internalDistance_eq_dense_seq hU hKU hLU u v hu hv

/-- Almost-everywhere measurable internal-distance evaluations on the fixed
sequences yield an almost-everywhere measurable supremum. -/
theorem aemeasurable_iSup_internalDistance_of_dense_seq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℂ → ℂ → ℝ} {U K L : Set ℂ} (hU : IsOpen U)
    (hKU : K ⊆ U) (hLU : L ⊆ U)
    (u : ℕ → K) (v : ℕ → L) (hu : DenseRange u) (hv : DenseRange v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hmeas : ∀ n m, AEMeasurable (fun ω => internalMetric (D ω) U (u n) (v m)) P) :
    AEMeasurable (fun ω => ⨆ x ∈ K, ⨆ y ∈ L, internalMetric (D ω) U x y) P := by
  have hm : AEMeasurable (fun ω => ⨆ n, ⨆ m, internalMetric (D ω) U (u n) (v m)) P :=
    AEMeasurable.iSup fun n => AEMeasurable.iSup fun m => hmeas n m
  apply hm.congr
  filter_upwards [hmetric] with ω hω
  exact (hω.iSup_internalDistance_eq_dense_seq hU hKU hLU u v hu hv).symm

/-- Measurable versions of the countably many internal-distance evaluations
provide a measurable representative of the supremum. -/
theorem exists_measurable_iSup_internalDistance_representative
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℂ → ℂ → ℝ} {U K L : Set ℂ} (hU : IsOpen U)
    (hKU : K ⊆ U) (hLU : L ⊆ U)
    (u : ℕ → K) (v : ℕ → L) (hu : DenseRange u) (hv : DenseRange v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (G : ℕ → ℕ → Ω → ℝ≥0∞) (hG : ∀ n m, Measurable (G n m))
    (heq : ∀ n m, ∀ᵐ ω ∂P, internalMetric (D ω) U (u n) (v m) = G n m ω) :
    ∃ Y : Ω → ℝ≥0∞, Measurable Y ∧
      ∀ᵐ ω ∂P, (⨆ x ∈ K, ⨆ y ∈ L, internalMetric (D ω) U x y) = Y ω := by
  refine ⟨fun ω => ⨆ n, ⨆ m, G n m ω, Measurable.iSup fun n => Measurable.iSup (hG n), ?_⟩
  filter_upwards [hmetric, ae_all_iff.mpr fun n => ae_all_iff.mpr (heq n)] with ω hω he
  rw [hω.iSup_internalDistance_eq_dense_seq hU hKU hLU u v hu hv]
  exact iSup_congr fun n => iSup_congr fun m => he n m

/-- Locality supplies a representative measurable in the field restricted to
`U`. The almost-everywhere equality is with respect to the original measure;
no inclusion between the two measurable spaces is assumed. -/
theorem SatisfiesLQGMetricAxioms.exists_local_internalDiameter_representative
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {h : Ω → (ℂ → ℝ) → ℝ}
    (haxioms : SatisfiesLQGMetricAxioms P γ ξ 𝔇 h)
    {U K : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U)
    (u : ℕ → K) (hu : DenseRange u) :
    ∃ Y : Ω → ℝ≥0∞, Measurable[pairingSigmaAlgebra h U] Y ∧
      ∀ᵐ ω ∂P, (⨆ x ∈ K, ⨆ y ∈ K, internalMetric (𝔇 (h ω)) U x y) = Y ω := by
  obtain ⟨G, hG, hEq⟩ := haxioms.locality U hU
  refine ⟨fun ω => ⨆ n, ⨆ m, G ω (u n) (u m),
    Measurable.iSup fun n => Measurable.iSup fun m => hG (u n) (u m), ?_⟩
  filter_upwards [haxioms.ae_isEuclideanLengthMetric, hEq] with ω hmetric heq
  rw [hmetric.iSup_internalDistance_eq_dense_seq hU hKU hKU u u hu hu]
  exact iSup_congr fun n => iSup_congr fun m =>
    heq (u n) (hKU (u n).property) (u m) (hKU (u m).property)

#print axioms IsEuclideanLengthMetric.continuousOn_internalDistance_pair
#print axioms IsEuclideanLengthMetric.iSup_internalDistance_eq_dense_seq
#print axioms IsEuclideanLengthMetric.compact_internalDiameter_eq_dense_seq_lt_top
#print axioms measurable_iSup_internalDistance_of_dense_seq
#print axioms aemeasurable_iSup_internalDistance_of_dense_seq
#print axioms exists_measurable_iSup_internalDistance_representative
#print axioms SatisfiesLQGMetricAxioms.exists_local_internalDiameter_representative

end HarmonicBalls
