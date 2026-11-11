import HarmonicBalls.Steps.Sec11.LocalPathLength
import HarmonicBalls.Steps.Sec11.ProperMetricDyadic
import HarmonicBalls.Proofs.Metric.AnnulusAcrossPositiveFinite

/-!
# Countable representations of set distances

A continuous distance on two nonempty sets is determined by fixed dense
sequences in the sets. This gives measurable and almost-everywhere measurable
representatives of distances between fixed sets, including circles.

We acknowledge Leonardo Bonanno's contributions to this formalization.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory TopologicalSpace
open scoped ENNReal

/-- A continuous function has the same infimum on a dense sequence as on
its whole domain. -/
theorem iInf_eq_iInf_dense_seq {X ι : Type*} [TopologicalSpace X]
    (u : ι → X) (hu : DenseRange u) {f : X → ℝ≥0∞} (hf : Continuous f) :
    (⨅ x, f x) = ⨅ n, f (u n) := by
  have h := hu.ciInf hf (show BddBelow (Set.range f) from ⟨⊥, fun _ _ => bot_le⟩)
  rw [iInf_subtype'', iInf_range] at h
  exact h.symm

/-- Set distance is computed using any fixed dense sequences in the two sets.
No compactness or separation is needed for this identity. -/
theorem ofReal_setDist_eq_iInf_dense_seq {D : ℂ → ℂ → ℝ} {K L : Set ℂ}
    (u : ℕ → K) (v : ℕ → L) (hu : DenseRange u) (hv : DenseRange v)
    (hD : Continuous fun p : ℂ × ℂ => D p.1 p.2) :
    ENNReal.ofReal (setDist D K L) = ⨅ n, ⨅ m, ENNReal.ofReal (D (u n) (v m)) := by
  rw [ofReal_setDist_eq_iInf ⟨u 0, (u 0).property⟩ ⟨v 0, (v 0).property⟩]
  simp only [iInf_subtype']
  have hc : Continuous (fun p : K × L => ENNReal.ofReal (D p.1 p.2)) :=
    ENNReal.continuous_ofReal.comp (hD.comp (continuous_subtype_val.prodMap continuous_subtype_val))
  calc
    (⨅ x : K, ⨅ y : L, ENNReal.ofReal (D x y)) =
        ⨅ p : K × L, ENNReal.ofReal (D p.1 p.2) := (iInf_prod (f := fun p : K × L => ENNReal.ofReal (D p.1 p.2))).symm
    _ = ⨅ p : ℕ × ℕ, ENNReal.ofReal (D (u p.1) (v p.2)) :=
      iInf_eq_iInf_dense_seq (Prod.map u v) (hu.prodMap hv) hc
    _ = ⨅ n, ⨅ m, ENNReal.ofReal (D (u n) (v m)) := iInf_prod (f := fun p : ℕ × ℕ => ENNReal.ofReal (D (u p.1) (v p.2)))

/-- Fixed dense sequences give a measurable distance when their point
pair evaluations are measurable and all distance functions are continuous. -/
theorem measurable_ofReal_setDist_of_dense_seq
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ} {K L : Set ℂ}
    (u : ℕ → K) (v : ℕ → L) (hu : DenseRange u) (hv : DenseRange v)
    (hcont : ∀ ω, Continuous fun p : ℂ × ℂ => D ω p.1 p.2)
    (hmeas : ∀ n m, Measurable fun ω => D ω (u n) (v m)) :
    Measurable fun ω => ENNReal.ofReal (setDist (D ω) K L) := by
  have hm : Measurable (fun ω => ⨅ n, ⨅ m, ENNReal.ofReal (D ω (u n) (v m))) :=
    Measurable.iInf fun n => Measurable.iInf fun m => ENNReal.measurable_ofReal.comp (hmeas n m)
  convert hm using 1
  funext ω
  exact ofReal_setDist_eq_iInf_dense_seq u v hu hv (hcont ω)

/-- If continuity holds almost surely and the countably many evaluations are
almost-everywhere measurable, the actual set distance is a.e. measurable. -/
theorem aemeasurable_ofReal_setDist_of_dense_seq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℂ → ℂ → ℝ} {K L : Set ℂ}
    (u : ℕ → K) (v : ℕ → L) (hu : DenseRange u) (hv : DenseRange v)
    (hcont : ∀ᵐ ω ∂P, Continuous fun p : ℂ × ℂ => D ω p.1 p.2)
    (hmeas : ∀ n m, AEMeasurable (fun ω => D ω (u n) (v m)) P) :
    AEMeasurable (fun ω => ENNReal.ofReal (setDist (D ω) K L)) P := by
  have hm : AEMeasurable (fun ω => ⨅ n, ⨅ m, ENNReal.ofReal (D ω (u n) (v m))) P :=
    AEMeasurable.iInf fun n => AEMeasurable.iInf fun m =>
      ENNReal.measurable_ofReal.comp_aemeasurable (hmeas n m)
  apply hm.congr
  filter_upwards [hcont] with ω hω
  exact (ofReal_setDist_eq_iInf_dense_seq u v hu hv hω).symm

/-- Pointwise a.e. equal evaluations yield one common a.e. equality of the
countable infima, without identifying the original random fields. -/
theorem ae_eq_iInf_dense_seq_of_ae_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D E : Ω → ℂ → ℂ → ℝ} {K L : Set ℂ} (u : ℕ → K) (v : ℕ → L)
    (h : ∀ n m, ∀ᵐ ω ∂P, D ω (u n) (v m) = E ω (u n) (v m)) :
    ∀ᵐ ω ∂P, (⨅ n, ⨅ m, ENNReal.ofReal (D ω (u n) (v m))) =
      ⨅ n, ⨅ m, ENNReal.ofReal (E ω (u n) (v m)) := by
  filter_upwards [ae_all_iff.mpr fun n => ae_all_iff.mpr (h n)] with ω hω
  exact iInf_congr fun n => iInf_congr fun m => congrArg ENNReal.ofReal (hω n m)

/-- Every nonempty subset of the Euclidean plane has a fixed dense sequence
in its relative topology. In particular, this applies to nonempty compact sets. -/
theorem exists_dense_seq_of_nonempty (K : Set ℂ) (hK : K.Nonempty) :
    ∃ u : ℕ → K, DenseRange u := by
  let : Nonempty K := ⟨⟨hK.choose, hK.choose_spec⟩⟩
  exact TopologicalSpace.exists_dense_seq K

/-- The set distance for an almost surely compatible length metric has a
measurable representative constructed from countably many representatives. -/
theorem exists_measurable_ofReal_setDist_representative
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D E : Ω → ℂ → ℂ → ℝ} {K L : Set ℂ}
    (u : ℕ → K) (v : ℕ → L) (hu : DenseRange u) (hv : DenseRange v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hmeas : ∀ n m, Measurable fun ω => E ω (u n) (v m))
    (heq : ∀ n m, ∀ᵐ ω ∂P, D ω (u n) (v m) = E ω (u n) (v m)) :
    ∃ Y : Ω → ℝ≥0∞, Measurable Y ∧
      ∀ᵐ ω ∂P, ENNReal.ofReal (setDist (D ω) K L) = Y ω := by
  refine ⟨fun ω => ⨅ n, ⨅ m, ENNReal.ofReal (E ω (u n) (v m)), ?_, ?_⟩
  · exact Measurable.iInf fun n => Measurable.iInf fun m =>
      ENNReal.measurable_ofReal.comp (hmeas n m)
  · filter_upwards [hmetric, ae_eq_iInf_dense_seq_of_ae_eq u v heq] with ω hω he
    exact (ofReal_setDist_eq_iInf_dense_seq u v hu hv hω.continuous_pair).trans he

/-- The across distance between fixed circles is the infimum over fixed dense
sequences in those circles. -/
theorem pfefferAcross_eq_iInf_dense_seq {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) (z : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R)
    (u : ℕ → sphere z r) (v : ℕ → sphere z R) (hu : DenseRange u) (hv : DenseRange v) :
    pfefferAcross D z r R = ⨅ n, ⨅ m, ENNReal.ofReal (D (u n) (v m)) := by
  rw [pfefferAcross_eq_ofReal_setDist D z hr hR]
  exact ofReal_setDist_eq_iInf_dense_seq u v hu hv hD.continuous_pair

/-- Across distances for fixed circles are a.e. measurable from countably
many a.e. measurable point evaluations. -/
theorem aemeasurable_pfefferAcross_of_dense_seq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℂ → ℂ → ℝ} (z : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R)
    (u : ℕ → sphere z r) (v : ℕ → sphere z R) (hu : DenseRange u) (hv : DenseRange v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hmeas : ∀ n m, AEMeasurable (fun ω => D ω (u n) (v m)) P) :
    AEMeasurable (fun ω => pfefferAcross (D ω) z r R) P := by
  simp_rw [pfefferAcross_eq_ofReal_setDist _ z hr hR]
  apply aemeasurable_ofReal_setDist_of_dense_seq u v hu hv
  · filter_upwards [hmetric] with ω hω
    exact hω.continuous_pair
  · exact hmeas


end HarmonicBalls
