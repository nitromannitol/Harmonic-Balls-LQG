import HarmonicBalls.Proofs.Sec8.LocalizedRecenteredObservation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Null sets of rooted observations

A rooted comparison transfers null sets of root positions from the reference
root measure to the sampled random measure. This includes the unit circle,
which separates the two buffered normalization regions. The imported Section 6
development uses Leonardo Bonanno's whole-plane GFF formalization.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

/-- A null set of roots is null for the root coordinate of a shifted
reference law. -/
theorem ae_shiftedRootReferenceLaw_root_not_mem
    {Z Ω F : Type*} [MeasurableSpace Z] [MeasurableSpace Ω] [MeasurableSpace F]
    (ρ : Measure Z) (P : Measure Ω) [SFinite P]
    (X : Z × Ω → F) (hX : Measurable X) (B : Set Z) (hB : MeasurableSet B)
    (hρ : ρ B = 0) :
    ∀ᵐ q ∂shiftedRootReferenceLaw ρ P X, q.2 ∉ B := by
  have hmap : Measurable (fun p : Z × Ω => (X p, p.1)) := hX.prodMk measurable_fst
  have hset : MeasurableSet {q : F × Z | q.2 ∉ B} := (measurable_snd hB).compl
  apply (ae_map_iff hmap.aemeasurable hset).2
  apply (Measure.ae_prod_iff_ae_ae (hmap hset)).2
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hρ] with z hz
  exact Filter.Eventually.of_forall (fun _ => hz)

/-- If a rooted observation law is dominated by a shifted reference law,
reference-null root sets contain almost no sampled points. -/
theorem IsWholePlaneGFF.ae_ae_not_mem_of_rooted_comparison
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (μ : Ω → Measure ℂ)
    (hμ : AEMeasurable μ P) (A B : Set ℂ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hfin : ∀ᵐ ω ∂P, μ ω A ≠ ∞)
    (ρ : Measure ℂ) (γ : ℝ) (hρ : ρ B = 0)
    (hrooted : (P.bind fun ω => ((μ ω).restrict A).map
      (fun z => (Section6.pairingProc hC ω, z))) ≪
      shiftedRootReferenceLaw ρ P (fun p => fun φ : LQGMetric.TestC0 =>
        hC p.2 φ.1 + ∫ x, φ.1 x *
          (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1)))) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ A → z ∉ B := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have href := ae_shiftedRootReferenceLaw_root_not_mem ρ P _
    (hh.measurable_wholePlane_inserted_pairings γ) B hB hρ
  exact ae_ae_mem_of_observed_restricted_bind P μ hμ (Section6.pairingProc hC)
    (Section6.measurable_pairingProc hh) A hA hfin (hrooted.ae_le href)

/-- Roots strictly outside the unit circle with a positive prescribed buffer. -/
def exteriorBufferedRoots (n : ℕ) : Set ℂ :=
  {z | 1 + 1 / ((n : ℝ) + 1) < ‖z‖}

/-- Each exterior buffered root set is measurable. -/
theorem measurableSet_exteriorBufferedRoots (n : ℕ) :
    MeasurableSet (exteriorBufferedRoots n) := by
  exact measurable_norm measurableSet_Ioi

/-- The exterior buffered root sets cover every point outside the closed unit disk. -/
theorem exteriorBufferedRoots_cover {z : ℂ} (hz : 1 < ‖z‖) :
    ∃ n, z ∈ exteriorBufferedRoots n := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hz)
  refine ⟨n, ?_⟩
  change 1 + 1 / ((n : ℝ) + 1) < ‖z‖
  linarith

/-- On an exterior buffered root set, the translated ball stays outside the
unit circle. -/
theorem ae_exteriorBufferedRoots_side (ρ : Measure ℂ) (n : ℕ) :
    ∀ᵐ z ∂(ρ.restrict (exteriorBufferedRoots n)),
      ‖z‖ + 1 / ((n : ℝ) + 1) ≤ 1 ∨
        1 + 1 / ((n : ℝ) + 1) ≤ ‖z‖ := by
  filter_upwards [ae_restrict_mem (measurableSet_exteriorBufferedRoots n)] with z hz
  exact Or.inr (le_of_lt hz)


/-- If the reference root measure is dominated by area, almost every sampled
root lies in one of the interior or exterior buffered regions. -/
theorem IsWholePlaneGFF.ae_ae_buffered_root_cover
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (μ : Ω → Measure ℂ)
    (hμ : AEMeasurable μ P) (A : Set ℂ) (hA : MeasurableSet A)
    (hfin : ∀ᵐ ω ∂P, μ ω A ≠ ∞) (ρ : Measure ℂ)
    (hρ : ρ ≪ volume) (γ : ℝ)
    (hrooted : (P.bind fun ω => ((μ ω).restrict A).map
      (fun z => (Section6.pairingProc hC ω, z))) ≪
      shiftedRootReferenceLaw ρ P (fun p => fun φ : LQGMetric.TestC0 =>
        hC p.2 φ.1 + ∫ x, φ.1 x *
          (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1)))) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ A →
      (∃ n, z ∈ unitBallBufferedRoots n) ∨ (∃ n, z ∈ exteriorBufferedRoots n) := by
  have hnull : ρ (sphere (0 : ℂ) 1) = 0 :=
    hρ (Measure.addHaar_sphere volume 0 1)
  filter_upwards [hh.ae_ae_not_mem_of_rooted_comparison μ hμ A (sphere 0 1) hA
    isClosed_sphere.measurableSet hfin ρ γ hnull hrooted] with ω hω
  filter_upwards [hω] with z hz hzA
  have hne : ‖z‖ ≠ 1 := by
    intro heq
    apply hz hzA
    simpa [mem_sphere, dist_eq_norm] using heq
  rcases lt_or_gt_of_ne hne with hin | hout
  · left
    apply unitBallBufferedRoots_cover
    simpa [mem_ball, dist_eq_norm] using hin
  · exact Or.inr (exteriorBufferedRoots_cover hout)

#print axioms IsWholePlaneGFF.ae_ae_buffered_root_cover
#print axioms ae_shiftedRootReferenceLaw_root_not_mem
#print axioms IsWholePlaneGFF.ae_ae_not_mem_of_rooted_comparison
#print axioms exteriorBufferedRoots_cover
#print axioms ae_exteriorBufferedRoots_side

end HarmonicBalls
