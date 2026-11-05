import HarmonicBalls.Proofs.Sec8.TranslatedDistributionMeasurable
import HarmonicBalls.Proofs.Sec8.RootedNormalizationShift

/-! # Insertions in translated distribution versions

The distribution reconstruction and Cameron–Martin input use Leonardo
Bonanno's whole-plane GFF development. -/

noncomputable section

open MeasureTheory Metric Set

namespace HarmonicBalls

/-- A measurable root-dependent operation maps a joint reference law to
another joint reference law. -/
theorem shiftedRootReferenceLaw_map_root_operation
    {Z Ω F G : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    [MeasurableSpace F] [MeasurableSpace G]
    (ρ : Measure Z) (P : Measure Ω) (X : Z × Ω → F) (hX : Measurable X)
    (T : F × Z → G) (hT : Measurable T) :
    (shiftedRootReferenceLaw ρ P X).map (fun q => (T q, q.2)) =
      shiftedRootReferenceLaw ρ P (fun p => T (X p, p.1)) := by
  unfold shiftedRootReferenceLaw
  rw [Measure.map_map (hT.prodMk measurable_snd) (hX.prodMk measurable_fst)]
  rfl

/-- Local restriction and a common measurable root-dependent insertion
preserve equivalence of two joint field-and-root laws. -/
theorem shiftedRootReferenceLaw_local_insertion_equivalence
    {Z Ω Ξ : Type*} [MeasurableSpace Z] [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (ρ : Measure Z) (P : Measure Ω) (Q : Measure Ξ) {U : Set ℂ}
    (X : Z × Ω → LQGMetric.TestC0 → ℝ)
    (Y : Z × Ξ → LQGMetric.TestC0 → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (heq : shiftedRootReferenceLaw ρ P X ≪ shiftedRootReferenceLaw ρ Q Y ∧
      shiftedRootReferenceLaw ρ Q Y ≪ shiftedRootReferenceLaw ρ P X)
    (g : Z → ℂ → ℝ) (hg : Measurable (Function.uncurry g)) :
    let A := shiftedRootReferenceLaw ρ P (fun p => fun φ : Section6.LocalTest U =>
      X p φ.1 + ∫ x, φ.1.1 x * g p.1 x)
    let B := shiftedRootReferenceLaw ρ Q (fun p => fun φ : Section6.LocalTest U =>
      Y p φ.1 + ∫ x, φ.1.1 x * g p.1 x)
    A ≪ B ∧ B ≪ A := by
  let T : (LQGMetric.TestC0 → ℝ) × Z → (Section6.LocalTest U → ℝ) :=
    fun q φ => q.1 φ.1 + ∫ x, φ.1.1 x * g q.2 x
  have hT : Measurable T := by
    apply measurable_pi_iff.mpr
    intro φ
    exact ((measurable_pi_apply φ.1).comp measurable_fst).add
      ((measurable_integral_test_mul_root_function g hg φ.1.1).comp measurable_snd)
  have hm : Measurable (fun q => (T q, q.2)) := hT.prodMk measurable_snd
  have hf := heq.1.map hm
  have hb := heq.2.map hm
  rw [shiftedRootReferenceLaw_map_root_operation ρ P X hX T hT,
    shiftedRootReferenceLaw_map_root_operation ρ Q Y hY T hT] at hf hb
  exact ⟨hf, hb⟩

/-- A translated distribution version with any common measurable insertion
has the same local rooted null sets as the original mean-zero pairing law. -/
theorem IsWholePlaneGFF.rooted_translated_distribution_insertion_equivalence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (H : Ω → LQGMetric.DistC)
    (hH : Measurable H)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1))
    (ρ : Measure ℂ) {U : Set ℂ} (g : ℂ → ℂ → ℝ)
    (hg : Measurable (Function.uncurry g)) :
    let A := shiftedRootReferenceLaw ρ P (fun p => fun φ : Section6.LocalTest U =>
      H p.2 (LQGMetric.testAffinePull 1 p.1 φ.1.1) + ∫ x, φ.1.1 x * g p.1 x)
    let B := shiftedRootReferenceLaw ρ P (fun p => fun φ : Section6.LocalTest U =>
      hC p.2 φ.1.1 + ∫ x, φ.1.1 x * g p.1 x)
    A ≪ B ∧ B ≪ A := by
  exact shiftedRootReferenceLaw_local_insertion_equivalence ρ P P _ _
    (measurable_translated_distribution_pairProc hH)
    ((Section6.measurable_pairingProc hh).comp measurable_snd)
    (hh.rooted_translated_distribution_version_equivalence H hH hversion ρ) g hg

/-- The translated distribution version with the recentered whole-plane
insertion has the local null sets of a field with the origin logarithm. -/
theorem IsWholePlaneGFF.rooted_translated_distribution_normalization_equivalence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (H : Ω → LQGMetric.DistC)
    (hH : Measurable H)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1))
    (ρ : Measure ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) (a b : ℝ)
    (hside : ∀ᵐ z ∂ρ, ‖z‖ + R ≤ 1 ∨ 1 + R ≤ ‖z‖) :
    let A := shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball 0 r) =>
        H p.2 (LQGMetric.testAffinePull 1 p.1 φ.1.1) + ∫ x, φ.1.1 x *
          (a * Real.log (max ‖p.1 + x‖ 1) + b * Real.log ‖x‖))
    let B := shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (b * Real.log ‖x‖))
    A ≪ B ∧ B ≪ A := by
  have hg : Measurable (Function.uncurry fun z x : ℂ =>
      a * Real.log (max ‖z + x‖ 1) + b * Real.log ‖x‖) := by
    exact ((Real.measurable_log.comp ((measurable_fst.add measurable_snd).norm.max
      measurable_const)).const_mul a).add ((Real.measurable_log.comp measurable_snd.norm).const_mul b)
  have h₁ := hh.rooted_translated_distribution_insertion_equivalence H hH hversion ρ
    (U := ball 0 r) _ hg
  have h₂ := hh.rooted_combined_normalization_equivalence ρ hr hrR a b hside
  exact ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

/-- The canonical measurable reconstruction of the original pairing process
agrees with every fixed mean-zero pairing almost surely. -/
theorem IsWholePlaneGFF.canonical_distribution_version_pairing
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (φ : LQGMetric.TestC0) :
    (fun ω => meanZeroDistributionVersion (Section6.pairingProc hC ω) φ.1) =ᵐ[P]
      (fun ω => hC ω φ.1) := by
  obtain ⟨H, hH, hversion⟩ := hh.exists_meanZero_distribution_version
  filter_upwards [ae_all_iff.mpr (fun c : LQGMetric.CoordJ =>
    hversion (LQGMetric.MarkovGerm.meanZeroApprox (LQGMetric.comb ⊤ c) 0)), hversion φ] with ω hω hφ
  have heq : meanZeroDistributionVersion (Section6.pairingProc hC ω) =
      meanZeroDistributionVersion (fun ψ => H ω ψ.1) := by
    unfold meanZeroDistributionVersion
    congr 1
    funext c
    exact (hω c).symm
  rw [heq, meanZeroDistributionVersion_pairProc, LQGMetric.GFFInv.addConst_apply,
    φ.2, zero_mul, add_zero]
  exact hφ

/-- The canonical reconstruction, measurable from the original full
mean-zero field, satisfies the translated local insertion comparison. -/
theorem IsWholePlaneGFF.rooted_canonical_distribution_normalization_equivalence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    (ρ : Measure ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) (a b : ℝ)
    (hside : ∀ᵐ z ∂ρ, ‖z‖ + R ≤ 1 ∨ 1 + R ≤ ‖z‖) :
    let H := meanZeroDistributionVersion ∘ Section6.pairingProc hC
    let A := shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball 0 r) =>
        H p.2 (LQGMetric.testAffinePull 1 p.1 φ.1.1) + ∫ x, φ.1.1 x *
          (a * Real.log (max ‖p.1 + x‖ 1) + b * Real.log ‖x‖))
    let B := shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (b * Real.log ‖x‖))
    A ≪ B ∧ B ≪ A := by
  exact hh.rooted_translated_distribution_normalization_equivalence
    (meanZeroDistributionVersion ∘ Section6.pairingProc hC)
    (measurable_meanZeroDistributionVersion.comp (Section6.measurable_pairingProc hh))
    hh.canonical_distribution_version_pairing ρ hr hrR a b hside

#print axioms IsWholePlaneGFF.canonical_distribution_version_pairing
#print axioms IsWholePlaneGFF.rooted_canonical_distribution_normalization_equivalence
#print axioms IsWholePlaneGFF.rooted_translated_distribution_normalization_equivalence

end HarmonicBalls
