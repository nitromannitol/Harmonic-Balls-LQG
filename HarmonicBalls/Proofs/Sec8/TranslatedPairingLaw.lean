import HarmonicBalls.Proofs.Sec6.AnnulusLawTransfer
import HarmonicBalls.Proofs.Sec8.RootedReferenceLawDomination
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance

/-! # Translation invariance of mean-zero GFF pairings

We transfer Leonardo Bonanno's affine invariance for distribution-valued
whole-plane GFFs to the pairing-valued field used in this project. -/

noncomputable section

open MeasureTheory

namespace HarmonicBalls

/-- Translation preserves the law of all mean-zero pairings of the frozen
whole-plane GFF. This holds simultaneously for the full cylinder law, not
just for individual test functions. -/
theorem IsWholePlaneGFF.map_translated_pairingProc_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (z : ℂ) :
    P.map (fun ω (φ : LQGMetric.TestC0) =>
      hC ω (LQGMetric.testAffinePull 1 z φ.1)) =
    P.map (Section6.pairingProc hC) := by
  obtain ⟨Ω', mΩ', P', hP', h', hh'⟩ := LQGMetric.GFFExist.exists_normalizedWPGFF
  let : MeasurableSpace Ω' := mΩ'
  let : IsProbabilityMeasure P' := hP'
  let e : (LQGMetric.TestC0 → ℝ) → (LQGMetric.TestC0 → ℝ) :=
    fun f φ => f (LQGMetric.GFFInv.pull0 1 z (by norm_num) φ)
  have he : Measurable e := measurable_pi_iff.mpr fun φ => measurable_pi_apply _
  have hmap := congrArg (fun μ : Measure (LQGMetric.TestC0 → ℝ) => μ.map e)
    (Section6.map_pairingProc_eq hh hh'.1)
  rw [Measure.map_map he (Section6.measurable_pairingProc hh),
    Measure.map_map he (LQGMetric.GFFLaw.measurable_pairProc hh'.1.measurable)] at hmap
  have htranslated := Section6.map_pairingProc_eq hh (hh'.1.affineComp (r := 1) (by norm_num) z)
  have heq : (fun ω => e (LQGMetric.GFFLaw.pairProc h' ω)) =
      LQGMetric.GFFLaw.pairProc (fun ω => LQGMetric.affineComp 1 z (h' ω)) := by
    funext ω φ
    simp only [e, LQGMetric.GFFLaw.pairProc, LQGMetric.GFFInv.pull0,
      LQGMetric.GFFInv.affineComp_apply, one_pow, inv_one, one_mul]
  change Measure.map (fun ω => e (Section6.pairingProc hC ω)) P =
    Measure.map (fun ω => e (LQGMetric.GFFLaw.pairProc h' ω)) P' at hmap
  rw [heq] at hmap
  exact hmap.trans htranslated.symm

/-- Jointly measurable translated pairings have the same null sets as an
independent copy of the original pairing process, with the root retained. -/
theorem IsWholePlaneGFF.rooted_translated_pairingProc_equivalence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (ρ : Measure ℂ)
    (hjoint : Measurable (fun p : ℂ × Ω => fun φ : LQGMetric.TestC0 =>
      hC p.2 (LQGMetric.testAffinePull 1 p.1 φ.1))) :
    let A := shiftedRootReferenceLaw ρ P (fun p => fun φ : LQGMetric.TestC0 =>
      hC p.2 (LQGMetric.testAffinePull 1 p.1 φ.1))
    let B := shiftedRootReferenceLaw ρ P (fun p => Section6.pairingProc hC p.2)
    A ≪ B ∧ B ≪ A := by
  have hP := hh.isProbabilityMeasure
  let : IsProbabilityMeasure P := hP
  have hbase : Measurable (fun p : ℂ × Ω => Section6.pairingProc hC p.2) :=
    (Section6.measurable_pairingProc hh).comp measurable_snd
  constructor
  · apply shiftedRootReferenceLaw_absolutelyContinuous_of_fiberwise ρ P P _ _ hjoint hbase
    exact Filter.Eventually.of_forall (fun z => Measure.absolutelyContinuous_of_le (hh.map_translated_pairingProc_eq z).le)
  · apply shiftedRootReferenceLaw_absolutelyContinuous_of_fiberwise ρ P P _ _ hbase hjoint
    exact Filter.Eventually.of_forall (fun z => Measure.absolutelyContinuous_of_le (hh.map_translated_pairingProc_eq z).symm.le)

end HarmonicBalls
