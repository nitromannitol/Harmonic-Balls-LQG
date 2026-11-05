import HarmonicBalls.Proofs.Sec8.TranslatedPairingLaw
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGerm
import LatticeProb.Bonanno.LQGMetric.Field.RandomDistVersion

/-! # Distribution-valued version modulo constants

The countable-coordinate reconstruction and whole-plane GFF used here are
from Leonardo Bonanno's LatticeProb formalization. -/

noncomputable section

open MeasureTheory Filter TopologicalSpace

namespace HarmonicBalls

/-- Reconstruct a distribution from countably many mean-zero pairings, with
its gauge fixed by a unit-integral circle mollifier. -/
def meanZeroDistributionVersion (F : LQGMetric.TestC0 → ℝ) : LQGMetric.DistC :=
  LQGMetric.pairJInv ⊤ (fun c => F (LQGMetric.MarkovGerm.meanZeroApprox
    (LQGMetric.comb ⊤ c) 0))

/-- The reconstruction is measurable for the cylinder sigma-algebra. -/
theorem measurable_meanZeroDistributionVersion : Measurable meanZeroDistributionVersion := by
  apply (LQGMetric.measurable_pairJInv ⊤).comp
  exact measurable_pi_iff.mpr fun c => measurable_pi_apply _

/-- On the mean-zero pairings of a distribution, reconstruction fixes a
deterministic additive-constant gauge. -/
theorem meanZeroDistributionVersion_pairProc (h : LQGMetric.DistC) :
    meanZeroDistributionVersion (fun φ => h φ.1) =
      LQGMetric.addConst h (-(h (LQGMetric.CircleAvg.circBump 0 0 1))) := by
  have heq : (fun c => h (LQGMetric.MarkovGerm.meanZeroApprox
      (LQGMetric.comb ⊤ c) 0).1) =
      LQGMetric.pairJ ⊤ (LQGMetric.addConst h (-(h (LQGMetric.CircleAvg.circBump 0 0 1)))) := by
    funext c
    change h (LQGMetric.MarkovGerm.meanZeroApprox (LQGMetric.comb ⊤ c) 0).1 =
      LQGMetric.addConst h (-(h (LQGMetric.CircleAvg.circBump 0 0 1))) (LQGMetric.comb ⊤ c)
    rw [LQGMetric.MarkovGerm.meanZeroApprox_apply, LQGMetric.GFFInv.addConst_apply,
      LQGMetric.CircleAvg.mollAvg_eq]
    ring
  unfold meanZeroDistributionVersion
  rw [heq, LQGMetric.pairJInv_pairJ]

/-- The frozen GFF pairings have a measurable distribution-valued version:
for each mean-zero test its pairing agrees almost surely with the original
pairing. The exceptional set may depend on the test. -/
theorem IsWholePlaneGFF.exists_meanZero_distribution_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) :
    ∃ H : Ω → LQGMetric.DistC, Measurable H ∧
      ∀ φ : LQGMetric.TestC0, (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1) := by
  obtain ⟨Ω', mΩ', P', hP', h', hh'⟩ := LQGMetric.GFFExist.exists_normalizedWPGFF
  let : MeasurableSpace Ω' := mΩ'
  let : IsProbabilityMeasure P' := hP'
  let X := Section6.pairingProc hC
  let H := meanZeroDistributionVersion ∘ X
  refine ⟨H, measurable_meanZeroDistributionVersion.comp (Section6.measurable_pairingProc hh), ?_⟩
  intro φ
  let S : Set (LQGMetric.TestC0 → ℝ) := {f | meanZeroDistributionVersion f φ.1 = f φ}
  have hS : MeasurableSet S :=
    measurableSet_eq_fun ((LQGMetric.measurable_distOn_apply φ.1).comp
      measurable_meanZeroDistributionVersion) (measurable_pi_apply φ)
  have href : ∀ᵐ ω ∂P', LQGMetric.GFFLaw.pairProc h' ω ∈ S := by
    filter_upwards with ω
    change meanZeroDistributionVersion (fun ψ => h' ω ψ.1) φ.1 = h' ω φ.1
    rw [meanZeroDistributionVersion_pairProc, LQGMetric.GFFInv.addConst_apply, φ.2, zero_mul, add_zero]
  have hmap := Section6.map_pairingProc_eq hh hh'.1
  have hin : ∀ᵐ f ∂P.map X, f ∈ S := by
    rw [hmap]
    exact (ae_map_iff (LQGMetric.GFFLaw.measurable_pairProc hh'.1.measurable).aemeasurable hS).2 href
  exact (ae_map_iff (Section6.measurable_pairingProc hh).aemeasurable hS).1 hin

#print axioms meanZeroDistributionVersion_pairProc
#print axioms IsWholePlaneGFF.exists_meanZero_distribution_version

end HarmonicBalls
