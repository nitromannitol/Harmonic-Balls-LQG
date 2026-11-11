import HarmonicBalls.Proofs.GFF.AdmissibleObservationLaw
import HarmonicBalls.Proofs.GFF.CoordinateModification
import LatticeProb.Bonanno.LQGMetric.Field.RandomDistVersion

/-! # Full test distribution-valued versions

The countable reconstruction and the reference whole-plane GFF are due to
Leonardo Bonanno. Agreement with the original pairings is at each fixed test,
with a test-dependent exceptional set. -/

noncomputable section
open MeasureTheory Filter
namespace HarmonicBalls

/-- The admissible observation corresponding to a test function. -/
def testObservable (φ : LQGMetric.TestC) : GFFObservable.Admissible :=
  ⟨.pairing φ, φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩

/-- Reconstruct a distribution from its countable full-test coordinates. -/
def fullTestDistributionVersion (F : LQGMetric.TestC → ℝ) : LQGMetric.DistC :=
  LQGMetric.pairJInv ⊤ (fun c => F (LQGMetric.comb ⊤ c))

theorem measurable_fullTestDistributionVersion : Measurable fullTestDistributionVersion := by
  apply (LQGMetric.measurable_pairJInv ⊤).comp
  exact measurable_pi_iff.mpr fun c => measurable_pi_apply _

theorem fullTestDistributionVersion_pairings (T : LQGMetric.DistC) :
    fullTestDistributionVersion (fun φ => T φ) = T := by
  exact LQGMetric.pairJInv_pairJ ⊤ T

/-- The canonical extension of distribution pairings vanishes on non-tests. -/
def distributionPairingExtension (T : LQGMetric.DistC) (φ : ℂ → ℝ) : ℝ := by
  classical
  exact if hφ : IsTestFunction Set.univ φ then T ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩ else 0

theorem distributionPairingExtension_test (T : LQGMetric.DistC) (φ : LQGMetric.TestC) :
    distributionPairingExtension T φ = T φ := by
  simp [distributionPairingExtension, show IsTestFunction Set.univ φ from
    ⟨φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩]
  congr 1

/-- Any distribution-valued fixed-test version equals the reconstruction on
one full-measure event. -/
theorem ae_fullTestDistributionVersion_eq_of_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} (H : Ω → LQGMetric.DistC)
    (hv : ∀ φ : LQGMetric.TestC, (fun ω => H ω φ) =ᵐ[P] (fun ω => hC ω φ)) :
    ∀ᵐ ω ∂P, fullTestDistributionVersion (fun φ => hC ω φ) = H ω := by
  filter_upwards [ae_all_iff.mpr (fun c : LQGMetric.CoordJ => hv (LQGMetric.comb ⊤ c))] with ω hω
  have he : (fun c => hC ω (LQGMetric.comb ⊤ c)) = LQGMetric.pairJ ⊤ (H ω) := by
    funext c
    exact (hω c).symm
  change LQGMetric.pairJInv ⊤ (fun c => hC ω (LQGMetric.comb ⊤ c)) = H ω
  rw [he, LQGMetric.pairJInv_pairJ]

/-- Fixed-test versions are equal as distributions almost surely. -/
theorem ae_eq_of_fullTest_versions
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} (H K : Ω → LQGMetric.DistC)
    (hH : ∀ φ : LQGMetric.TestC, (fun ω => H ω φ) =ᵐ[P] (fun ω => hC ω φ))
    (hK : ∀ φ : LQGMetric.TestC, (fun ω => K ω φ) =ᵐ[P] (fun ω => hC ω φ)) :
    H =ᵐ[P] K := by
  filter_upwards [ae_fullTestDistributionVersion_eq_of_version H hH,
    ae_fullTestDistributionVersion_eq_of_version K hK] with ω h₁ h₂
  exact h₁.symm.trans h₂

/-- The full-test pairings have a measurable distribution-valued version. -/
theorem IsWholePlaneGFF.exists_fullTest_distribution_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) :
    ∃ H : Ω → LQGMetric.DistC, Measurable H ∧
      (∀ φ : LQGMetric.TestC, (fun ω => H ω φ) =ᵐ[P] (fun ω => hC ω φ)) ∧
      IsWholePlaneGFF P (fun ω => distributionPairingExtension (H ω)) hcirc := by
  obtain ⟨Ω', mΩ', P', hP', T, hT⟩ := LQGMetric.GFFExist.exists_normalizedWPGFF
  let : MeasurableSpace Ω' := mΩ'
  let : IsProbabilityMeasure P' := hP'
  obtain ⟨hC', hcirc', hh', heq, _⟩ := normalizedGFF_exists_projectGFF hT
  let X : Ω → GFFObservable.Admissible → ℝ := fun ω o => o.1.eval (hC ω) (hcirc ω)
  let X' : Ω' → GFFObservable.Admissible → ℝ := fun ω o => o.1.eval (hC' ω) (hcirc' ω)
  let R : (GFFObservable.Admissible → ℝ) → LQGMetric.DistC := fun f =>
    fullTestDistributionVersion (fun φ => f (testObservable φ))
  have hR : Measurable R := measurable_fullTestDistributionVersion.comp
    (measurable_pi_iff.mpr fun φ => measurable_pi_apply (testObservable φ))
  let H := R ∘ X
  have hHm : Measurable H := hR.comp hh.measurable_admissibleObservationProcess
  have hv : ∀ φ : LQGMetric.TestC, (fun ω => H ω φ) =ᵐ[P] (fun ω => hC ω φ) := by
    intro φ
    let S : Set (GFFObservable.Admissible → ℝ) := {f | R f φ = f (testObservable φ)}
    have hS : MeasurableSet S := measurableSet_eq_fun
      ((LQGMetric.measurable_distOn_apply φ).comp hR) (measurable_pi_apply _)
    have href : ∀ᵐ ω ∂P', X' ω ∈ S := by
      filter_upwards with ω
      change fullTestDistributionVersion (fun ψ => hC' ω ψ) φ = hC' ω φ
      simp only [heq, fullTestDistributionVersion_pairings]
    have hin : ∀ᵐ f ∂P.map X, f ∈ S := by
      rw [hh.map_admissibleObservationProcess_eq hh']
      exact (ae_map_iff hh'.measurable_admissibleObservationProcess.aemeasurable hS).2 href
    exact (ae_map_iff hh.measurable_admissibleObservationProcess.aemeasurable hS).1 hin
  refine ⟨H, hHm, hv, hh.coordinateModification ?_ ?_⟩
  · intro φ hφ
    simp only [distributionPairingExtension, dite_eq_left hφ]
    exact (LQGMetric.measurable_distOn_apply ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩).comp hHm
  · intro φ hφ
    simpa [distributionPairingExtension, hφ] using (hv ⟨φ, hφ.1, hφ.2.1, hφ.2.2⟩).symm

end HarmonicBalls
