import HarmonicBalls.Proofs.GFF.AdmissibleObservationLaw
import HarmonicBalls.Proofs.GFF.CoordinateModification
import LatticeProb.Bonanno.LQGMetric.Field.RandomDistVersion

/-! # Deterministic shifts of full-test distribution reconstruction

The countable reconstruction and canonical whole-plane GFF are due to Leonardo
Bonanno. Fixed-test agreement has a test-dependent exceptional set; the
countable coordinate agreement below holds on one event. -/

noncomputable section
open MeasureTheory Filter
namespace HarmonicBalls

/-- Reconstruct from the countable family of full-plane test coordinates. -/
def reconstructFullTest (F : LQGMetric.TestC → ℝ) : LQGMetric.DistC :=
  LQGMetric.pairJInv ⊤ (fun c => F (LQGMetric.comb ⊤ c))

theorem measurable_reconstructFullTest : Measurable reconstructFullTest := by
  apply (LQGMetric.measurable_pairJInv ⊤).comp
  exact measurable_pi_iff.mpr fun c => measurable_pi_apply _

/-- Reconstruct after adding the pairings of a deterministic distribution. -/
def reconstructFullTestShift (g : LQGMetric.DistC) (F : LQGMetric.TestC → ℝ) :
    LQGMetric.DistC := reconstructFullTest (fun φ => F φ + g φ)

theorem measurable_reconstructFullTestShift (g : LQGMetric.DistC) :
    Measurable (reconstructFullTestShift g) := by
  apply measurable_reconstructFullTest.comp
  exact measurable_pi_iff.mpr fun φ => (measurable_pi_apply φ).add_const _

private def testObs (φ : LQGMetric.TestC) : GFFObservable.Admissible :=
  ⟨.pairing φ, φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩

/-- Reconstruction agrees with the original process at each fixed test. -/
theorem IsWholePlaneGFF.ae_reconstructFullTest_apply
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (φ : LQGMetric.TestC) :
    (fun ω => reconstructFullTest (fun ψ => hC ω ψ) φ) =ᵐ[P]
      (fun ω => hC ω φ) := by
  obtain ⟨Ω', mΩ', P', hP', T, hT⟩ := LQGMetric.GFFExist.exists_normalizedWPGFF
  let : MeasurableSpace Ω' := mΩ'
  let : IsProbabilityMeasure P' := hP'
  obtain ⟨hC', hcirc', hh', heq, _⟩ := normalizedGFF_exists_projectGFF hT
  let X : Ω → GFFObservable.Admissible → ℝ := fun ω o => o.1.eval (hC ω) (hcirc ω)
  let X' : Ω' → GFFObservable.Admissible → ℝ := fun ω o => o.1.eval (hC' ω) (hcirc' ω)
  let R : (GFFObservable.Admissible → ℝ) → LQGMetric.DistC := fun f =>
    reconstructFullTest (fun ψ => f (testObs ψ))
  have hR : Measurable R := measurable_reconstructFullTest.comp
    (measurable_pi_iff.mpr fun ψ => measurable_pi_apply (testObs ψ))
  let S : Set (GFFObservable.Admissible → ℝ) := {f | R f φ = f (testObs φ)}
  have hS : MeasurableSet S := measurableSet_eq_fun
    ((LQGMetric.measurable_distOn_apply φ).comp hR) (measurable_pi_apply _)
  have href : ∀ᵐ ω ∂P', X' ω ∈ S := by
    filter_upwards with ω
    change reconstructFullTest (fun ψ => hC' ω ψ) φ = hC' ω φ
    simp only [heq, reconstructFullTest]
    change LQGMetric.pairJInv ⊤ (LQGMetric.pairJ ⊤ (T ω)) φ = T ω φ
    rw [LQGMetric.pairJInv_pairJ]
  have hin : ∀ᵐ f ∂P.map X, f ∈ S := by
    rw [hh.map_admissibleObservationProcess_eq hh']
    exact (ae_map_iff hh'.measurable_admissibleObservationProcess.aemeasurable hS).2 href
  exact (ae_map_iff hh.measurable_admissibleObservationProcess.aemeasurable hS).1 hin

/-- The reconstruction of the raw pairing process is measurable. -/
theorem IsWholePlaneGFF.measurable_reconstructFullTest
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) :
    Measurable (fun ω => reconstructFullTest (fun φ => hC ω φ)) := by
  apply HarmonicBalls.measurable_reconstructFullTest.comp
  exact measurable_pi_iff.mpr fun φ => hh.measurable_pairing φ
    ⟨φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩

/-- The shifted reconstruction of the raw pairing process is measurable. -/
theorem IsWholePlaneGFF.measurable_reconstructFullTestShift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (g : LQGMetric.DistC) :
    Measurable (fun ω => reconstructFullTestShift g (fun φ => hC ω φ)) := by
  apply (HarmonicBalls.measurable_reconstructFullTestShift g).comp
  exact measurable_pi_iff.mpr fun φ => hh.measurable_pairing φ
    ⟨φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩

/-- The countable raw coordinate array is the image of its reconstruction almost surely. -/
theorem IsWholePlaneGFF.ae_pairJ_reconstructFullTest
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, LQGMetric.pairJ ⊤ (reconstructFullTest (fun φ => hC ω φ)) =
      (fun c => hC ω (LQGMetric.comb ⊤ c)) := by
  filter_upwards [ae_all_iff.mpr (fun c : LQGMetric.CoordJ =>
    hh.ae_reconstructFullTest_apply (LQGMetric.comb ⊤ c))] with ω hω
  funext c
  exact hω c

/-- On one full-measure event, deterministic shifts commute with reconstruction. -/
theorem IsWholePlaneGFF.ae_reconstructFullTestShift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (g : LQGMetric.DistC) :
    ∀ᵐ ω ∂P, reconstructFullTestShift g (fun φ => hC ω φ) =
      reconstructFullTest (fun φ => hC ω φ) + g := by
  filter_upwards [ae_all_iff.mpr (fun c : LQGMetric.CoordJ =>
    hh.ae_reconstructFullTest_apply (LQGMetric.comb ⊤ c))] with ω hω
  let T := reconstructFullTest (fun φ => hC ω φ)
  have he : (fun c => hC ω (LQGMetric.comb ⊤ c) + g (LQGMetric.comb ⊤ c)) =
      LQGMetric.pairJ ⊤ (T + g) := by
    funext c
    change hC ω (LQGMetric.comb ⊤ c) + g (LQGMetric.comb ⊤ c) =
      T (LQGMetric.comb ⊤ c) + g (LQGMetric.comb ⊤ c)
    rw [hω c]
  change LQGMetric.pairJInv ⊤ (fun c => hC ω (LQGMetric.comb ⊤ c) +
    g (LQGMetric.comb ⊤ c)) = T + g
  rw [he, LQGMetric.pairJInv_pairJ]

/-- The shifted reconstruction agrees with the shifted raw process at each test. -/
theorem IsWholePlaneGFF.ae_reconstructFullTestShift_apply
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (g : LQGMetric.DistC) (φ : LQGMetric.TestC) :
    (fun ω => reconstructFullTestShift g (fun ψ => hC ω ψ) φ) =ᵐ[P]
      (fun ω => hC ω φ + g φ) := by
  filter_upwards [hh.ae_reconstructFullTestShift g, hh.ae_reconstructFullTest_apply φ] with ω hs hv
  rw [hs]
  change reconstructFullTest (fun ψ => hC ω ψ) φ + g φ = _
  rw [hv]

#print axioms IsWholePlaneGFF.ae_reconstructFullTestShift
#print axioms IsWholePlaneGFF.ae_reconstructFullTestShift_apply
end HarmonicBalls
