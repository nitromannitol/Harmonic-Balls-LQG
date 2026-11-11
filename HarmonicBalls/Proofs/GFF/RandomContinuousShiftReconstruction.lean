import HarmonicBalls.Proofs.GFF.DistributionReconstructionShift
import LatticeProb.Bonanno.LQGMetric.Field.Measurable

/-! # Reconstruction under a random continuous shift

The countable distribution reconstruction and continuous-field pairing results used
here are due to Leonardo Bonanno. No independence of the shift is assumed. -/

noncomputable section
open MeasureTheory Filter
namespace HarmonicBalls

/-- Package continuous sample paths as a continuous-map-valued function. -/
def continuousShift {Ω : Type*} (f : Ω → ℂ → ℝ)
    (hf : ∀ ω, Continuous (f ω)) : Ω → C(ℂ, ℝ) :=
  fun ω => ⟨f ω, hf ω⟩

@[simp] theorem continuousShift_apply {Ω : Type*} (f : Ω → ℂ → ℝ)
    (hf : ∀ ω, Continuous (f ω)) (ω : Ω) (z : ℂ) :
    continuousShift f hf ω z = f ω z := rfl

/-- Pointwise measurability and continuous sample paths give compact-open measurability. -/
theorem measurable_continuousShift {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → ℂ → ℝ) (hf : ∀ ω, Continuous (f ω))
    (hm : ∀ z, Measurable fun ω => f ω z) : Measurable (continuousShift f hf) :=
  ContinuousMap.measurable_iff_eval.mpr hm

/-- The distribution of each continuous sample has the expected test pairing. -/
theorem ofCont_continuousShift_apply {Ω : Type*} (f : Ω → ℂ → ℝ)
    (hf : ∀ ω, Continuous (f ω)) (ω : Ω) (φ : LQGMetric.TestC) :
    LQGMetric.ofCont (continuousShift f hf ω) φ = ∫ z, f ω z * φ z := by
  rw [LQGMetric.ofCont_apply]
  simp only [continuousShift_apply, mul_comm]

/-- The reconstruction of the randomly shifted raw field is measurable. -/
theorem IsWholePlaneGFF.measurable_reconstructFullTest_randomShift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (f : Ω → ℂ → ℝ)
    (hf : ∀ ω, Continuous (f ω)) (hm : ∀ z, Measurable fun ω => f ω z) :
    Measurable (fun ω => reconstructFullTest (fun φ => addFunPairing (hC ω) (f ω) φ)) := by
  apply HarmonicBalls.measurable_reconstructFullTest.comp
  apply measurable_pi_iff.mpr
  intro φ
  have hpair := (LQGMetric.measurable_ofCont_apply φ).comp (measurable_continuousShift f hf hm)
  change Measurable (fun ω => LQGMetric.ofCont (continuousShift f hf ω) φ) at hpair
  simp only [ofCont_continuousShift_apply] at hpair
  exact (hh.measurable_pairing φ ⟨φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩).add hpair

/-- One full-measure event suffices for distribution equality, even for dependent shifts. -/
theorem IsWholePlaneGFF.ae_reconstructFullTest_randomShift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (f : Ω → ℂ → ℝ)
    (hf : ∀ ω, Continuous (f ω)) :
    ∀ᵐ ω ∂P, reconstructFullTest (fun φ => addFunPairing (hC ω) (f ω) φ) =
      reconstructFullTest (fun φ => hC ω φ) + LQGMetric.ofCont (continuousShift f hf ω) := by
  filter_upwards [hh.ae_pairJ_reconstructFullTest] with ω hω
  let T := reconstructFullTest (fun φ => hC ω φ)
  let g := LQGMetric.ofCont (continuousShift f hf ω)
  have he : (fun c => addFunPairing (hC ω) (f ω) (LQGMetric.comb ⊤ c)) =
      LQGMetric.pairJ ⊤ (T + g) := by
    funext c
    change hC ω (LQGMetric.comb ⊤ c) + ∫ z, f ω z * LQGMetric.comb ⊤ c z =
      T (LQGMetric.comb ⊤ c) + g (LQGMetric.comb ⊤ c)
    rw [ofCont_continuousShift_apply]
    congr 1
    exact (congrFun hω c).symm
  change LQGMetric.pairJInv ⊤ (fun c => addFunPairing (hC ω) (f ω) (LQGMetric.comb ⊤ c)) = T + g
  rw [he, LQGMetric.pairJInv_pairJ]

/-- At each fixed test, the shifted reconstruction agrees with the raw shifted pairing. -/
theorem IsWholePlaneGFF.ae_reconstructFullTest_randomShift_apply
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (f : Ω → ℂ → ℝ)
    (hf : ∀ ω, Continuous (f ω)) (φ : LQGMetric.TestC) :
    (fun ω => reconstructFullTest (fun ψ => addFunPairing (hC ω) (f ω) ψ) φ) =ᵐ[P]
      (fun ω => addFunPairing (hC ω) (f ω) φ) := by
  filter_upwards [hh.ae_reconstructFullTest_randomShift f hf,
    hh.ae_reconstructFullTest_apply φ] with ω hs hv
  rw [hs]
  change reconstructFullTest (fun ψ => hC ω ψ) φ +
    LQGMetric.ofCont (continuousShift f hf ω) φ = hC ω φ + ∫ z, f ω z * φ z
  rw [hv, ofCont_continuousShift_apply]

end HarmonicBalls
