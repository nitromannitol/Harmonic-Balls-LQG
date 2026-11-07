import HarmonicBalls.Proofs.GFF.DistributionReconstructionShift
import HarmonicBalls.Proofs.Sec8.RootedLogarithmicShift
import LatticeProb.Bonanno.LQGMetric.Field.Measurable

/-! # Logarithmic insertions and full-test reconstruction

The countable reconstruction and distribution measurable structure are due to
Leonardo Bonanno. The insertion is the locally integrable function with
singularity at `z`, with the convention `x - z`. -/

noncomputable section
open MeasureTheory Filter
namespace HarmonicBalls

/-- The logarithmic insertion as a distribution on the whole plane. -/
def logInsertionDistribution (z : ℂ) (a : ℝ) : LQGMetric.DistC :=
  Distribution.ofFun ⊤ (fun x : ℂ => a * Real.log ‖x - z‖) volume ⊤

/-- The logarithmic singularity is locally integrable, including at its root. -/
theorem locallyIntegrable_logInsertion (z : ℂ) (a : ℝ) :
    LocallyIntegrable (fun x : ℂ => a * Real.log ‖x - z‖) volume := by
  have h := (locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm z).smul a
  convert h using 1

/-- Every test pairing is the integral against the actual logarithmic function. -/
theorem logInsertionDistribution_apply (z : ℂ) (a : ℝ) (φ : LQGMetric.TestC) :
    logInsertionDistribution z a φ = ∫ x, φ x * (a * Real.log ‖x - z‖) := by
  rw [logInsertionDistribution, Distribution.ofFun_apply
    ((locallyIntegrable_logInsertion z a).locallyIntegrableOn _)]
  rfl

/-- The test integrand is Bochner integrable; `-z + x = x - z`. -/
theorem integrable_test_mul_logInsertion (z : ℂ) (a : ℝ) (φ : LQGMetric.TestC) :
    Integrable (fun x => φ x * (a * Real.log ‖x - z‖)) := by
  simpa only [sub_eq_add_neg, add_comm] using integrable_test_mul_translated_log φ (-z) a

/-- The distribution is jointly measurable in the root and coefficient. -/
theorem measurable_logInsertionDistribution :
    Measurable (fun p : ℂ × ℝ => logInsertionDistribution p.1 p.2) := by
  apply LQGMetric.measurable_distOn_iff.mpr
  intro φ
  simp only [logInsertionDistribution_apply]
  apply measurable_integral_test_mul_root_function
  change Measurable (fun p : (ℂ × ℝ) × ℂ => p.1.2 * Real.log ‖p.2 - p.1.1‖)
  exact (measurable_snd.comp measurable_fst).mul
    (Real.measurable_log.comp ((measurable_snd.sub (measurable_fst.comp measurable_fst)).norm))

/-- One event works simultaneously for every root and coefficient. -/
theorem IsWholePlaneGFF.ae_reconstructFullTest_logInsertion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, ∀ (z : ℂ) (a : ℝ),
      reconstructFullTest (fun φ => hC ω φ + ∫ x, φ x * (a * Real.log ‖x - z‖)) =
        reconstructFullTest (fun φ => hC ω φ) + logInsertionDistribution z a := by
  filter_upwards [hh.ae_pairJ_reconstructFullTest] with ω hω
  intro z a
  let T := reconstructFullTest (fun φ => hC ω φ)
  let g := logInsertionDistribution z a
  have he : (fun c => hC ω (LQGMetric.comb ⊤ c) +
      ∫ x, LQGMetric.comb ⊤ c x * (a * Real.log ‖x - z‖)) =
      LQGMetric.pairJ ⊤ (T + g) := by
    funext c
    change hC ω (LQGMetric.comb ⊤ c) + _ =
      T (LQGMetric.comb ⊤ c) + g (LQGMetric.comb ⊤ c)
    rw [logInsertionDistribution_apply]
    congr 1
    exact (congrFun hω c).symm
  change LQGMetric.pairJInv ⊤ _ = T + g
  rw [he, LQGMetric.pairJInv_pairJ]

/-- Fixed-test raw compatibility has its own test-dependent exceptional set. -/
theorem IsWholePlaneGFF.ae_reconstructFullTest_logInsertion_apply
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (φ : LQGMetric.TestC) :
    ∀ᵐ ω ∂P, ∀ (z : ℂ) (a : ℝ),
      reconstructFullTest (fun ψ => hC ω ψ + ∫ x, ψ x * (a * Real.log ‖x - z‖)) φ =
        hC ω φ + ∫ x, φ x * (a * Real.log ‖x - z‖) := by
  filter_upwards [hh.ae_reconstructFullTest_logInsertion,
    hh.ae_reconstructFullTest_apply φ] with ω hs hv
  intro z a
  rw [hs z a]
  change reconstructFullTest (fun ψ => hC ω ψ) φ + logInsertionDistribution z a φ = _
  rw [hv, logInsertionDistribution_apply]

#print axioms locallyIntegrable_logInsertion
#print axioms logInsertionDistribution_apply
#print axioms integrable_test_mul_logInsertion
#print axioms measurable_logInsertionDistribution
#print axioms IsWholePlaneGFF.ae_reconstructFullTest_logInsertion
#print axioms IsWholePlaneGFF.ae_reconstructFullTest_logInsertion_apply
end HarmonicBalls
