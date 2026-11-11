import HarmonicBalls.FirstPass.Phase2.CameronMartinLipschitzShiftDerived
import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.Proofs.Sec3.ConservationOfMassStep2
import HarmonicBalls.Proofs.Potential.Fundamental
import LatticeProb.Analysis.LipschitzMollification
import LatticeProb.Analysis.LocallyLipschitzCompactSupport
import LatticeProb.Gauss.CameronMartinLimitShift

/-! # Cameron-Martin for locally Lipschitz compactly supported shifts of the whole-plane GFF

A locally Lipschitz compactly supported `g : ℂ → ℝ` has finite Dirichlet energy, so it lies in the Cameron-Martin space
of the whole-plane Gaussian free field modulo additive constants (Miller-Sheffield, Imaginary Geometry IV,
arXiv:1302.4738v2, Proposition 2.9 and Section 2.2.1). Read on the mean-zero pairings: a measurable set of observations
that is null for `(h^ℂ, φ)_φ` is null for `((h^ℂ, φ) + ∫ φ g)_φ`.

Proof. `g` is globally Lipschitz; its mollifications `u_n` are smooth, compactly supported, converge to `g` uniformly and
in Dirichlet energy. With `q_n = Δ(-(2π)⁻¹ u_n)`, the pairings `(h^ℂ, q_n)` are Cauchy in `L²(P)` and
`Cov((h^ℂ, φ), (h^ℂ, q_n)) → ∫ φ g` for every mean-zero test function `φ`
(`IsWholePlaneGFF.cauchy_pairing_laplacian_of_tendsto_lineDeriv`, `IsWholePlaneGFF.tendsto_covariance_pairing_laplacian`).
The Cameron-Martin theorem for limit shifts of a Gaussian process
(`LatticeProb.Gauss.measure_shift_eq_zero_of_tendsto_covariance`) concludes.

* `cameronMartinLocallyLipschitzShiftAbsCont_holds`: the frozen input `CameronMartinLocallyLipschitzShiftAbsCont`. -/

open MeasureTheory ProbabilityTheory Metric Set Laplacian Filter
open scoped Topology

namespace HarmonicBalls

universe u

/-- **Cameron-Martin for locally Lipschitz compactly supported shifts** of the whole-plane GFF, on the mean-zero
pairings with the test functions supported in a set `D` (Miller-Sheffield, Imaginary Geometry IV, Proposition 2.9):
the input `CameronMartinLocallyLipschitzShiftAbsCont` is a theorem. -/
theorem cameronMartinLocallyLipschitzShiftAbsCont_holds : CameronMartinLocallyLipschitzShiftAbsCont.{u} := by
  intro Ω _ P _ hC hcirc D g h hgL hgc S hS h0
  obtain ⟨C, hLip⟩ := LatticeProb.exists_lipschitzWith_of_locallyLipschitz_of_hasCompactSupport hgL hgc
  obtain ⟨u, hu, huc, hunif, hd⟩ :=
    LatticeProb.exists_contDiff_approx_of_lipschitz (volume : Measure ℂ) hLip hgc
  -- the approximating mean-zero test functions `Δ(-(2π)⁻¹ u_n)`
  let q : ℕ → {φ : ℂ → ℝ // IsTestFunction univ φ ∧ ∫ x, φ x = 0} := fun n =>
    ⟨Δ ((-(2 * Real.pi)⁻¹) • u n),
      isTestFunction_laplacian_of_smooth (contDiff_const_smul_fun _ (hu n))
        (hasCompactSupport_const_smul_fun _ (huc n)),
      integral_laplacian_eq_zero ((contDiff_const_smul_fun _ (hu n)).of_le (by simp))
        (hasCompactSupport_const_smul_fun _ (huc n))⟩
  -- restriction of the observations to the test functions supported in `D`
  let ρ : ({φ : ℂ → ℝ // IsTestFunction univ φ ∧ ∫ x, φ x = 0} → ℝ) →
      ({φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ) :=
    fun f φ => f ⟨φ.1, φ.2.1.mono_set (subset_univ _), φ.2.2⟩
  have hρ : Measurable ρ := measurable_pi_iff.mpr fun φ => measurable_pi_apply _
  exact LatticeProb.Gauss.measure_shift_eq_zero_of_tendsto_covariance h.isGaussianProcess_meanZero_pairing
    (fun φ => h.measurable_pairing φ.1 φ.2.1) (fun φ => h.integral_eq_zero (.pairing φ.1) φ.2.1) q
    (fun φ => ∫ x, φ.1 x * g x) (h.cauchy_pairing_laplacian_of_tendsto_lineDeriv _ hu huc hd)
    (fun φ => h.tendsto_covariance_pairing_laplacian hLip.continuous hu huc hunif φ.2.1 φ.2.2) (hρ hS) h0

end HarmonicBalls
