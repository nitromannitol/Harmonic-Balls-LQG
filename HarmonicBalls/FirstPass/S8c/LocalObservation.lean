import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proofs.Sec11.PinchRootedKernel

/-! # Local observations for the rooted comparison of Lemma 8.2

Definitions of the actual local observation maps of
`docs/campaign/audits/LocalRootedComparisonRepair.md`, section "Actual local observation":

* `r_j = 1/(16 j)` and the domain `D_j = {z : 3 r_j < |z| < 1 - 3 r_j}`, which covers `B_1(0) \ {0}`;
* the recentred restricted measure `L_j(η, z) = (T_z)_* (η|B_{r_j}(z))`, with `T_z x = x - z`;
* the mass normalisation `N_r(η) = η(B_{r/2}(0))⁻¹ • η`, which removes the random positive constant;
* the root observation `O_j(ω, z) = (z, N_{r_j}(L_j(μ ω, z)))` and the reference observation
  `V_j(z, ω) = (z, N_{r_j}(ν ω|B_{r_j}(0)))`;
* the root kernel `λ|B_1(0) / λ(B_1(0))` of the whole-plane LQG measure `λ` (no insertion).

No measurability claim is made here; the measurability of `O_j` and `V_j` is a separate step.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- The radius `r_j = 1/(16 j)` of the local comparison at index `j`. -/
noncomputable def localRadius (j : ℕ) : ℝ := 1 / (16 * (j : ℝ))

/-- The domain `D_j = {z : 3 r_j < |z| < 1 - 3 r_j}`; these sets cover `B_1(0) \ {0}`. -/
def localDomain (j : ℕ) : Set ℂ :=
  {z : ℂ | 3 * localRadius j < ‖z‖ ∧ ‖z‖ < 1 - 3 * localRadius j}

/-- The recentred restriction `L(η, z) = (T_z)_* (η|B_r(z))` with `T_z x = x - z`. -/
noncomputable def recenteredRestriction (η : Measure ℂ) (r : ℝ) (z : ℂ) : Measure ℂ :=
  (η.restrict (ball z r)).map (fun x : ℂ => x - z)

/-- The mass normalisation `N_r(η) = η(B_{r/2}(0))⁻¹ • η`. -/
noncomputable def massNormalize (r : ℝ) (η : Measure ℂ) : Measure ℂ :=
  (η (ball 0 (r / 2)))⁻¹ • η

/-- The root observation `O_j(ω, z) = (z, N_{r_j}(L_j(μ ω, z)))`. -/
noncomputable def localRootObservation {Ω : Type*} (μ : Ω → Measure ℂ) (j : ℕ) :
    Ω × ℂ → ℂ × Measure ℂ :=
  fun x => (x.2, massNormalize (localRadius j) (recenteredRestriction (μ x.1) (localRadius j) x.2))

/-- The reference observation `V_j(z, ω) = (z, N_{r_j}(ν ω|B_{r_j}(0)))`. -/
noncomputable def localReferenceObservation {Ω : Type*} (ν : Ω → Measure ℂ) (j : ℕ) :
    ℂ × Ω → ℂ × Measure ℂ :=
  fun x => (x.1, massNormalize (localRadius j) ((ν x.2).restrict (ball 0 (localRadius j))))

/-- The normalised root kernel `λ|B_1(0) / λ(B_1(0))`, i.e. the weighted restriction kernel with unit weight. -/
noncomputable def localRootKernel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (lam : Ω → Measure ℂ) (hlam : AEMeasurable lam P) : Kernel Ω ℂ :=
  weightedRestrictionKernel P lam hlam (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const

end HarmonicBalls
