import HarmonicBalls.Proofs.Sec8.GaussianGerm
import HarmonicBalls.Proofs.Sec8.CircleDensityDoubleLog

/-! # Interior pairings and exterior Laplacian probes

The logarithmic fundamental solution makes the interior zero-integral field
orthogonal to Laplacian probes whose potentials vanish in the interior. The
imported Section 8 argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

open MeasureTheory ProbabilityTheory Metric Set Laplacian
open scoped Topology ProbabilityTheory

namespace HarmonicBalls

/-- The whole-plane covariance potential of a Laplacian consists of a
constant and minus `2π` times its compactly supported potential. -/
theorem integral_laplacian_mul_wholePlaneCov {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (x : ℂ) :
    (∫ y, Δ ψ y * wholePlaneCov x y) =
      (∫ y, Δ ψ y * wholePlaneNormalization y) - 2 * Real.pi * ψ x := by
  let g : ℂ → ℝ := Δ ψ
  have hg : Continuous g := continuous_laplacian_of_contDiff hψ
  have hgc : HasCompactSupport g := hasCompactSupport_laplacian hψc
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hni : Integrable (fun y => g y * wholePlaneNormalization y) :=
    (hg.mul continuous_wholePlaneNormalization).integrable_of_hasCompactSupport hgc.mul_right
  have hli : Integrable (fun y => g y * Real.log ‖y - x‖) := by
    have h := (locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm x
      ).integrable_smul_right_of_hasCompactSupport hg hgc
    simpa only [smul_eq_mul, mul_comm] using h
  have heq : (∫ y, g y * wholePlaneCov x y) =
      ∫ y, (g y * wholePlaneNormalization x + g y * wholePlaneNormalization y) -
        g y * Real.log ‖y - x‖ := by
    apply integral_congr_ae
    filter_upwards [ae_ne_complex x] with y hy
    have hxy : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy.symm)
    have hx : max ‖x‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    have hy' : max ‖y‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    rw [wholePlaneCov, Real.log_div (mul_ne_zero hx hy') hxy, Real.log_mul hx hy', norm_sub_rev]
    simp only [wholePlaneNormalization]
    ring
  have hai : Integrable (fun y => g y * wholePlaneNormalization x +
      g y * wholePlaneNormalization y) := (hgi.mul_const _).add hni
  have hsum : (∫ y, g y * wholePlaneNormalization x + g y * wholePlaneNormalization y) =
      (∫ y, g y * wholePlaneNormalization x) + ∫ y, g y * wholePlaneNormalization y :=
    integral_add (hgi.mul_const _) hni
  have hgzero : ∫ y, g y = 0 := integral_laplacian_eq_zero hψ hψc
  have hlog : (∫ y, g y * Real.log ‖y - x‖) = 2 * Real.pi * ψ x := by
    simpa only [g, mul_comm] using integral_log_norm_sub_mul_laplacian hψ hψc x
  change (∫ y, g y * wholePlaneCov x y) = _
  rw [heq, integral_sub hai hli, hsum, integral_mul_const, hgzero, zero_mul, zero_add, hlog]

/-- A zero-integral interior pairing has zero covariance with the Laplacian
of a compactly supported potential that vanishes on the interior support. -/
theorem wholePlaneGFFCov_pairing_laplacian_eq_zero {φ ψ : ℂ → ℝ}
    (hφzero : ∫ x, φ x = 0) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (hvanish : ∀ x ∈ tsupport φ, ψ x = 0) :
    wholePlaneGFFCov (.pairing φ) (.pairing (Δ ψ)) = 0 := by
  change (∫ x, φ x * (∫ y, Δ ψ y * wholePlaneCov x y)) = 0
  simp_rw [integral_laplacian_mul_wholePlaneCov hψ hψc]
  calc
    _ = ∫ x, φ x * (∫ y, Δ ψ y * wholePlaneNormalization y) := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : φ x = 0
      · simp [hx]
      · have hψx := hvanish x (subset_tsupport φ (by simpa using hx))
        rw [hψx]
        ring
    _ = 0 := by rw [integral_mul_const, hφzero, zero_mul]

/-- The interior field modulo constants is jointly independent of all
Laplacian pairings whose compactly supported potentials vanish there. -/
theorem IsWholePlaneGFF.indepFun_interiorPairings_exteriorLaplacians
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (U : Set ℂ) :
    IndepFun
      (fun ω (φ : {φ : ℂ → ℝ // IsTestFunction U φ ∧ ∫ x, φ x = 0}) => hC ω φ.1)
      (fun ω (ψ : {ψ : ℂ → ℝ // IsTestFunction Set.univ ψ ∧
          IsTestFunction Set.univ (Δ ψ) ∧ ∀ x ∈ U, ψ x = 0}) => hC ω (Δ ψ.1)) P := by
  let S := {φ : ℂ → ℝ // IsTestFunction U φ ∧ ∫ x, φ x = 0}
  let T := {ψ : ℂ → ℝ // IsTestFunction Set.univ ψ ∧
    IsTestFunction Set.univ (Δ ψ) ∧ ∀ x ∈ U, ψ x = 0}
  let X : S → Ω → ℝ := fun φ ω => hC ω φ.1
  let Y : T → Ω → ℝ := fun ψ ω => hC ω (Δ ψ.1)
  have htest (φ : S) : IsTestFunction Set.univ φ.1 :=
    ⟨φ.2.1.1, φ.2.1.2.1, subset_univ _⟩
  let o : S ⊕ T → GFFObservable.Admissible := Sum.elim
    (fun φ => ⟨.pairing φ.1, htest φ⟩) (fun ψ => ⟨.pairing (Δ ψ.1), ψ.2.2.1⟩)
  have hg : IsGaussianProcess (Sum.elim X Y) P := by
    convert h.isGaussianProcess.comp_right o using 1
    funext q ω
    cases q <;> rfl
  apply hg.indepFun_of_covariance_eq_zero
  · exact fun φ => (h.measurable_pairing φ.1 (htest φ)).aemeasurable
  · exact fun ψ => (h.measurable_pairing (Δ ψ.1) ψ.2.2.1).aemeasurable
  · intro φ ψ
    exact (h.covariance_eq (.pairing φ.1) (.pairing (Δ ψ.1))
      (htest φ) ψ.2.2.1).trans
      (wholePlaneGFFCov_pairing_laplacian_eq_zero φ.2.2
        (ψ.2.1.1.of_le (by norm_num)) ψ.2.1.2.1
        (fun x hx => ψ.2.2.2 x (φ.2.1.2.2 hx)))

end HarmonicBalls
