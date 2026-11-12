import HarmonicBalls.FirstPass.Phase2.CampbellLeftLimit
import HarmonicBalls.FirstPass.Phase2.CampbellRegularized
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmDMSConstant
import HarmonicBalls.Proofs.Sec6.ContinuousWeylCircleAverage
import HarmonicBalls.Proofs.Sec8.OpenBallDensity

/-!
# Campbell identity for product tests (Duplantier-Miller-Sheffield, Lemma A.10)

For a whole-plane GFF `h` with pairings `(h, φ)` and circle averages `h_ε(z)`, `0 < γ < 2`, and its `γ`-LQG measure `μ`
(insertion `α = 0`), the rooted measure `E[μ_h(dz) dh]` restricted to the open unit disc `B₁` and tested against a
product `F((h, φ_1), …, (h, φ_n)) g(z)` equals the average over `z ∈ B₁` of the law of the field shifted by the
covariance potential `γ G(z, ·)` (Duplantier-Sheffield, §3.3; Duplantier-Miller-Sheffield, Lemma A.10, proof):
`E[F((h, φ_i)_i) ∫ g dμ] = ∫_{B₁} g(z) E[F((h + f_z + κ, φ_i)_i)] dz`, with the shift `f_z` and the constant `κ` of
Lemma A.10 (`κ = 0` almost surely in the closed unit disc).

The proof passes to the limit `ε_k = 2^{-k} → 0` in the regularized identity: on the rooted side by the `L¹`
convergence of the approximating measures, on the shifted side by the convergence of the covariances
`Cov((h, φ), h_ε(z)) → ∫ φ(w) G(z, w) dw` and dominated convergence.

## Main results

* `IsWholePlaneGFF.ae_setLIntegral_circleWeight_mul_eq`: the circle-average density integrated against `g` is the
  mass of `g` under the approximating measure.
* `IsWholePlaneGFF.lintegral_mul_lintegral_eq_dmsShifted`: the Campbell identity for product tests.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Density form of the approximating measure.** Almost surely, the circle-average density
`ε_k^{γ²/2} e^{γ h_{ε_k}(z)}` integrated against `g` over its support is the mass of `g` under the approximating
measure at the scale `ε_k = 2^{-k}`. -/
theorem IsWholePlaneGFF.ae_setLIntegral_circleWeight_mul_eq (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {g : ℂ → ℝ} (hgc : Continuous g) (k : ℕ) :
    ∀ᵐ ω ∂P, ∫⁻ z in tsupport g, ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * hcirc ω (dyadicScale k) z)) * ENNReal.ofReal (g z)
      = ∫⁻ z, ENNReal.ofReal (g z) ∂(lqgApprox γ (hcirc ω) (dyadicScale k)) := by
  obtain ⟨H, hHm, -, -, hH⟩ := hh.exists_measurable_circle_version (dyadicScale_pos k)
  filter_upwards [hH] with ω hω
  have hdm : Measurable fun z => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * hcirc ω (dyadicScale k) z)) := by
    rw [← hω]
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (hHm.comp measurable_prodMk_left))))
  rw [lqgApprox, lintegral_withDensity_eq_lintegral_mul _ hdm hgc.measurable.ennreal_ofReal]
  refine setLIntegral_eq_of_support_subset ?_
  intro z hz
  refine subset_tsupport g ?_
  intro hgz
  apply hz
  simp [hgz]

/-- **Campbell identity for product tests** (Duplantier-Miller-Sheffield, Lemma A.10, whole-plane clause, for
product tests). For a whole-plane GFF, `0 < γ < 2`, the `α = 0` LQG measure `μ`, test functions `φ_1, …, φ_n`, a
continuous `F` with `0 ≤ F ≤ 1` and a continuous `g ≥ 0` with compact support in the open unit disc,
`E[F((h, φ_i)_i) ∫ g dμ] = ∫_{B₁} g(z) E[F((h + f_z + κ, φ_i)_i)] dz`. -/
theorem IsWholePlaneGFF.lintegral_mul_lintegral_eq_dmsShifted (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) {n : ℕ}
    {φ : Fin n → ℂ → ℝ} (hφ : ∀ i, IsTestFunction univ (φ i)) {F : (Fin n → ℝ) → ℝ} (hFc : Continuous F)
    (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1) {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    (hg1 : tsupport g ⊆ ball (0 : ℂ) 1) (hg0 : ∀ z, 0 ≤ g z) :
    ∫⁻ ω, ENNReal.ofReal (F fun i => hC ω (φ i)) * ∫⁻ z, ENNReal.ofReal (g z) ∂(μ ω) ∂P
      = ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (g z) *
          ∫⁻ ω, ENNReal.ofReal (F fun i => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) (φ i)) ∂P := by
  have hP : IsProbabilityMeasure P := hh.isGaussianProcess.isProbabilityMeasure
  have hU : MeasurableSet (tsupport g) := (isClosed_tsupport g).measurableSet
  obtain ⟨k₀, hk₀⟩ := LatticeProb.Gauss.exists_norm_add_dyadicScale_le_one hgs.isCompact hg1
  have hk : ∀ k, k₀ ≤ k → ∀ z ∈ tsupport g, ‖z‖ + dyadicScale k ≤ 1 := fun k hk z hz => by
    have := hk₀ z hz (k - k₀)
    rwa [Nat.sub_add_cancel hk] at this
  have hXm : Measurable fun ω => fun i => hC ω (φ i) :=
    measurable_pi_iff.mpr fun i => hh.measurable_pairing (φ i) (hφ i)
  have hcov : ∀ {r : ℝ}, 0 < r → ∀ i z, cov[fun ω => hC ω (φ i), fun ω => hcirc ω r z; P]
      = Real.circleAverage (observableCovariancePotential (.pairing (φ i))) z r := fun hr i z =>
    hh.covariance_observable_circle_eq_potential ⟨.pairing (φ i), hφ i⟩ hr z
  have hpotc : ∀ i, Continuous (observableCovariancePotential (.pairing (φ i))) := fun i =>
    continuous_observableCovariancePotential ⟨.pairing (φ i), hφ i⟩
  -- the shifted side at scale `ε_k` and in the limit
  let S : ℕ → ℂ → ℝ≥0∞ := fun k z => ENNReal.ofReal (g z) * ∫⁻ ω, ENNReal.ofReal (F fun i =>
    hC ω (φ i) + γ * Real.circleAverage (observableCovariancePotential (.pairing (φ i))) z (dyadicScale k)) ∂P
  let Slim : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (g z) * ∫⁻ ω, ENNReal.ofReal (F fun i =>
    hC ω (φ i) + γ * observableCovariancePotential (.pairing (φ i)) z) ∂P
  have hSm : ∀ k, Measurable (S k) := fun k => by
    refine hgc.measurable.ennreal_ofReal.mul ?_
    have hj : Measurable fun q : ℂ × Ω => ENNReal.ofReal (F fun i => hC q.2 (φ i) +
        γ * Real.circleAverage (observableCovariancePotential (.pairing (φ i))) q.1 (dyadicScale k)) := by
      refine ENNReal.measurable_ofReal.comp (hFc.measurable.comp (measurable_pi_iff.mpr fun i => ?_))
      refine ((hh.measurable_pairing (φ i) (hφ i)).comp measurable_snd).add (measurable_const.mul ?_)
      exact ((Section6.continuous_circleAverage_radius_center (hpotc i)).comp
        (continuous_const.prodMk continuous_id)).measurable.comp measurable_fst
    exact hj.lintegral_prod_right'
  have hSle : ∀ k z, S k z ≤ ENNReal.ofReal (g z) := fun k z => by
    have h1 : ∫⁻ ω, ENNReal.ofReal (F fun i => hC ω (φ i) + γ * Real.circleAverage
        (observableCovariancePotential (.pairing (φ i))) z (dyadicScale k)) ∂P ≤ 1 :=
      (lintegral_mono fun ω => ENNReal.ofReal_le_one.2 (hF1 _)).trans_eq (by simp)
    calc S k z ≤ ENNReal.ofReal (g z) * 1 := by
          simp only [S]
          gcongr
      _ = ENNReal.ofReal (g z) := mul_one _
  have hSlim : ∀ z, Tendsto (fun k => S k z) atTop (𝓝 (Slim z)) := fun z => by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofReal_ne_top)
    refine tendsto_lintegral_of_dominated_convergence (fun _ => 1) (fun k => ?_) (fun k => ?_) (by simp) ?_
    · exact ENNReal.measurable_ofReal.comp (hFc.measurable.comp (measurable_pi_iff.mpr fun i =>
        (hh.measurable_pairing (φ i) (hφ i)).add_const _))
    · exact Eventually.of_forall fun ω => ENNReal.ofReal_le_one.2 (hF1 _)
    · refine Eventually.of_forall fun ω => ENNReal.tendsto_ofReal ?_
      refine (hFc.tendsto _).comp (tendsto_pi_nhds.2 fun i => ?_)
      refine tendsto_const_nhds.add (tendsto_const_nhds.mul ?_)
      have h := (hh.tendsto_covariance_pairing_circle (hφ i) z).comp tendsto_dyadicScale_nhdsGT
      exact h.congr fun k => hcov (dyadicScale_pos k) i z
  have hc : ∫⁻ z in tsupport g, ENNReal.ofReal (g z) ≠ ∞ :=
    ((hgc.integrable_of_hasCompactSupport hgs).integrableOn.lintegral_lt_top).ne
  have hR : Tendsto (fun k => ∫⁻ z in tsupport g, S k z) atTop (𝓝 (∫⁻ z in tsupport g, Slim z)) :=
    tendsto_lintegral_of_dominated_convergence (fun z => ENNReal.ofReal (g z)) hSm
      (fun k => Eventually.of_forall (hSle k)) hc (Eventually.of_forall hSlim)
  -- the rooted side
  have hL := hh.tendsto_lintegral_mul_lintegral_lqgApprox hγ0 hγ2 hμ hgc hgs hg1 hg0
    (Θ := fun ω => F fun i => hC ω (φ i)) (hFc.measurable.comp hXm).aemeasurable (fun _ => hF0 _)
    (fun _ => hF1 _)
  -- the regularized identity at small dyadic scales
  have heq : ∀ k, k₀ ≤ k → ∫⁻ ω, ENNReal.ofReal (F fun i => hC ω (φ i)) *
      ∫⁻ z, ENNReal.ofReal (g z) ∂(lqgApprox γ (hcirc ω) (dyadicScale k)) ∂P = ∫⁻ z in tsupport g, S k z := by
    intro k hkk
    have hΦ : Measurable fun p : ({φ : ℂ → ℝ // IsTestFunction univ φ} → ℝ) × ℂ =>
        ENNReal.ofReal (F fun i => p.1 ⟨φ i, hφ i⟩) * ENNReal.ofReal (g p.2) :=
      (ENNReal.measurable_ofReal.comp (hFc.measurable.comp (measurable_pi_iff.mpr fun i =>
        (measurable_pi_apply _).comp measurable_fst))).mul
        (ENNReal.measurable_ofReal.comp (hgc.measurable.comp measurable_snd))
    have h5 := hh.lintegral_lintegral_circleWeight_mul_eq (dyadicScale_pos k) γ hU (hk k hkk) hΦ
    calc _ = ∫⁻ ω, ∫⁻ z in tsupport g, ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
            Real.exp (γ * hcirc ω (dyadicScale k) z)) *
            (ENNReal.ofReal (F fun i => hC ω (φ i)) * ENNReal.ofReal (g z)) ∂volume ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hh.ae_setLIntegral_circleWeight_mul_eq γ hgc k] with ω hω
          rw [← hω, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun z => ?_
          ring
      _ = ∫⁻ z in tsupport g, ∫⁻ ω, ENNReal.ofReal (F fun i => hC ω (φ i) +
            γ * cov[fun ω => hC ω (φ i), fun ω => hcirc ω (dyadicScale k) z; P]) * ENNReal.ofReal (g z) ∂P
            ∂volume := h5
      _ = ∫⁻ z in tsupport g, S k z := by
          refine setLIntegral_congr_fun hU fun z _ => ?_
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm]
          simp only [S, hcov (dyadicScale_pos k)]
  have hlimeq : ∫⁻ ω, ENNReal.ofReal (F fun i => hC ω (φ i)) * ∫⁻ z, ENNReal.ofReal (g z) ∂(μ ω) ∂P
      = ∫⁻ z in tsupport g, Slim z :=
    tendsto_nhds_unique (hL.congr' (eventually_atTop.2 ⟨k₀, heq⟩)) hR
  -- identification of the shift with the DMS-shifted pairing
  have hsupp : ∀ z, z ∉ tsupport g → g z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  rw [hlimeq, setLIntegral_eq_of_support_subset (Function.support_subset_iff'.2 fun z hz => by
      simp [Slim, hsupp z hz]),
    setLIntegral_eq_of_support_subset (Function.support_subset_iff'.2 fun z hz => by
      simp [hsupp z fun h => hz (hg1 h)])]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ ball (0 : ℂ) 1
  · have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.1 hz).le
    refine congrArg (ENNReal.ofReal (g z) * ·) (lintegral_congr_ae ?_)
    filter_upwards [dmsShiftedPairing_ae_eq hh γ hz1] with ω hω
    rw [hω]
    simp only [mul_observableCovariancePotential_pairing_eq hz1]
  · simp [Slim, hsupp z fun h => hz (hg1 h)]

end HarmonicBalls
