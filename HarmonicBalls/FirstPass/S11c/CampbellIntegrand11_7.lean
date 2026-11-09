import HarmonicBalls.FirstPass.S11c.CampbellLocal11_7

/-!
# First pass, Lemma 11.7: measurability of the Campbell integrand (task fp-S11c-11-7-redo-11-10, owner n1; B2 sec 6;
discharges the hypothesis `hF` of `campbell_local_eventual`)

Let `U = B_{r₁}(c₁) ⊆ D = B_{r₂}(c₂)` and let `S` be the local bad set (measurable, `measurableSet_localBadSet`).
On the decoder event `K(obs ω) = c • (μ ω)|_D` with `c ∈ (0,∞)`, the Campbell integrand
`(μ ω U)⁻¹ ∫_U 1_S(z, obs ω) dμ_ω(z)` equals `G(obs ω)`, where
`G x = (K x U)⁻¹ ∫_U 1_S(z, x) dK_x(z)` is measurable on the observation space (kernel integrals of a jointly measurable
integrand). The integrand is therefore almost everywhere measurable.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

universe u

namespace HarmonicBalls.S11c

/-- Ratio identity used to cancel the decoder constant `c ∈ (0,∞)`: `(c⁻¹ a)⁻¹ (c⁻¹ I) = a⁻¹ I`. -/
theorem ennreal_ratio_cancel {c a I : ℝ≥0∞} (hc0 : c ≠ 0) (hcT : c ≠ ⊤) :
    (c⁻¹ * a)⁻¹ * (c⁻¹ * I) = a⁻¹ * I := by
  rw [ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.mpr hcT)) (Or.inl (ENNReal.inv_ne_top.mpr hc0)), inv_inv]
  calc (c * a⁻¹) * (c⁻¹ * I) = (c * c⁻¹) * (a⁻¹ * I) := by ring
    _ = a⁻¹ * I := by rw [ENNReal.mul_inv_cancel hc0 hcT, one_mul]

/-- The ratio `G x = (K x U)⁻¹ ∫_U 1_S(z, x) dK_x(z)` on the observation space. -/
noncomputable def campbellRatio {X : Type*} [MeasurableSpace X] (K : Kernel X ℂ) (U : Set ℂ)
    (S : Set (ℂ × X)) (x : X) : ℝ≥0∞ :=
  (K x U)⁻¹ * ∫⁻ z in U, S.indicator (fun _ => (1 : ℝ≥0∞)) (z, x) ∂(K x)

/-- The ratio is measurable on the observation space (kernel integrals of a jointly measurable integrand). -/
theorem measurable_campbellRatio {X : Type*} [MeasurableSpace X] (K : Kernel X ℂ) [IsSFiniteKernel K]
    {U : Set ℂ} (hU : MeasurableSet U) {S : Set (ℂ × X)} (hS : MeasurableSet S) :
    Measurable (campbellRatio K U S) := by
  have h1 : Measurable (fun p : X × ℂ => S.indicator (fun _ => (1 : ℝ≥0∞)) (p.2, p.1)) :=
    (measurable_const.indicator hS).comp (measurable_snd.prodMk measurable_fst)
  have hT : MeasurableSet {p : X × ℂ | p.2 ∈ U} := hU.preimage measurable_snd
  have h2 : Measurable (fun p : X × ℂ =>
      {p : X × ℂ | p.2 ∈ U}.indicator (fun q : X × ℂ => S.indicator (fun _ => (1 : ℝ≥0∞)) (q.2, q.1)) p) :=
    h1.indicator hT
  have hint : ∀ x : X, ∫⁻ z in U, S.indicator (fun _ => (1 : ℝ≥0∞)) (z, x) ∂(K x) =
      ∫⁻ z, {p : X × ℂ | p.2 ∈ U}.indicator (fun q : X × ℂ => S.indicator (fun _ => (1 : ℝ≥0∞)) (q.2, q.1))
        (x, z) ∂(K x) := by
    intro x
    rw [← lintegral_indicator hU]
    refine lintegral_congr fun z => ?_
    by_cases h : z ∈ U
    · exact (Set.indicator_of_mem h _).trans
        (Set.indicator_of_mem (show (x, z) ∈ {p : X × ℂ | p.2 ∈ U} from h) (fun q : X × ℂ => S.indicator (fun _ => (1 : ℝ≥0∞)) (q.2, q.1))).symm
    · exact (Set.indicator_of_notMem h _).trans
        (Set.indicator_of_notMem (show (x, z) ∉ {p : X × ℂ | p.2 ∈ U} from h) (fun q : X × ℂ => S.indicator (fun _ => (1 : ℝ≥0∞)) (q.2, q.1))).symm
  have hI : Measurable (fun x : X => ∫⁻ z in U, S.indicator (fun _ => (1 : ℝ≥0∞)) (z, x) ∂(K x)) := by
    simp only [hint]
    exact Measurable.lintegral_kernel_prod_right' h2
  exact ((Kernel.measurable_coe K hU).inv).mul hI

/-- The Campbell integrand is almost everywhere measurable, given the decoder identity (B2 sec 6, hypothesis `hF` of
`campbell_local_eventual`). -/
theorem aemeasurable_campbell_integrand
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hh : IsWholePlaneGFF P hC hcirc)
    {α₀ : ℝ} {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    {K : Kernel ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) ℂ} [IsSFiniteKernel K]
    {Q : Set ℂ} (hQ : IsCone Q) {M a : ℝ} {nD : ℕ}
    (hdec : ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
      K (localMeanZeroObs α₀ (ball c₂ r₂) (hC ω)) = c • (μ ω).restrict (ball c₂ r₂)) :
    AEMeasurable (fun ω => ((μ ω) (ball c₁ r₁))⁻¹ * ∫⁻ z in ball c₁ r₁,
        (localBadSet K Q M a (ball c₁ r₁) nD).indicator (fun _ => (1 : ℝ≥0∞))
          (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω)) P := by
  have hS : MeasurableSet (localBadSet K Q M a (ball c₁ r₁) nD) :=
    measurableSet_localBadSet K (measurableSet_of_isCone hQ) M a measurableSet_ball nD
  have hG := measurable_campbellRatio K (measurableSet_ball : MeasurableSet (ball c₁ r₁)) hS
  have hobs : Measurable (fun ω => localMeanZeroObs α₀ (ball c₂ r₂) (hC ω)) := by
    apply Measurable.of_eval
    rintro ⟨φ, hφ⟩
    unfold localMeanZeroObs fieldPairing
    exact (hh.measurable_pairing φ ⟨hφ.1.1, hφ.1.2.1, Set.subset_univ _⟩).sub measurable_const
  refine ((hG.comp hobs).aemeasurable).congr ?_
  filter_upwards [hdec] with ω hω
  obtain ⟨c, hc0, hcT, hK⟩ := hω
  have hc0' : c ≠ 0 := hc0.ne'
  have hcT' : c ≠ ⊤ := hcT.ne
  have hUD : ball c₁ r₁ ⊆ ball c₂ r₂ := Metric.ball_subset_closedBall.trans hsub
  -- the restricted measure of the root ball and the decoder constant
  have hD' : (μ ω).restrict (ball c₂ r₂) = c⁻¹ • K (localMeanZeroObs α₀ (ball c₂ r₂) (hC ω)) := by
    rw [hK, smul_smul, ENNReal.inv_mul_cancel hc0' hcT', one_smul]
  have hμU : (μ ω) (ball c₁ r₁) = c⁻¹ * K (localMeanZeroObs α₀ (ball c₂ r₂) (hC ω)) (ball c₁ r₁) := by
    have h := congrArg (fun ν : Measure ℂ => ν (ball c₁ r₁)) hK
    simp only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply measurableSet_ball,
      Set.inter_eq_left.mpr hUD] at h
    rw [h, ← mul_assoc, ENNReal.inv_mul_cancel hc0' hcT', one_mul]
  have hμint : ∫⁻ z in ball c₁ r₁, (localBadSet K Q M a (ball c₁ r₁) nD).indicator (fun _ => (1 : ℝ≥0∞))
        (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω) =
      c⁻¹ * ∫⁻ z in ball c₁ r₁, (localBadSet K Q M a (ball c₁ r₁) nD).indicator (fun _ => (1 : ℝ≥0∞))
        (z, localMeanZeroObs α₀ (ball c₂ r₂) (hC ω)) ∂(K (localMeanZeroObs α₀ (ball c₂ r₂) (hC ω))) := by
    have hres : (μ ω).restrict (ball c₁ r₁) =
        c⁻¹ • (K (localMeanZeroObs α₀ (ball c₂ r₂) (hC ω))).restrict (ball c₁ r₁) := by
      calc (μ ω).restrict (ball c₁ r₁) = ((μ ω).restrict (ball c₂ r₂)).restrict (ball c₁ r₁) := by
            rw [Measure.restrict_restrict' measurableSet_ball, Set.inter_eq_left.mpr hUD]
        _ = (c⁻¹ • K (localMeanZeroObs α₀ (ball c₂ r₂) (hC ω))).restrict (ball c₁ r₁) := by rw [hD']
        _ = c⁻¹ • (K (localMeanZeroObs α₀ (ball c₂ r₂) (hC ω))).restrict (ball c₁ r₁) :=
            by rw [Measure.restrict_smul]
    show ∫⁻ z, (localBadSet K Q M a (ball c₁ r₁) nD).indicator (fun _ => (1 : ℝ≥0∞))
        (z, localMeanZeroObs α₀ (ball c₂ r₂) (hC ω)) ∂((μ ω).restrict (ball c₁ r₁)) = _
    rw [hres, lintegral_smul_measure]
    rfl
  show campbellRatio K (ball c₁ r₁) (localBadSet K Q M a (ball c₁ r₁) nD)
      (localMeanZeroObs α₀ (ball c₂ r₂) (hC ω)) = _
  rw [hμU, hμint]
  unfold campbellRatio
  exact (ennreal_ratio_cancel hc0' hcT').symm

end HarmonicBalls.S11c
