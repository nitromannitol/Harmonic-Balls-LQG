import HarmonicBalls.Proofs.Sec5.PuncturedDiscInadmissibility

/-! # Uniform small-time inadmissibility at punctures

The unit-disc upper bound applies simultaneously to all centres and all
punctures separated from the centre by a fixed positive distance.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- For any fixed separation, the punctured-domain infimum is inadmissible
simultaneously for all centres and punctures, with polynomially high probability
as the time horizon tends to zero. -/
theorem polyHighProb_uniform_punctured_disc_infimum_not_admissible
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    PolyHighProb P (fun T => {ω | ∀ t ∈ Ioc (0 : ℝ) T,
      ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ a ∈ ball (0 : ℂ) 1,
      r / 2 ≤ dist a z →
      leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ {a}) z t ∉
        supersolutionsOn (μ ω) (ball (0 : ℂ) 1 \ {a}) z t}) := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  have hsmall := h71 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ r hr
  apply (hsmall.inter_ae hV).mono
  intro T ω hω t ht z hz a ha hdist
  have hza : z ≠ a := by
    intro heq
    subst z
    simp only [dist_self] at hdist
    linarith [hr.1]
  have hzU : z ∈ ball (0 : ℂ) 1 \ {a} :=
    ⟨ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) hz, by simpa using hza⟩
  have hnot : a ∉ cluster (μ ω) 1 z t := by
    intro hacl
    have hbound := hω.1 t ht z hz (subset_closure hacl)
    have : dist a z < r / 2 := hbound
    linarith
  exact punctured_disc_infimum_not_admissible_of_not_mem_cluster hω.2.1 zero_lt_one
    (hω.2.2 1 zero_lt_one) ha hzU ht.1 hnot

/-- Almost surely, every centre in the half disc and every distinct puncture
in the unit disc have a positive interval of inadmissibility. The horizon can
be chosen uniformly when their separation has a fixed positive lower bound. -/
theorem ae_uniform_punctured_disc_infimum_not_admissible
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) (1 / 2),
      ∀ a ∈ ball (0 : ℂ) 1, ε ≤ dist a z →
      leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ {a}) z t ∉
        supersolutionsOn (μ ω) (ball (0 : ℂ) 1 \ {a}) z t := by
  have hevent : ∀ n : ℕ, ∀ᵐ ω ∂P, ∃ T : ℝ, 0 < T ∧
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) (1 / 2),
      ∀ a ∈ ball (0 : ℂ) 1, ((2 : ℝ)⁻¹ ^ n / 2) / 2 ≤ dist a z →
      leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ {a}) z t ∉
        supersolutionsOn (μ ω) (ball (0 : ℂ) 1 \ {a}) z t := by
    intro n
    have hr : ((2 : ℝ)⁻¹ ^ n / 2) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · positivity
      · have hp : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        linarith
    have h := polyHighProb_uniform_punctured_disc_infimum_not_admissible
      hI2 h71 hγ hγ2 hα hGFF hμ hr
    filter_upwards [h.ae_eventually_dyadic] with ω hω
    obtain ⟨m, hm⟩ := hω.exists
    exact ⟨(2 : ℝ)⁻¹ ^ m, by positivity, hm⟩
  filter_upwards [ae_all_iff.mpr hevent] with ω hω
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 : ℝ)⁻¹ < 1)
  obtain ⟨T, hT, hbound⟩ := hω n
  refine ⟨T, hT, fun t ht z hz a ha hdist => hbound t ht z hz a ha ?_⟩
  have hp : 0 ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  linarith

end HarmonicBalls
