import HarmonicBalls.Proofs.Sec5.UniformFinitePunctureContainment
import HarmonicBalls.Proofs.Sec5.LocallyFinitePunctureAdmissibility

/-! # Uniform small-time containment after locally finite deletion

A uniform small-time disc bound also controls every locally finite puncture set at
positive distance from the centre. -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- With polynomially high probability, for all small times and centres in
`B_{1/2}`, every nonempty locally finite set of punctures at distance at least
`r / 2` has a compactly contained punctured-disc cluster with inadmissible
least supersolution. -/
theorem polyHighProb_uniform_locally_finite_puncture_compact_not_admissible
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    PolyHighProb P (fun T => {ω | ∀ t ∈ Ioc (0 : ℝ) T,
      ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ K : Set ℂ,
      K ⊆ ball (0 : ℂ) 1 → K.Nonempty →
      (∀ ρ : ℝ, ρ < 1 → (K ∩ closedBall (0 : ℂ) ρ).Finite) →
      (∀ a ∈ K, r / 2 ≤ dist a z) →
      closure (clusterOn (μ ω) (ball (0 : ℂ) 1 \ K) z t) ⊆
        ball (0 : ℂ) 1 \ K ∧
      leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ K) z t ∉
        supersolutionsOn (μ ω) (ball (0 : ℂ) 1 \ K) z t}) := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  have hsmall := h71 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ r hr
  apply (hsmall.inter_ae hV).mono
  intro T ω hω t ht z hz K hK hKne hKloc hsep
  have hzK : z ∈ ball (0 : ℂ) 1 \ K := by
    refine ⟨ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) hz, ?_⟩
    intro hzmem
    have h := hsep z hzmem
    simp only [dist_self] at h
    linarith [hr.1]
  have hdisc : closure (cluster (μ ω) 1 z t) ⊆ ball (0 : ℂ) 1 \ K := by
    intro x hx
    have hnear : dist x z < r / 2 := mem_ball.mp (hω.1 t ht z hz hx)
    have hz0 : dist z (0 : ℂ) < 1 / 2 := mem_ball.mp hz
    refine ⟨mem_ball.mpr ?_, ?_⟩
    · have htri := dist_triangle x z (0 : ℂ)
      linarith [hr.2]
    · intro hxK
      have h := hsep x hxK
      linarith
  have hpunc : closure (clusterOn (μ ω) (ball (0 : ℂ) 1 \ K) z t) ⊆
      ball (0 : ℂ) 1 \ K := by
    rw [closure_clusterOn_locally_finite_punctured_disc_eq hω.2.1 zero_lt_one
      (hω.2.2 1 zero_lt_one) hKloc hzK ht.1]
    exact hdisc
  exact ⟨hpunc, not_mem_supersolutionsOn_locally_finite_punctured_of_compact_containment
    hω.2.1 zero_lt_one (hω.2.2 1 zero_lt_one) K hKne hKloc hK hzK ht.1 hpunc⟩

/-- For each prescribed positive separation below `1/2`, almost surely there
is a common positive horizon on which the uniform compact-containment and
inadmissibility conclusions hold. -/
theorem ae_uniform_locally_finite_puncture_compact_not_admissible
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, ∃ T : ℝ, 0 < T ∧ ∀ t ∈ Ioc (0 : ℝ) T,
      ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ K : Set ℂ,
      K ⊆ ball (0 : ℂ) 1 → K.Nonempty →
      (∀ ρ : ℝ, ρ < 1 → (K ∩ closedBall (0 : ℂ) ρ).Finite) →
      (∀ a ∈ K, r / 2 ≤ dist a z) →
      closure (clusterOn (μ ω) (ball (0 : ℂ) 1 \ K) z t) ⊆
        ball (0 : ℂ) 1 \ K ∧
      leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ K) z t ∉
        supersolutionsOn (μ ω) (ball (0 : ℂ) 1 \ K) z t := by
  have h := polyHighProb_uniform_locally_finite_puncture_compact_not_admissible
    hI2 h71 hγ hγ2 hα hGFF hμ hr
  filter_upwards [h.ae_eventually_dyadic] with ω hω
  obtain ⟨n, hn⟩ := hω.exists
  exact ⟨(2 : ℝ)⁻¹ ^ n, by positivity, hn⟩

/-- Almost surely, every positive separation admits one common horizon for
all centres and all nonempty locally finite puncture sets at that separation. -/
theorem ae_uniform_locally_finite_puncture_compact_not_admissible_all_separations
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ t ∈ Ioc (0 : ℝ) T,
      ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ K : Set ℂ,
      K ⊆ ball (0 : ℂ) 1 → K.Nonempty →
      (∀ ρ : ℝ, ρ < 1 → (K ∩ closedBall (0 : ℂ) ρ).Finite) →
      (∀ a ∈ K, ε ≤ dist a z) →
      closure (clusterOn (μ ω) (ball (0 : ℂ) 1 \ K) z t) ⊆
        ball (0 : ℂ) 1 \ K ∧
      leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ K) z t ∉
        supersolutionsOn (μ ω) (ball (0 : ℂ) 1 \ K) z t := by
  have hevent : ∀ n : ℕ, ∀ᵐ ω ∂P, ∃ T : ℝ, 0 < T ∧ ∀ t ∈ Ioc (0 : ℝ) T,
      ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ K : Set ℂ,
      K ⊆ ball (0 : ℂ) 1 → K.Nonempty →
      (∀ ρ : ℝ, ρ < 1 → (K ∩ closedBall (0 : ℂ) ρ).Finite) →
      (∀ a ∈ K, ((2 : ℝ)⁻¹ ^ n / 2) / 2 ≤ dist a z) →
      closure (clusterOn (μ ω) (ball (0 : ℂ) 1 \ K) z t) ⊆
        ball (0 : ℂ) 1 \ K ∧
      leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ K) z t ∉
        supersolutionsOn (μ ω) (ball (0 : ℂ) 1 \ K) z t := by
    intro n
    have hr : ((2 : ℝ)⁻¹ ^ n / 2) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · positivity
      · have hp : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        linarith
    exact ae_uniform_locally_finite_puncture_compact_not_admissible hI2 h71 hγ hγ2 hα hGFF hμ hr
  filter_upwards [ae_all_iff.mpr hevent] with ω hω
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 : ℝ)⁻¹ < 1)
  obtain ⟨T, hT, hbound⟩ := hω n
  refine ⟨T, hT, fun t ht z hz K hK hKne hKloc hsep => hbound t ht z hz K hK hKne hKloc ?_⟩
  intro a ha
  have hp : 0 ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  have h := hsep a ha
  linarith

#print axioms ae_uniform_locally_finite_puncture_compact_not_admissible_all_separations

#print axioms polyHighProb_uniform_locally_finite_puncture_compact_not_admissible
#print axioms ae_uniform_locally_finite_puncture_compact_not_admissible

end HarmonicBalls
