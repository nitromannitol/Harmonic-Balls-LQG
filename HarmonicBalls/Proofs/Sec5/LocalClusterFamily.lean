import HarmonicBalls.Proofs.Sec5.LocalMeasureEvaluations

/-! # Local representation of the positive-time disc cluster family -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- The entire positive-time disc cluster family has a representative measurable
with respect to the field on the disc, with the pointwise evaluation σ-algebra
on the family. The equality holds simultaneously for all centres and times. -/
theorem exists_local_lqg_clusterFamily_representative
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) {R : ℝ} (hR : 0 < R) :
    ∃ F : Ω → (ball (0 : ℂ) R × Ioi (0 : ℝ) → Set ℂ),
      Measurable[fieldSigmaAlgebra α₀ hC (ball 0 R)] F ∧
      ∀ᵐ ω ∂P, F ω = fun p => cluster (μ ω) R p.1 p.2 := by
  classical
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (greenPotentialBall (μ ω) R) (closedBall 0 R) := by
    filter_upwards [hae] with ω hω
    exact greenPotentialBallContinuousStep_holds _ hω.1 R βm βp hR (hω.2 R hR)
  obtain ⟨Q, hQ, hQeq⟩ := exists_local_lqg_greenPotentialBall_continuous_representative
    hγ hγ2 hα hGFF hμ hloc hR hcont
  let J := ball (0 : ℂ) R × Ioi (0 : ℝ)
  let G : J → ℂ → C(closedBall (0 : ℂ) R, ℝ) → ℝ := fun p x =>
    if h : x ∈ ball (0 : ℂ) R ∧ x ≠ p.1 then
      Classical.choose (exists_continuous_shiftedOdometer_decoder hR p.1.property p.2.property h.1 h.2)
    else fun _ => 0
  have hG : ∀ p x, Continuous (G p x) := by
    intro p x
    dsimp only [G]
    split_ifs with h
    · exact (Classical.choose_spec
        (exists_continuous_shiftedOdometer_decoder hR p.1.property p.2.property h.1 h.2)).1
    · exact continuous_const
  let F : Ω → J → Set ℂ := fun ω p =>
    {x | x ∈ ball (0 : ℂ) R ∧ (x = p.1 ∨ 0 < G p x (Q ω))}
  have hF : Measurable[fieldSigmaAlgebra α₀ hC (ball 0 R)] F := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC (ball 0 R)
    apply Measurable.of_eval
    intro p
    apply Measurable.of_eval
    intro x
    exact measurable_const.and (measurable_const.or (measurable_const.lt ((hG p x).measurable.comp hQ)))
  refine ⟨F, hF, ?_⟩
  filter_upwards [hae, hQeq] with ω hω hqω
  funext p
  ext x
  by_cases hx : x ∈ ball (0 : ℂ) R
  · by_cases hxz : x = p.1
    · change (x ∈ ball (0 : ℂ) R ∧ (x = p.1 ∨ 0 < G p x (Q ω))) ↔ _
      rw [mem_cluster_iff]
      simp only [hxz, true_or]
    · have hgood := (Classical.choose_spec
        (exists_continuous_shiftedOdometer_decoder hR p.1.property p.2.property hx hxz)).2
      have hgeq : shiftedOdometer (μ ω) R p.1 p.2 x = G p x (Q ω) := by
        have hp : x ∈ ball (0 : ℂ) R ∧ x ≠ p.1 := ⟨hx, hxz⟩
        simpa only [G, dite_eq_left hp] using
          hgood (μ ω) hω.1 ⟨βm, βp, hω.2 R hR⟩ (Q ω) hqω
      have heq := (obstacleCompatibilityShiftStep_holds (μ ω) hω.1 R βm βp hR
        (hω.2 R hR) p.1 p.1.property p.2 p.2.property).2.2.1
      rw [heq, mem_nonCoincidenceSet_iff]
      simp only [F, mem_ofPred_eq, hx, hxz, false_or, true_and, hgeq]
  · change (x ∈ ball (0 : ℂ) R ∧ (x = p.1 ∨ 0 < G p x (Q ω))) ↔ _
    rw [mem_cluster_iff]
    simp only [hx, false_and]

/-- The regularized cluster family has a local representative on the same
full-measure event, simultaneously for all centres and positive times. -/
theorem exists_local_lqg_regularizedClusterFamily_representative
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) {R : ℝ} (hR : 0 < R) :
    ∃ F : Ω → (ball (0 : ℂ) R × Ioi (0 : ℝ) → Set ℂ),
      Measurable[fieldSigmaAlgebra α₀ hC (ball 0 R)] F ∧
      ∀ᵐ ω ∂P, F ω = fun p => regularizedCluster (μ ω) R p.1 p.2 := by
  obtain ⟨F, hF, hEq⟩ := exists_local_lqg_clusterFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc hR
  refine ⟨fun ω p => denseSequenceRegularization (F ω p),
    measurable_denseSequenceRegularization_family.comp hF, ?_⟩
  filter_upwards [hEq, clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα
    Ω P hC hcirc μ hGFF hμ] with ω heq hopen
  funext p
  rw [heq]
  exact denseSequenceRegularization_eq (hopen p.2 R p.2.property hR p.1 p.1.property).1

end HarmonicBalls
