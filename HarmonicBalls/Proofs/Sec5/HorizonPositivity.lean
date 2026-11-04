import HarmonicBalls.Proofs.Sec5.CountableHorizonLaw
import HarmonicBalls.Steps.Sec5.ClusterBounds

/-! # Positive horizons from the uniform cluster bound -/

namespace HarmonicBalls

universe u

open MeasureTheory Metric Set ProbabilityTheory TopologicalSpace Filter
open scoped Pointwise

/-- Fixed-centre family measurability implies all countable membership tests
needed for the horizon law. -/
theorem countableClusterTests_of_familyMeasurability
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hfam : ClusterFamilyMeasurabilityStep.{u})
    {ι : Type*} (e : ι → {z // z ∈ ball (0 : ℂ) 1}) :
    ∀ i n m, AEMeasurable (fun ν : Measure ℂ =>
      denseSeq ℂ m ∈ cluster ν 1 (e i) (reciprocalTime n)) (Measure.map μ P) := by
  intro i n m
  exact ((hfam γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ (e i) (e i).property).eval
    (reciprocalTime n)).eval (denseSeq ℂ m)

/-- Proposition 7.1 supplies a strictly positive countable-centre horizon
inside the closed ball of radius `3/4`, uniformly over centres in `B(0,1/2)`. -/
theorem ae_countableCentresHorizon_pos_of_upperBound
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    {ι : Type*} (e : ι → {z // z ∈ ball (0 : ℂ) (1 / 2)}) :
    ∀ᵐ ω ∂P, 0 < realDenseSequenceBallHorizon (3 / 4)
      (fun i t => cluster (μ ω) 1 (e i) t) := by
  have hsmall := h71 γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ (1 / 2) (by norm_num)
  filter_upwards [hsmall.ae_eventually_dyadic] with ω hω
  obtain ⟨k, hk⟩ := hω.exists
  have hkpos : 0 < (2 : ℝ)⁻¹ ^ k := by positivity
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hkpos
  have htest : denseSequenceBallTest (3 / 4)
      (fun i t => cluster (μ ω) 1 (e i) t) n := by
    intro i m hm
    have hx := hk (reciprocalTime n) ⟨(reciprocalTime n).property, hn.le⟩
      (e i) (e i).property (subset_closure hm)
    have hz := (e i).property
    simp only [mem_ball] at hx hz
    simp only [mem_closedBall]
    have htri := dist_triangle (denseSeq ℂ m) (e i) (0 : ℂ)
    simp only [dist_zero_right] at htri
    norm_num at hx hz ⊢
    linarith
  have hp := denseSequenceBallHorizon_pos htest
  exact ENNReal.toReal_pos (ne_of_gt hp)
    (ne_top_of_le_ne_top (by simp) (denseSequenceBallHorizon_le_one _ _))


/-- The dyadically rescaled horizons have a common law and are positive
almost surely. Proposition 7.1 supplies positivity; fixed-centre family
measurability suffices for their common law. -/
theorem dyadicCountableCentresHorizons_of_steps
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hfam : ClusterFamilyMeasurabilityStep.{u})
    {ι : Type*} [Countable ι] (e : ι → {z // z ∈ ball (0 : ℂ) (1 / 2)}) :
    ∃ T : ℕ → Ω → ℝ,
      (∀ n, IdentDistrib (T n) (T 0) P P) ∧
      (∀ᵐ ω ∂P, 0 < T 0 ω) ∧
      ∀ n ω, T n ω = realDenseSequenceBallHorizon (3 / 4) (fun i t =>
        ((2 : ℝ) ^ n)⁻¹ • cluster (μ ω) ((2 : ℝ) ^ n)
          (((2 : ℝ) ^ n) • ((e i) : ℂ))
          (Real.exp (γ * (lqgQ γ * Real.log ((2 : ℝ) ^ n) +
            fieldCircleAverage α₀ (hcirc ω) ((2 : ℝ) ^ n) 0)) * t)) := by
  let e' : ι → {z // z ∈ ball (0 : ℂ) 1} := fun i =>
    ⟨e i, ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) (e i).property⟩
  let T : ℕ → Ω → ℝ := fun n ω => realDenseSequenceBallHorizon (3 / 4) (fun i t =>
    ((2 : ℝ) ^ n)⁻¹ • cluster (μ ω) ((2 : ℝ) ^ n)
      (((2 : ℝ) ^ n) • ((e i) : ℂ))
      (Real.exp (γ * (lqgQ γ * Real.log ((2 : ℝ) ^ n) +
        fieldCircleAverage α₀ (hcirc ω) ((2 : ℝ) ^ n) 0)) * t))
  have htests := countableClusterTests_of_familyMeasurability h hγ hγ2 hα hμ hfam e'
  have hlaw : ∀ n, IdentDistrib
      (fun ω => realDenseSequenceBallHorizon (3 / 4) (fun i t => cluster (μ ω) 1 (e i) t))
      (T n) P P := by
    intro n
    exact countableCentresHorizonScaleInvariance_of_measurable_tests h hAff hCC hγ hγ2 hα
      hμ e' (3 / 4) htests (by positivity)
  refine ⟨T, fun n => (hlaw n).symm.trans (hlaw 0), ?_, fun n ω => rfl⟩
  exact (hlaw 0).ae_snd measurableSet_Ioi
    (ae_countableCentresHorizon_pos_of_upperBound h hγ hγ2 hα hμ h71 e)

end HarmonicBalls
