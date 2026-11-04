import HarmonicBalls.Proofs.Sec5.ExitHorizon

/-! # Scale laws from countably many cluster evaluations -/

namespace HarmonicBalls

universe u

open MeasureTheory Metric Set ProbabilityTheory TopologicalSpace
open scoped Pointwise

/-- To measure the horizon, it suffices to measure the countably many dense
point tests at reciprocal times. No other evaluations of the family are used. -/
theorem measurable_realDenseSequenceBallHorizon_of_tests {Ω ι : Type*}
    [MeasurableSpace Ω] [Countable ι] (r : ℝ)
    (F : Ω → ι → Ioi (0 : ℝ) → Set ℂ)
    (h : ∀ i n m, Measurable (fun ω => denseSeq ℂ m ∈ F ω i (reciprocalTime n))) :
    Measurable (fun ω => realDenseSequenceBallHorizon r (F ω)) := by
  classical
  apply Measurable.ennreal_toReal
  change Measurable (fun ω => ⨆ n, if denseSequenceBallTest r (F ω) n then
    ENNReal.ofReal (reciprocalTime n) else 0)
  apply Measurable.iSup
  intro n
  apply Measurable.ite _ measurable_const measurable_const
  apply measurableSet_setOfPred.mpr
  unfold denseSequenceBallTest
  apply Measurable.forall
  intro i
  apply Measurable.forall
  intro m
  exact (h i n m).imp measurable_const

/-- A dense set of centres recovers the union of a set-valued family whose
membership is open in the centre. -/
theorem subset_iUnion_of_isOpen_centres {ι J : Type*} [TopologicalSpace J]
    (e : ι → J) (he : DenseRange e) (F : J → Set ℂ)
    (hopen : ∀ x, IsOpen {j | x ∈ F j}) (j : J) :
    F j ⊆ ⋃ i, F (e i) := by
  intro x hx
  obtain ⟨i, hi⟩ := he.exists_mem_open (hopen x) ⟨j, hx⟩
  exact mem_iUnion.mpr ⟨i, hi⟩

/-- A horizon decoder on the profile of countable centre, time and point
tests. -/
noncomputable def realCountableTestHorizon {ι : Type*} (r : ℝ)
    (G : ι → ℕ → ℕ → Prop) : ℝ := by
  classical
  exact (⨆ n, if ∀ i m, G i n m → denseSeq ℂ m ∈ closedBall (0 : ℂ) r then
    ENNReal.ofReal (reciprocalTime n) else 0).toReal

/-- The profile decoder is measurable in the product measurable structure. -/
theorem measurable_realCountableTestHorizon {ι : Type*} [Countable ι] (r : ℝ) :
    Measurable (realCountableTestHorizon (ι := ι) r) := by
  classical
  apply Measurable.ennreal_toReal
  change Measurable (fun G : ι → ℕ → ℕ → Prop => ⨆ n,
    if ∀ i m, G i n m → denseSeq ℂ m ∈ closedBall (0 : ℂ) r then
      ENNReal.ofReal (reciprocalTime n) else 0)
  apply Measurable.iSup
  intro n
  apply Measurable.ite _ measurable_const measurable_const
  apply measurableSet_setOfPred.mpr
  apply Measurable.forall
  intro i
  apply Measurable.forall
  intro m
  have hg : Measurable (fun G : ι → ℕ → ℕ → Prop => G i n m) :=
    (measurable_pi_apply m).comp ((measurable_pi_apply n).comp (measurable_pi_apply i))
  exact hg.imp measurable_const

/-- Almost-everywhere measurability of the countably many tests suffices for
almost-everywhere measurability of the horizon. -/
theorem aemeasurable_realDenseSequenceBallHorizon_of_tests {Ω ι : Type*}
    [MeasurableSpace Ω] [Countable ι] (P : Measure Ω) (r : ℝ)
    (F : Ω → ι → Ioi (0 : ℝ) → Set ℂ)
    (h : ∀ i n m, AEMeasurable (fun ω => denseSeq ℂ m ∈ F ω i (reciprocalTime n)) P) :
    AEMeasurable (fun ω => realDenseSequenceBallHorizon r (F ω)) P := by
  have hp : AEMeasurable (fun ω i n m => denseSeq ℂ m ∈ F ω i (reciprocalTime n)) P := by
    apply AEMeasurable.of_eval
    intro i
    apply AEMeasurable.of_eval
    intro n
    apply AEMeasurable.of_eval
    intro m
    exact h i n m
  exact (measurable_realCountableTestHorizon r).comp_aemeasurable hp

/-- Scaling preserves the horizon law when its countable cluster-membership
tests are measurable. The two field inputs remain explicit hypotheses. -/
theorem countableCentresHorizonScaleInvariance_of_measurable_tests
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {ι : Type*} [Countable ι] (e : ι → {z // z ∈ ball (0 : ℂ) 1}) (r : ℝ)
    (hmeas : ∀ i n m, AEMeasurable (fun ν : Measure ℂ =>
      denseSeq ℂ m ∈ cluster ν 1 (e i) (reciprocalTime n)) (Measure.map μ P))
    {k : ℝ} (hk : 0 < k) :
    IdentDistrib
      (fun ω => realDenseSequenceBallHorizon r
        (fun i t => cluster (μ ω) 1 (e i) t))
      (fun ω => realDenseSequenceBallHorizon r (fun i t =>
        k⁻¹ • cluster (μ ω) k (k • ((e i) : ℂ))
          (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0)) * t)))
      P P := by
  have hobs : AEMeasurable (fun ν : Measure ℂ => realDenseSequenceBallHorizon r
      (fun i t => cluster ν 1 (e i) t)) (Measure.map μ P) :=
    aemeasurable_realDenseSequenceBallHorizon_of_tests (Measure.map μ P) r _ hmeas
  have hd := (h.identDistrib_normalizedPullback hAff hCC hγ hγ2 hα hμ hk).comp_of_aemeasurable hobs
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [clusterPathwiseScaleStep_proved γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ k hk] with ω hω
  change realDenseSequenceBallHorizon r (fun i t =>
    cluster (normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) 1 (e i) t) = _
  apply congrArg (realDenseSequenceBallHorizon r)
  funext i t
  exact hω (e i) (e i).property t t.property

end HarmonicBalls
