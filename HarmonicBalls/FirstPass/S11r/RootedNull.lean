import HarmonicBalls.FirstPass.S11r.FrozenMetricReplacement

/-!
# Rooted null transfer from the marked rooting identity

The Tonelli step: the frozen marked identity `LocalMarkedRootingIdentityWeightedFrozen` (the unweighted `LocalMarkedRootingIdentityFrozen` is RETIRED)
(equation (24), marked form) tested with the set `S = univ ×ˢ A` of marked observations. If the ordinary local
observation `obs_D h = (φ ↦ fieldPairing α₀ (hC ω) φ)` of the LQG-weighted field lies a.s. outside `A`, then the
reference mixture over the root `z ∈ U` gives mass zero to `A`, that is `∫_U P[obs_D f_z ∈ A] dz = 0` (the domination
(25) `R ≪ Q` in the form used for Lebesgue-a.e. roots). Measure theory on top of the frozen input only.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

universe u

/-- The root weight `rootWeight γ α₀` is measurable in the root. -/
theorem measurable_rootWeight (γ α₀ : ℝ) : Measurable (rootWeight γ α₀) := by
  unfold rootWeight
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
  exact ((measurable_const.mul (Real.measurable_log.comp measurable_norm)).add
    (measurable_const.mul (Real.measurable_log.comp (measurable_norm.max measurable_const))))

/-- The root weight is strictly positive at every root (it is `exp` of a real number). -/
theorem rootWeight_ne_zero (γ α₀ : ℝ) (z : ℂ) : rootWeight γ α₀ z ≠ 0 :=
  (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'

/-- **Null transfer over the root.** Let `h = h^ℂ - α₀ log|·|` be the LQG-weighted whole-plane field with
`IsLQGMeasureOfField P γ α₀ hcirc μ`, and let `A` be a measurable set of mean-zero observables in `D = ball c₂ r₂`.
If `obs_D h ∉ A` almost surely, then the rooted mixture over `U = ball c₁ r₁` vanishes on `A`:
`∫_U (∫ 1_A(obs_D f_z) dP) dz = 0`, where `f_z` is the reference observation `campbellReferenceObs`. -/
theorem lintegral_rootedObs_eq_zero_of_obs_null (hI1 : LocalMarkedRootingIdentityWeightedFrozen.{u})
    {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂) (h0 : (0 : ℂ) ∉ closedBall c₂ r₂)
    (A : Set ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)) (hA : MeasurableSet A)
    (hnull : ∀ᵐ ω ∂P, (fun φ => fieldPairing α₀ (hC ω) φ.1) ∉ A) :
    ∫⁻ z in ball c₁ r₁,
      rootWeight γ α₀ z * (∫⁻ ω, (univ ×ˢ A).indicator (fun _ => (1 : ℝ≥0∞)) (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P)
      = 0 := by
  have hS : MeasurableSet (univ ×ˢ A : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ))) :=
    MeasurableSet.univ.prod hA
  have key := hI1 γ α₀ hγ0 hγ2 hα Ω P hC hcirc μ hGFF hμ c₁ c₂ r₁ r₂ hr₁ hr₂ hsub h0 (univ ×ˢ A) hS
  have hL : (∫⁻ ω, ∫⁻ z in ball c₁ r₁,
      (univ ×ˢ A).indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω) ∂P) = 0 := by
    have hzero : ∀ᵐ ω ∂P, ∫⁻ z in ball c₁ r₁,
        (univ ×ˢ A).indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω) = 0 := by
      filter_upwards [hnull] with ω hω
      have hpt : ∀ z : ℂ, (univ ×ˢ A).indicator (fun _ => (1 : ℝ≥0∞))
          (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) = 0 := by
        intro z
        have hnot : campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z ∉ univ ×ˢ A :=
          fun h => hω h.2
        exact indicator_of_notMem hnot _
      simp [hpt]
    rw [lintegral_congr_ae hzero, lintegral_zero]
  rw [hL] at key
  exact key.symm

/-- **Lebesgue-a.e. root**. Under the same hypotheses, if the
root-wise rooted probabilities are AE-measurable in `z` (hypothesis `hmeas`: joint measurability of
`(z, ω) ↦ 1_A(obs_D f_z(ω))`, a Fubini step not yet formalised here, kept explicit), then for Lebesgue-a.e. root
`z ∈ U` the reference observation `obs_D f_z` is P-null on `A`. -/
theorem ae_root_rootedObs_eq_zero_of_obs_null (hI1 : LocalMarkedRootingIdentityWeightedFrozen.{u})
    {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂) (h0 : (0 : ℂ) ∉ closedBall c₂ r₂)
    (A : Set ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)) (hA : MeasurableSet A)
    (hnull : ∀ᵐ ω ∂P, (fun φ => fieldPairing α₀ (hC ω) φ.1) ∉ A)
    (hmeas : AEMeasurable (fun z => ∫⁻ ω, (univ ×ˢ A).indicator (fun _ => (1 : ℝ≥0∞))
      (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P) (volume.restrict (ball c₁ r₁))) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)),
      ∫⁻ ω, (univ ×ˢ A).indicator (fun _ => (1 : ℝ≥0∞))
        (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P = 0 :=
  by
  have hzero := lintegral_rootedObs_eq_zero_of_obs_null hI1 hγ0 hγ2 hα Ω P hC hcirc μ hGFF hμ hr₁ hr₂ hsub h0 A hA hnull
  have hW : AEMeasurable (fun z => rootWeight γ α₀ z * ∫⁻ ω, (univ ×ˢ A).indicator (fun _ => (1 : ℝ≥0∞))
      (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P) (volume.restrict (ball c₁ r₁)) :=
    (measurable_rootWeight γ α₀).aemeasurable.mul hmeas
  have hae := (lintegral_eq_zero_iff' hW).1 hzero
  filter_upwards [hae] with z hz
  rcases mul_eq_zero.1 hz with h | h
  · exact absurd h (rootWeight_ne_zero γ α₀ z)
  · exact h


end HarmonicBalls
