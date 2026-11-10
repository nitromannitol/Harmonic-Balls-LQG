import HarmonicBalls.FirstPass.S11r.RootedNull

/-!
# Joint measurability of the rooted observation; the rooted null transfer without `hmeas` (fp-S11r, owner n2)

`ae_root_rootedObs_eq_zero_of_obs_null` (RootedNull.lean) keeps the joint measurability of
`(z, ω) ↦ 1_A(obs_D f_z(ω))` as a side hypothesis `hmeas`. Here that hypothesis is proved from the measurability of
the pairings of a whole-plane GFF (`IsWholePlaneGFF.measurable_pairing`) and Tonelli (`Measurable.lintegral_prod_right'`),
so the Lebesgue-a.e. root statement of CHATGPT-n3-B1-B2.md section 4.2 needs no extra hypothesis.

The root enters the reference observation (`campbellReferenceObs`) only through the deterministic kernel
`z ↦ ∫ (log|w - z| - log max(1,|w|)) φ(w) dw`, whose joint measurability in `(z, w)` is clear, and the sample point
enters only through the pairings `ω ↦ h^ℂ(ω)(φ)`.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

universe u

/-- The rooted reference observation is jointly measurable in the root `z` and the sample point `ω`. -/
theorem measurable_campbellReferenceObs_joint {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (γ α₀ : ℝ) (D : Set ℂ) :
    Measurable (fun q : ℂ × Ω => campbellReferenceObs γ α₀ D (hC q.2) q.1) := by
  apply Measurable.prodMk measurable_fst
  refine Measurable.of_eval (fun φ => ?_)
  have hφ : IsTestFunction Set.univ φ.1 := ⟨φ.2.1.1, φ.2.1.2.1, Set.subset_univ _⟩
  show Measurable fun q : ℂ × Ω =>
    fieldPairing α₀ (hC q.2) φ.1 - γ * ∫ w, (Real.log ‖w - q.1‖ - Real.log (max 1 ‖w‖)) * φ.1 w
  -- the sample-point part: a pairing of the whole-plane GFF, shifted by a constant
  have hA : Measurable fun q : ℂ × Ω => fieldPairing α₀ (hC q.2) φ.1 := by
    unfold fieldPairing
    exact ((hGFF.measurable_pairing φ.1 hφ).comp measurable_snd).sub_const _
  -- the root part: Tonelli for the jointly measurable kernel in `(z, w)`
  have hn : Measurable fun q : ℂ × ℂ => ‖q.2 - q.1‖ :=
    (continuous_norm.comp (continuous_snd.sub continuous_fst)).measurable
  have hl1 : Measurable fun q : ℂ × ℂ => Real.log ‖q.2 - q.1‖ := Real.measurable_log.comp hn
  have hl2 : Measurable fun q : ℂ × ℂ => Real.log (max 1 ‖q.2‖) :=
    Real.measurable_log.comp ((measurable_const.max measurable_norm).comp measurable_snd)
  have hφc : Measurable fun q : ℂ × ℂ => φ.1 q.2 :=
    (φ.2.1.1.continuous.measurable).comp measurable_snd
  have hK : Measurable fun q : ℂ × ℂ => (Real.log ‖q.2 - q.1‖ - Real.log (max 1 ‖q.2‖)) * φ.1 q.2 :=
    ((hl1.sub hl2)).mul hφc
  have hB : Measurable fun z : ℂ => ∫ w, (Real.log ‖w - z‖ - Real.log (max 1 ‖w‖)) * φ.1 w :=
    (StronglyMeasurable.integral_prod_right' (ν := volume) hK.stronglyMeasurable).measurable
  exact hA.sub (measurable_const.mul (hB.comp measurable_fst))

/-- **Rooted null transfer, without the side hypothesis.** The statement of
`ae_root_rootedObs_eq_zero_of_obs_null` (RootedNull.lean) with the joint measurability `hmeas` proved from the GFF
pairings (`measurable_campbellReferenceObs_joint`). -/
theorem ae_root_rootedObs_eq_zero_of_obs_null_noMeas (hI1 : LocalMarkedRootingIdentityFrozen.{u})
    {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂) (h0 : (0 : ℂ) ∉ closedBall c₂ r₂)
    (A : Set ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)) (hA : MeasurableSet A)
    (hnull : ∀ᵐ ω ∂P, (fun φ => fieldPairing α₀ (hC ω) φ.1) ∉ A) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)),
      ∫⁻ ω, (univ ×ˢ A).indicator (fun _ => (1 : ℝ≥0∞))
        (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P = 0 := by
  have hS : MeasurableSet (univ ×ˢ A : Set (ℂ ×
      ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ))) :=
    MeasurableSet.univ.prod hA
  have hG : Measurable (fun q : ℂ × Ω => (univ ×ˢ A).indicator (fun _ => (1 : ℝ≥0∞))
      (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC q.2) q.1)) :=
    (measurable_const.indicator hS).comp
      (measurable_campbellReferenceObs_joint P hC hcirc hGFF γ α₀ (ball c₂ r₂))
  exact ae_root_rootedObs_eq_zero_of_obs_null hI1 hγ0 hγ2 hα Ω P hC hcirc μ hGFF hμ hr₁ hr₂ hsub h0 A hA hnull
    (hG.lintegral_prod_right'.aemeasurable)

#print axioms HarmonicBalls.measurable_campbellReferenceObs_joint
#print axioms HarmonicBalls.ae_root_rootedObs_eq_zero_of_obs_null_noMeas

end HarmonicBalls
