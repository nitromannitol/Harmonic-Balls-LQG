import HarmonicBalls.Proofs.Sec8.OrdinaryFieldNormalizedRestriction

/-! # Centered LQG approximations

Subtracting one circle average removes a common additive constant from each
finite-scale density. The corresponding normalized measures are unchanged.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace HarmonicBalls

/-- The LQG approximation after subtracting its circle average at a fixed
reference point. The deterministic regularization factor is omitted because
it also cancels on normalization. -/
noncomputable def centeredLQGApprox (γ : ℝ) (hε : ℝ → ℂ → ℝ)
    (ε : ℝ) (z₀ : ℂ) : Measure ℂ :=
  volume.withDensity fun z => ENNReal.ofReal (Real.exp (γ * (hε ε z - hε ε z₀)))

/-- The original approximation and the centered approximation have the same
normalized restriction at every strictly positive regularization scale. -/
theorem normalizedRestriction_lqgApprox_eq_centered (γ : ℝ)
    (hε : ℝ → ℂ → ℝ) {ε : ℝ} (hεpos : 0 < ε) (z₀ : ℂ) (U : Set ℂ) :
    normalizedRestriction (lqgApprox γ hε ε) U =
      normalizedRestriction (centeredLQGApprox γ hε ε z₀) U := by
  let c : ℝ := ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε z₀)
  have hc : 0 < c := mul_pos (Real.rpow_pos_of_pos hεpos _) (Real.exp_pos _)
  have hmeasure : lqgApprox γ hε ε = ENNReal.ofReal c • centeredLQGApprox γ hε ε z₀ := by
    unfold lqgApprox centeredLQGApprox
    rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul hc.le]
    congr 1
    dsimp [c]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hmeasure]
  exact normalizedRestriction_smul _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top

/-- Joint measurability of the centered circle-average field implies
measurability of its finite-scale normalized restriction. -/
theorem measurable_normalized_centeredLQGApprox {Ω : Type*} [MeasurableSpace Ω]
    (γ : ℝ) (d : Ω → ℂ → ℝ) (hd : Measurable (Function.uncurry d))
    (U : Set ℂ) (hU : MeasurableSet U) :
    Measurable (fun ω => normalizedRestriction
      (volume.withDensity fun z => ENNReal.ofReal (Real.exp (γ * d ω z))) U) := by
  have hm : Measurable (fun ω => volume.withDensity
      (fun z => ENNReal.ofReal (Real.exp (γ * d ω z)))) := by
    apply measurable_withDensity
    exact ((measurable_const.mul hd).exp).ennreal_ofReal
  exact (measurable_normalizedRestriction_measure U hU).comp hm

/-- Only the centered circle averages inside the reference set affect the
normalized approximation. -/
theorem normalizedRestriction_lqgApprox_eq_of_centered_on (γ : ℝ)
    (hε : ℝ → ℂ → ℝ) {ε : ℝ} (hεpos : 0 < ε) (z₀ : ℂ)
    {U : Set ℂ} (hU : MeasurableSet U) (d : ℂ → ℝ)
    (hd : ∀ z ∈ U, d z = hε ε z - hε ε z₀) :
    normalizedRestriction (lqgApprox γ hε ε) U =
      normalizedRestriction (volume.withDensity fun z =>
        ENNReal.ofReal (Real.exp (γ * d z))) U := by
  rw [normalizedRestriction_lqgApprox_eq_centered γ hε hεpos z₀ U]
  apply normalizedRestriction_eq_of_restrict_eq_smul hU (c := 1) one_ne_zero ENNReal.one_ne_top
  rw [one_smul, centeredLQGApprox, restrict_withDensity hU, restrict_withDensity hU]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hU] with z hz
  rw [hd z hz]

/-- A limit of normalized approximating masses has a local measurable
version if the centered circle-average fields have jointly measurable local
versions. The convergence hypothesis is stated separately. -/
theorem exists_local_ratio_version_of_centered_approximations
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω) (γ : ℝ) (hε : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) {U A : Set ℂ} (hA : MeasurableSet A)
    (Uapprox : ℕ → Set ℂ) (hUapprox : ∀ n, MeasurableSet (Uapprox n))
    (z₀ : ℂ) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (d : ℕ → Ω → ℂ → ℝ)
    (hdm : ∀ n, @Measurable (Ω × ℂ) ℝ (m.prod inferInstance) _
      (Function.uncurry (d n)))
    (hdeq : ∀ n, ∀ᵐ ω ∂P, ∀ z ∈ Uapprox n,
      d n ω z = hε ω (r n) z - hε ω (r n) z₀)
    (hlim : ∀ᵐ ω ∂P, Tendsto
      (fun n => normalizedRestriction (lqgApprox γ (hε ω) (r n)) (Uapprox n) A)
      atTop (𝓝 (μ ω (A ∩ U) / μ ω U))) :
    ∃ Y : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞ m _ Y ∧
      (fun ω => μ ω (A ∩ U) / μ ω U) =ᵐ[P] Y := by
  let Y : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    normalizedRestriction (volume.withDensity fun z =>
      ENNReal.ofReal (Real.exp (γ * d n ω z))) (Uapprox n) A
  have hYm : ∀ n, @Measurable Ω ℝ≥0∞ m _ (Y n) := by
    intro n
    exact (Measure.measurable_coe hA).comp
      (@measurable_normalized_centeredLQGApprox Ω m γ (d n) (hdm n) (Uapprox n) (hUapprox n))
  have hYlim : @Measurable Ω ℝ≥0∞ m _
      (fun ω => Filter.liminf (fun n => Y n ω) atTop) := by
    let : MeasurableSpace Ω := m
    exact Measurable.liminf hYm
  refine ⟨fun ω => Filter.liminf (fun n => Y n ω) atTop, hYlim, ?_⟩
  filter_upwards [hlim, ae_all_iff.mpr hdeq] with ω hω heq
  have he : ∀ n, Y n ω = normalizedRestriction
      (lqgApprox γ (hε ω) (r n)) (Uapprox n) A := by
    intro n
    exact congrArg (fun ν : Measure ℂ => ν A)
      (normalizedRestriction_lqgApprox_eq_of_centered_on γ (hε ω)
        (hr n) z₀ (hUapprox n) (d n ω) (heq n)).symm
  simp_rw [he]
  exact hω.liminf_eq.symm

end HarmonicBalls
