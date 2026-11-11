import HarmonicBalls.Proofs.Sec11.ClosureScales.UniversalCircleLaw
import HarmonicBalls.Proofs.Sec5.LQGApproxDecoder

/-!
# LQG approximations of canonical profiles

Source: the measure part `m_{γ,α}`. For a canonical profile `f` (a continuous circle-average profile on `J = (0,∞) × ℂ`), the approximations
`ε^{γ²/2} e^{γ h_ε(z)} dz` along the dyadic scales `ε = 2^{-k}` are defined through the measurable decoder of
`Sec5/LQGApproxDecoder.lean`. This file proves four facts:
* the approximation is measurable in `f`, and so is the integral of each compactly supported continuous test;
* it is locally finite, and it equals the LQG approximation of the field `(r,z) ↦ f(r,z)` (`lqgApprox`);
* `IsLQGLimit` depends only on the field at the dyadic radii, so the vague limit of `IsLQGLimit` for `hcirc ω`
  transfers to the canonical profile of `ω` whenever the two agree on `J`.

The LQG density is the one of `IsLQGLimit` (Defs/LQG.lean), that is Duplantier-Sheffield 2011, eq. (1.3) and Prop. 1.1.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology ProbabilityTheory

/-- The field `(r,z) ↦ f(r,z)` of a canonical profile. -/
def profileField (f : CanonicalProfile) : ℝ → ℂ → ℝ :=
  fun r z => f.1 (r, z)

/-- The radius-`r` exponent `z ↦ h_r(z) - α₀ log max(r,|z|)` of the LQG density, for a canonical profile
(`fieldCircleAverage`, Defs/GFF.lean). -/
noncomputable def profileRadiusField (α₀ r : ℝ) (f : CanonicalProfile) : ℂ → ℝ :=
  fun z => fieldCircleAverage α₀ (profileField f) r z

/-- A measurable decoder of the LQG approximation at a fixed radius (Sec5, `exists_measurable_lqgApprox_decoder`):
it agrees with `lqgApprox` on continuous exponents. -/
noncomputable def profileDecoder (γ r : ℝ) : (ℂ → ℝ) → Measure ℂ :=
  (exists_measurable_lqgApprox_decoder γ r).choose

theorem measurable_profileDecoder (γ r : ℝ) : Measurable (profileDecoder γ r) :=
  (exists_measurable_lqgApprox_decoder γ r).choose_spec.1

theorem profileDecoder_of_continuous (γ r : ℝ) {u : ℂ → ℝ} (hu : Continuous u) :
    profileDecoder γ r u = lqgApprox γ (fun _ => u) r :=
  (exists_measurable_lqgApprox_decoder γ r).choose_spec.2 u hu

/-- The LQG approximation of a canonical profile at the dyadic scale `2^{-k}`. -/
noncomputable def profileApprox (γ α₀ : ℝ) (k : ℕ) (f : CanonicalProfile) : Measure ℂ :=
  profileDecoder γ (dyadicScale k) (profileRadiusField α₀ (dyadicScale k) f)

theorem measurable_profileRadiusField (α₀ r : ℝ) : Measurable (profileRadiusField α₀ r) := by
  refine Measurable.of_eval fun z => ?_
  show Measurable fun f : CanonicalProfile =>
    f.1 (r, z) - α₀ * Real.circleAverage (fun x => Real.log ‖x‖) z r
  exact ((measurable_pi_apply (r, z)).comp measurable_subtype_coe).sub measurable_const

theorem continuous_profileRadiusField (α₀ : ℝ) {r : ℝ} (hr : 0 < r) (f : CanonicalProfile) :
    Continuous (profileRadiusField α₀ r f) := by
  have h1 : Continuous fun z : ℂ => f.1 (r, z) :=
    f.2.comp_continuous (continuous_const.prodMk continuous_id) fun z => Set.mk_mem_prod hr (Set.mem_univ z)
  have h2 : Continuous fun z : ℂ => Real.log (max r ‖z‖) :=
    (continuous_const.max continuous_norm).log fun z => (lt_max_of_lt_left hr).ne'
  have hfun : profileRadiusField α₀ r f = fun z => f.1 (r, z) - α₀ * Real.log (max r ‖z‖) := by
    funext z
    simp only [profileRadiusField, fieldCircleAverage, profileField, circleAverage_log_norm hr z]
  rw [hfun]
  exact h1.sub (continuous_const.mul h2)

/-- The LQG approximation of a canonical profile is the `lqgApprox` of its field at the dyadic scale. -/
theorem profileApprox_eq_lqgApprox (γ α₀ : ℝ) (k : ℕ) (f : CanonicalProfile) :
    profileApprox γ α₀ k f =
      lqgApprox γ (fun r z => fieldCircleAverage α₀ (profileField f) r z) (dyadicScale k) := by
  unfold profileApprox
  rw [profileDecoder_of_continuous γ _ (continuous_profileRadiusField α₀ (dyadicScale_pos k) f)]
  rfl

/-- The approximation is measurable in the canonical profile. -/
theorem measurable_profileApprox (γ α₀ : ℝ) (k : ℕ) : Measurable (profileApprox γ α₀ k) :=
  (measurable_profileDecoder γ _).comp (measurable_profileRadiusField α₀ _)

/-- The approximation of a canonical profile is locally finite. -/
theorem isLocallyFiniteMeasure_profileApprox (γ α₀ : ℝ) (k : ℕ) (f : CanonicalProfile) :
    IsLocallyFiniteMeasure (profileApprox γ α₀ k f) := by
  have hc : Continuous fun z : ℂ => fieldCircleAverage α₀ (profileField f) (dyadicScale k) z :=
    continuous_profileRadiusField α₀ (dyadicScale_pos k) f
  rw [profileApprox_eq_lqgApprox]
  unfold lqgApprox
  exact IsLocallyFiniteMeasure.withDensity_ofReal
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc)))

/-- Integrals of a compactly supported continuous test against the approximations are measurable in the profile. -/
theorem measurable_integral_profileApprox (γ α₀ : ℝ) (k : ℕ) {ψ : ℂ → ℝ} (hψ : Continuous ψ)
    (hcs : HasCompactSupport ψ) :
    Measurable fun f : CanonicalProfile => ∫ z, ψ z ∂(profileApprox γ α₀ k f) := by
  have hint : ∀ f : CanonicalProfile, Integrable ψ (profileApprox γ α₀ k f) := by
    intro f
    have := isLocallyFiniteMeasure_profileApprox γ α₀ k f
    exact hψ.integrable_of_hasCompactSupport hcs
  have hform : (fun f : CanonicalProfile => ∫ z, ψ z ∂(profileApprox γ α₀ k f)) =
      fun f => (∫⁻ z, ENNReal.ofReal (ψ z) ∂(profileApprox γ α₀ k f)).toReal -
        (∫⁻ z, ENNReal.ofReal (-ψ z) ∂(profileApprox γ α₀ k f)).toReal := by
    funext f
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint f)
  rw [hform]
  refine Measurable.sub ?_ ?_
  · exact ((Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hψ.measurable)).comp
      (measurable_profileApprox γ α₀ k)).ennreal_toReal
  · exact ((Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hψ.measurable.neg)).comp
      (measurable_profileApprox γ α₀ k)).ennreal_toReal

/-- `IsLQGLimit` depends only on the exponent at the dyadic radii `2^{-k}` (the approximations use no other radius). -/
theorem isLQGLimit_of_radius_eq {γ : ℝ} {h₁ h₂ : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (hh : ∀ k : ℕ, ∀ z : ℂ, h₁ (dyadicScale k) z = h₂ (dyadicScale k) z) (hL : IsLQGLimit γ h₁ m) :
    IsLQGLimit γ h₂ m := by
  have hA : ∀ k : ℕ, lqgApprox γ h₁ (dyadicScale k) = lqgApprox γ h₂ (dyadicScale k) := by
    intro k
    unfold lqgApprox
    congr 1
    funext z
    rw [hh k z]
  refine ⟨hL.isLocallyFiniteMeasure, fun f hf hc => ?_⟩
  have h := hL.tendsto_integral f hf hc
  simpa only [hA] using h

/-- **Vague convergence transfers to canonical profiles.** If `μ` is the LQG limit of the field `hcirc`, and `f` is a
canonical profile agreeing with `hcirc` on `J`, then the LQG approximations of `f` integrate every compactly supported
continuous test to `∫ ψ dμ`. -/
theorem tendsto_profileApprox_of_isLQGLimit {γ α₀ : ℝ} {hcirc : ℝ → ℂ → ℝ} {μ : Measure ℂ} {f : CanonicalProfile}
    (hL : IsLQGLimit γ (fun r z => fieldCircleAverage α₀ hcirc r z) μ)
    (hf : ∀ p ∈ circleIndexSet, f.1 p = hcirc p.1 p.2) {ψ : ℂ → ℝ} (hψ : Continuous ψ)
    (hcs : HasCompactSupport ψ) :
    Tendsto (fun k : ℕ => ∫ z, ψ z ∂(profileApprox γ α₀ k f)) atTop (𝓝 (∫ z, ψ z ∂μ)) := by
  have hrad : ∀ k : ℕ, ∀ z : ℂ,
      fieldCircleAverage α₀ hcirc (dyadicScale k) z = fieldCircleAverage α₀ (profileField f) (dyadicScale k) z := by
    intro k z
    have hp : (dyadicScale k, z) ∈ circleIndexSet := Set.mk_mem_prod (dyadicScale_pos k) (Set.mem_univ z)
    simp only [fieldCircleAverage, profileField, hf (dyadicScale k, z) hp]
  have hL' := isLQGLimit_of_radius_eq (fun k z => hrad k z) hL
  simp only [profileApprox_eq_lqgApprox]
  exact hL'.tendsto_integral ψ hψ hcs

end HarmonicBalls
