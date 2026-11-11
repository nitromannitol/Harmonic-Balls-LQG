import HarmonicBalls.Proofs.Sec11.InternalDiameterLaw
import HarmonicBalls.Steps.Sec11.NormalizedDiameterPositiveMoment

/-! # Positive moments of normalized internal diameters

Affine invariance identifies all exact-power normalized positive moments with
fixed-domain moments. The GFF formalization used here includes work by
Leonardo Bonanno on LatticeProb.
-/

namespace HarmonicBalls

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Every real power of an exact-power normalized compact internal diameter
has the same integral as the corresponding fixed-domain power. -/
theorem IsWholePlaneGFF.lintegral_rpow_scaledCompactInternalDiameter_eq
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {U K : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U) {r : ℝ} (hr : 0 < r)
    (p : ℝ) :
    (∫⁻ ω, (scaledCompactInternalDiameter (fun ω => 𝔇 (hC ω)) hcirc ξ K U r
      (ENNReal.ofReal (r ^ (ξ * lqgQ γ))) ω) ^ p ∂P) =
      ∫⁻ ω, (⨆ x ∈ K, ⨆ y ∈ K, internalMetric (𝔇 (hC ω)) U x y) ^ p ∂P := by
  have haff : IsWholePlaneGFF P (affinePairing hC hcirc (r : ℂ) 0)
      (affineCircle hcirc (r : ℂ) 0) :=
    hAff h (r : ℂ) (by exact_mod_cast hr.ne') 0
  calc
    _ = ∫⁻ ω, (⨆ x ∈ K, ⨆ y ∈ K,
        internalMetric (𝔇 (affinePairing hC hcirc (r : ℂ) 0 ω)) U x y) ^ p ∂P :=
      lintegral_congr_ae ((h.ae_scaledCompactInternalDiameter_eq_affine hAff 𝔇 h𝔇 K U hr).mono
        (fun _ hω => by rw [hω]))
    _ = _ := ((haff.identDistrib_baseMetric_internalDiameter h 𝔇 h𝔇 hU hKU).comp
      ENNReal.continuous_rpow_const.measurable).lintegral_eq

/-- Finitely many fixed-domain positive moments give a uniform bound at all
scales for the associated exact-power normalized diameters. -/
theorem IsWholePlaneGFF.exists_uniform_rpow_scaledCompactInternalDiameter_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (s ε p : ℝ) (N : ℕ) (c : ℕ → ℂ) (hε : 0 < ε)
    (hmom : ∀ i, i ≤ N → (∫⁻ ω,
      (⨆ x ∈ Metric.closedBall (c i) ε, ⨆ y ∈ Metric.closedBall (c i) ε,
        internalMetric (𝔇 (hC ω)) (Metric.ball (c i) (2 * ε)) x y) ^ p ∂P) ≠ ∞) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (n i : ℕ), i ≤ N →
      (∫⁻ ω, (scaledCompactInternalDiameter (fun ω => 𝔇 (hC ω)) hcirc ξ
        (Metric.closedBall (c i) ε) (Metric.ball (c i) (2 * ε))
        (Real.exp (-(s + n)))
        (ENNReal.ofReal ((Real.exp (-(s + n))) ^ (ξ * lqgQ γ))) ω) ^ p ∂P) ≤ C := by
  apply exists_uniform_lintegral_bound_of_finite_centers
  intro i hi
  refine ⟨_, hmom i hi, ?_⟩
  intro n
  exact (h.lintegral_rpow_scaledCompactInternalDiameter_eq hAff 𝔇 h𝔇 Metric.isOpen_ball
    (closedBall_compact_connected_subset_double (c i) hε).2.2.1
    (Real.exp_pos _) p).le

/-- A larger deterministic normalization bounds the explicit local diameter
by the exact-scale compact diameter. -/
theorem scaledBallNormalizedInternalDiameter_le_compact_of_scale_le
    {Ω : Type*} (D : Ω → ℂ → ℂ → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (s ξ η ε : ℝ) (c : ℕ → ℂ) (a : ℕ → ℝ≥0∞) (n i : ℕ) (ω : Ω)
    (hle : a n ≤ ENNReal.ofReal (Real.exp (-η * (n : ℝ)))) :
    scaledBallNormalizedInternalDiameter D hcirc s ξ η ε c n i ω ≤
      scaledCompactInternalDiameter D hcirc ξ (Metric.closedBall (c i) ε)
        (Metric.ball (c i) (2 * ε)) (Real.exp (-(s + n))) (a n) ω := by
  calc
    _ ≤ scaledBallDiameterWithScale D hcirc s ξ ε c a n i ω := by
      simp only [scaledBallNormalizedInternalDiameter, scaledBallDiameterWithScale,
        Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _), div_eq_mul_inv]
      gcongr
    _ ≤ _ := scaledBallDiameterWithScale_le_compact D hcirc s ξ ε c a n i ω

/-- Puncture removal follows from finite positive moments of finitely many
fixed-domain compact internal diameters. -/
theorem IsWholePlaneGFF.exists_puncture_criterion_of_fixed_diameter_positive_moments
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (E : Ω → ℂ → ℂ → ℝ) (s α p : ℝ)
    (hs : 0 ≤ s) (hξ : 0 < ξ) (hα : 0 ≤ α) (hαQ : α < lqgQ γ) (hp : 0 < p)
    (V : Set ℂ) (hball : Metric.ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V)
    (hmeasD : ∀ x y, Measurable fun ω => 𝔇 (hC ω) x y)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hDnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ 𝔇 (hC ω) x y)
    (hEnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ E ω x y)
    (hzero : ∀ᵐ ω ∂P, ∀ x y,
      weylScaling (𝔇 (hC ω)) ξ 0 x y = ENNReal.ofReal (𝔇 (hC ω) x y))
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y) :
    ∃ (ε : ℝ) (N : ℕ) (c : ℕ → ℂ), 0 < ε ∧
      ((∀ i, i ≤ N → (∫⁻ ω,
        (⨆ x ∈ Metric.closedBall (c i) ε, ⨆ y ∈ Metric.closedBall (c i) ε,
          internalMetric (𝔇 (hC ω)) (Metric.ball (c i) (2 * ε)) x y) ^ p ∂P) ≠ ∞) →
        ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
          internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y) := by
  have hgap : ξ * α < ξ * lqgQ γ := mul_lt_mul_of_pos_left hαQ hξ
  obtain ⟨κ, hκ, hκQ⟩ := exists_between hgap
  obtain ⟨β, hβ, hβκ⟩ := exists_between hκ
  obtain ⟨η, hκη, hηQ⟩ := exists_between hκQ
  obtain ⟨ε, N, c, hε, hcriterion⟩ :=
    exists_scaled_ball_criterion_of_explicit_positive_moments P hC hcirc h
      (fun ω => 𝔇 (hC ω)) E s ξ α β κ η p hs hξ hα hβ hβκ hκη hp
      V hball hmeasD hD hE hDnonneg hEnonneg hzero hscale
  refine ⟨ε, N, c, hε, ?_⟩
  intro hmom
  obtain ⟨C, hCfin, hbound⟩ :=
    h.exists_uniform_rpow_scaledCompactInternalDiameter_bound hAff 𝔇 h𝔇 s ε p N c hε hmom
  apply hcriterion C hCfin
  intro n i hi
  have hq : 0 < ξ * lqgQ γ := lt_of_le_of_lt (mul_nonneg hξ.le hα) hgap
  have hle : ENNReal.ofReal ((Real.exp (-(s + n))) ^ (ξ * lqgQ γ)) ≤
      ENNReal.ofReal (Real.exp (-η * (n : ℝ))) := by
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    apply Real.exp_le_exp.mpr
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith only [mul_nonneg hs hq.le, mul_nonneg hn (sub_nonneg.mpr hηQ.le)]
  calc
    _ ≤ ∫⁻ ω, (scaledCompactInternalDiameter (fun ω => 𝔇 (hC ω)) hcirc ξ
        (Metric.closedBall (c i) ε) (Metric.ball (c i) (2 * ε))
        (Real.exp (-(s + n)))
        (ENNReal.ofReal ((Real.exp (-(s + n))) ^ (ξ * lqgQ γ))) ω) ^ p ∂P := by
      apply lintegral_mono
      intro ω
      exact ENNReal.rpow_le_rpow
        (scaledBallNormalizedInternalDiameter_le_compact_of_scale_le (fun ω => 𝔇 (hC ω))
          hcirc s ξ η ε c (fun n => ENNReal.ofReal ((Real.exp (-(s + n))) ^
            (ξ * lqgQ γ))) n i ω hle) hp.le
    _ ≤ C := hbound n i hi


end HarmonicBalls
