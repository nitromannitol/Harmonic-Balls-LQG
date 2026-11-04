import HarmonicBalls.Steps.Sec11.PinchAnnulusConnected
import HarmonicBalls.Steps.Sec11.PinchAuxiliaryThresholds

/-! # Strict thresholds for the third auxiliary event

The annular diameter is finite and the sphere separation positive. On any
positive-mass event they admit deterministic strict bounds on a positive-mass
subevent. The contraction factor below contains explicit slack.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- A positive-mass event has a positive-mass subevent on which the distance
between the two spheres has a deterministic positive lower bound and the
third auxiliary diameter has a deterministic finite upper bound. -/
theorem IsPinchPointProofConfiguration.exists_positive_measure_third_thresholds
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hconfig : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (D : Ω → ℂ → ℂ → ℝ) (hA : 0 < P A)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) :
    ∃ n m : ℕ, 0 < n ∧ 0 < P {ω | ω ∈ A ∧
      (n : ℝ≥0∞)⁻¹ < ENNReal.ofReal (setDist (D ω)
        (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) ∧
      internalDiam (D ω) δ (thickening (3 * δ) W \ V) < (m : ℝ≥0∞)} := by
  let G : Set Ω := {ω | IsEuclideanLengthMetric (D ω)}
  have heq : A =ᵐ[P] A ∩ G := by
    filter_upwards [hmetric] with ω hω
    simp only [mem_inter_iff, hω, and_true, G, mem_ofPred_eq]
  have hAG : 0 < P (A ∩ G) := by rwa [← measure_congr heq]
  let f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (setDist (D ω)
    (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))
  let g : Ω → ℝ≥0∞ := fun ω => internalDiam (D ω) δ (thickening (3 * δ) W \ V)
  have hfg : ∀ ω ∈ A ∩ G, f ω ≠ 0 ∧ g ω ≠ ∞ := by
    intro ω hω
    have hD : IsEuclideanLengthMetric (D ω) := hω.2
    have hnonneg : ∀ x y, 0 ≤ D ω x y := by
      intro x y
      have htri := hD.triangle x y x
      rw [hD.self_eq_zero, hD.symm y x] at htri
      linarith
    have hpos := (hD.pinch_sphere_distances_pos hconfig.δ₀_mem.1).2
    exact ⟨(ENNReal.ofReal_pos.mpr hpos).ne',
      (hconfig.internalDiam_outerAnnulus_lt_top hD hnonneg).ne⟩
  obtain ⟨n, m, hn, hp⟩ := exists_positive_measure_uniform_thresholds P (A ∩ G) f g hAG hfg
  refine ⟨n, m, hn, hp.trans_le (measure_mono ?_)⟩
  intro ω hω
  exact ⟨hω.1.1, hω.2.1, hω.2.2⟩

/-- A finite upper threshold and a positive lower threshold admit a positive
contraction factor with strict slack. -/
theorem exists_strict_contraction_factor {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ ∀ x y : ℝ≥0∞,
      x ≤ ENNReal.ofReal b → ENNReal.ofReal a ≤ y → ENNReal.ofReal q * x < y := by
  let q : ℝ := a / (2 * (b + 1) + a)
  have hden : 0 < 2 * (b + 1) + a := by positivity
  have hq : 0 < q := div_pos ha hden
  have hqone : q ≤ 1 := (div_le_one₀ hden).2 (by linarith)
  have hqb : q * b < a := by
    dsimp [q]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  refine ⟨q, hq, hqone, fun x y hx hy => ?_⟩
  calc
    ENNReal.ofReal q * x ≤ ENNReal.ofReal q * ENNReal.ofReal b := by gcongr
    _ = ENNReal.ofReal (q * b) := (ENNReal.ofReal_mul hq.le).symm
    _ < ENNReal.ofReal a := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg hq.le hb)).2 hqb
    _ ≤ y := hy

/-- On a positive-mass event there is a deterministic positive contraction
factor making the third diameter strictly smaller than the sphere separation
on a positive-mass subevent. This is a numerical bound; obtaining the
corresponding Weyl-scaling inequality is a separate step. -/
theorem IsPinchPointProofConfiguration.exists_positive_measure_third_contraction
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hconfig : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (D : Ω → ℂ → ℂ → ℝ) (hA : 0 < P A)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 ∧ 0 < P {ω | ω ∈ A ∧
      ENNReal.ofReal q * internalDiam (D ω) δ (thickening (3 * δ) W \ V) <
        ENNReal.ofReal (setDist (D ω) (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))} := by
  obtain ⟨n, m, hn, hp⟩ := hconfig.exists_positive_measure_third_thresholds P A D hA hmetric
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨q, hq, hqone, hqbound⟩ := exists_strict_contraction_factor
    (inv_pos.mpr hnreal) (Nat.cast_nonneg m)
  refine ⟨q, hq, hqone, hp.trans_le (measure_mono ?_)⟩
  intro ω hω
  refine ⟨hω.1, hqbound _ _ ?_ ?_⟩
  · simpa only [ENNReal.ofReal_natCast] using hω.2.2.le
  · simpa only [ENNReal.ofReal_inv_of_pos hnreal, ENNReal.ofReal_natCast] using hω.2.1.le

end HarmonicBalls
