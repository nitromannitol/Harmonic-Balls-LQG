import HarmonicBalls.Proofs.Sec8.BallMassSizeScaling
import HarmonicBalls.Proofs.Sec8.GreenPotentialScaling
import HarmonicBalls.Proofs.Sec8.VeryGoodMeasureScaling

/-! # Dilation of the good-radius count -/

open MeasureTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- If good annuli themselves are transported by dilation, their counts in
corresponding geometric radius intervals agree. -/
theorem goodAnnulus_radius_count_map_inv_smul (μ : Measure ℂ) {k : ℝ} (hk : 0 < k)
    (ρ : ℝ) (n : ℕ) (z : ℂ) (a b : ℝ)
    (hgood : ∀ r : ℝ,
      IsGoodAnnulus (μ.map (fun x : ℂ => k⁻¹ • x)) r z a b ↔
        IsGoodAnnulus μ (k * r) (k • z) a b) :
    {r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
      (∃ j : ℕ, 1 ≤ j ∧ r = ρ * (7 : ℝ)⁻¹ ^ j) ∧
        IsGoodAnnulus (μ.map (fun x : ℂ => k⁻¹ • x)) r z a b}.ncard =
    {r : ℝ | r ∈ Icc (dyadicScale n * (k * ρ)) (Real.sqrt (dyadicScale n) * (k * ρ)) ∧
      (∃ j : ℕ, 1 ≤ j ∧ r = (k * ρ) * (7 : ℝ)⁻¹ ^ j) ∧
        IsGoodAnnulus μ r (k • z) a b}.ncard := by
  let S : Set ℝ := {r | r ∈ Icc (dyadicScale n * (k * ρ))
      (Real.sqrt (dyadicScale n) * (k * ρ)) ∧
      (∃ j : ℕ, 1 ≤ j ∧ r = (k * ρ) * (7 : ℝ)⁻¹ ^ j) ∧
        IsGoodAnnulus μ r (k • z) a b}
  have hpre : {r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
      (∃ j : ℕ, 1 ≤ j ∧ r = ρ * (7 : ℝ)⁻¹ ^ j) ∧
        IsGoodAnnulus (μ.map (fun x : ℂ => k⁻¹ • x)) r z a b} =
      (fun r : ℝ => k * r) ⁻¹' S := by
    ext r
    simp only [mem_ofPred_eq, mem_preimage, S, mem_Icc, hgood]
    have hmul (t : ℝ) : k * (t * ρ) = t * (k * ρ) := by ring
    simp only [← hmul, mul_le_mul_iff_right₀ hk, mul_assoc, mul_right_inj' hk.ne']
  rw [hpre]
  apply ncard_preimage_of_injective_subset_range
  · intro x y h; exact mul_left_cancel₀ hk.ne' h
  · intro x hx
    exact ⟨k⁻¹ * x, by field_simp⟩

/-- Geometric transport of each good-annulus event implies transport of the
complete very-good-annulus event at the origin. -/
theorem isVeryGoodAnnulus_map_inv_smul_of_good_transport (μ : Measure ℂ)
    {k : ℝ} (hk : 0 < k) (β ρ : ℝ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ)
    (hgood : ∀ r : ℝ, ∀ z : ℂ,
      IsGoodAnnulus (μ.map (fun x : ℂ => k⁻¹ • x)) r z a b ↔
        IsGoodAnnulus μ (k * r) (k • z) a b) :
    IsVeryGoodAnnulus (μ.map (fun x : ℂ => k⁻¹ • x)) β ρ 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ↔
      IsVeryGoodAnnulus μ β (k * ρ) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ := by
  have hp : (fun z : ℂ => k⁻¹ • z) ⁻¹' annulus (0 : ℂ) (ρ / 2) ρ =
      annulus 0 ((k * ρ) / 2) (k * ρ) := by
    simp only [annulus, preimage_sdiff, preimage_inv_smul_ball_zero hk,
      preimage_inv_smul_closedBall_zero hk]
    congr 2; ring
  have hmem (z : ℂ) : z ∈ annulus (0 : ℂ) (ρ / 2) ρ ↔
      k • z ∈ annulus (0 : ℂ) ((k * ρ) / 2) (k * ρ) := by
    rw [← hp]
    simp only [mem_preimage, smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  have hinj : Function.Injective (fun z : ℂ => k • z) := by
    intro x y h
    have h' := congrArg (fun z : ℂ => k⁻¹ • z) h
    simpa only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul] using h'
  have hscale (n : ℕ) (j l : ℤ) :
      k • (((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (l : ℂ) * Complex.I)) =
        (((dyadicScale n * (k * ρ) / 100 : ℝ) : ℂ) * ((j : ℂ) + (l : ℂ) * Complex.I)) := by
    rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]
    congr 1
    congr 1
    ring
  have hlat (n : ℕ) (z : ℂ) :
      (∃ j l : ℤ, z = ((dyadicScale n * ρ / 100 : ℝ) : ℂ) *
        ((j : ℂ) + (l : ℂ) * Complex.I)) ↔
      (∃ j l : ℤ, k • z = ((dyadicScale n * (k * ρ) / 100 : ℝ) : ℂ) *
        ((j : ℂ) + (l : ℂ) * Complex.I)) := by
    constructor
    · rintro ⟨j, l, rfl⟩
      exact ⟨j, l, hscale n j l⟩
    · rintro ⟨j, l, h⟩
      exact ⟨j, l, hinj (h.trans (hscale n j l).symm)⟩
  unfold IsVeryGoodAnnulus
  rw [annulusBallMassRatioSize_map_inv_smul μ hk,
    annulusGreenPotentialRatio_map_inv_smul μ hk]
  constructor
  · rintro ⟨h₁, h₂, h⟩
    refine ⟨h₁, h₂, ?_⟩
    intro n hn z hz hlatz
    have hz' : k⁻¹ • z ∈ annulus (0 : ℂ) (ρ / 2) ρ := by
      rw [← hp] at hz
      exact hz
    have hlat' := (hlat n (k⁻¹ • z)).mpr (by
      simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using hlatz)
    have hh := h n hn (k⁻¹ • z) hz' hlat'
    rw [goodAnnulus_radius_count_map_inv_smul μ hk ρ n (k⁻¹ • z) a b
      (fun r => hgood r (k⁻¹ • z))] at hh
    simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using hh
  · rintro ⟨h₁, h₂, h⟩
    refine ⟨h₁, h₂, ?_⟩
    intro n hn z hz hlatz
    have hh := h n hn (k • z) ((hmem z).mp hz) ((hlat n z).mp hlatz)
    rw [goodAnnulus_radius_count_map_inv_smul μ hk ρ n z a b (fun r => hgood r z)]
    exact hh

universe u

open Filter ProbabilityTheory

open Classical in
/-- Stationarity of joint very-good and comparison indicators follows from
measurability and dyadic transport of the individual good-annulus events. -/
theorem identDistrib_lqg_veryGoodComparable_sequence_of_good_transport
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (hmeas : ∀ n, MeasurableSet {ν : Measure ℂ |
      IsVeryGoodAnnulus ν β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃})
    (hgood : ∀ᵐ ω ∂P, ∀ r : ℝ, ∀ z : ℂ,
      IsGoodAnnulus ((μ ω).map (fun x : ℂ => (dyadicScale 1)⁻¹ • x)) r z a b ↔
        IsGoodAnnulus (μ ω) (dyadicScale 1 * r) (dyadicScale 1 • z) a b) :
    IdentDistrib
      (fun ω n => if IsVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0)
      (fun ω n => if IsVeryGoodAnnulus (μ ω) β (dyadicScale (1 + n)) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) (1 + n) 0 m then (1 : ℝ) else 0)
      P P := by
  apply identDistrib_lqg_veryGoodComparable_sequence_of_dyadic_transport hγ hγ2 hα
    hGFF hμ hAff hCC β N₀ a b C₁m C₁p C₂m C₂p C₃ m hmeas
  filter_upwards [hgood] with ω hω n
  have ht := isVeryGoodAnnulus_map_inv_smul_of_good_transport (μ ω) (dyadicScale_pos 1)
    β (dyadicScale n) N₀ a b C₁m C₁p C₂m C₂p C₃ hω
  simpa only [dyadicScale, pow_add] using ht

end HarmonicBalls
