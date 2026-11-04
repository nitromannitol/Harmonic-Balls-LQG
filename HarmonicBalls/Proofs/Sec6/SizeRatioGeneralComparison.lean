import HarmonicBalls.Proofs.Sec6.SizeRatioLocalComparison

/-! # Size ratios under general local measure comparison -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

/-- Two measures are comparable on a set with lower scale `c` and distortion `K`. -/
structure IsComparableOnWith (μ ν : Measure ℂ) (B : Set ℂ) (c K : ℝ≥0∞) : Prop where
  scale_ne_zero : c ≠ 0
  scale_ne_top : c ≠ ∞
  distortion_ne_zero : K ≠ 0
  distortion_ne_top : K ≠ ∞
  lower : c • ν.restrict B ≤ μ.restrict B
  upper : μ.restrict B ≤ (K * c) • ν.restrict B

theorem IsComparableOnWith.le_apply {μ ν : Measure ℂ} {B s : Set ℂ} {c K : ℝ≥0∞}
    (h : IsComparableOnWith μ ν B c K) (hs : s ⊆ B) : c * ν s ≤ μ s := by
  have hl := h.lower s
  rwa [Measure.smul_apply, Measure.restrict_eq_self _ hs,
    Measure.restrict_eq_self _ hs, smul_eq_mul] at hl

theorem IsComparableOnWith.apply_le {μ ν : Measure ℂ} {B s : Set ℂ} {c K : ℝ≥0∞}
    (h : IsComparableOnWith μ ν B c K) (hs : s ⊆ B) : μ s ≤ K * c * ν s := by
  have hu := h.upper s
  rwa [Measure.smul_apply, Measure.restrict_eq_self _ hs,
    Measure.restrict_eq_self _ hs, smul_eq_mul] at hu

/-- Pointwise density bounds give local comparison, including when the omitted hole contains zero. -/
theorem isComparableOnWith_of_withDensity {μ ν : Measure ℂ} {B : Set ℂ}
    {c K : ℝ≥0∞} {w : ℂ → ℝ≥0∞} (hB : MeasurableSet B)
    (hμ : μ.restrict B = (ν.withDensity w).restrict B)
    (hc0 : c ≠ 0) (hct : c ≠ ∞) (hK0 : K ≠ 0) (hKt : K ≠ ∞)
    (hw : ∀ x ∈ B, c ≤ w x ∧ w x ≤ K * c) : IsComparableOnWith μ ν B c K where
  scale_ne_zero := hc0
  scale_ne_top := hct
  distortion_ne_zero := hK0
  distortion_ne_top := hKt
  lower := by
    rw [hμ, Measure.le_iff]
    intro s hs
    rw [Measure.smul_apply, Measure.restrict_apply hs, Measure.restrict_apply hs,
      withDensity_apply _ (hs.inter hB), smul_eq_mul, ← setLIntegral_const]
    exact setLIntegral_mono' (hs.inter hB) fun x hx => (hw x hx.2).1
  upper := by
    rw [hμ, Measure.le_iff]
    intro s hs
    rw [Measure.smul_apply, Measure.restrict_apply hs, Measure.restrict_apply hs,
      withDensity_apply _ (hs.inter hB), smul_eq_mul, ← setLIntegral_const]
    exact setLIntegral_mono' (hs.inter hB) fun x hx => (hw x hx.2).2

/-- The ball-mass size inherits general comparison on the enclosing annulus. -/
theorem annulusBallMassSize_comparableWith_on_annulus
    {μ ν : Measure ℂ} {x₀ : ℂ} {ρ : ℝ} {c K : ℝ≥0∞}
    (h : IsComparableOnWith μ ν (annulus x₀ (ρ / 4) (2 * ρ)) c K) (hρ : 0 < ρ)
    (β : ℝ) : c * annulusBallMassSize ν β ρ x₀ ≤ annulusBallMassSize μ β ρ x₀ ∧
      annulusBallMassSize μ β ρ x₀ ≤ K * c * annulusBallMassSize ν β ρ x₀ := by
  have hKc0 : K * c ≠ 0 := mul_ne_zero h.distortion_ne_zero h.scale_ne_zero
  have hKct : K * c ≠ ∞ := ENNReal.mul_ne_top h.distortion_ne_top h.scale_ne_top
  constructor
  · refine le_iInf₂ fun z hz => le_iInf₂ fun r hr => ?_
    calc c * annulusBallMassSize ν β ρ x₀ ≤ c * (ν (ball z r) / ENNReal.ofReal ((r / ρ) ^ β)) := by
          gcongr; exact iInf₂_le_of_le z hz (iInf₂_le r hr)
      _ = c * ν (ball z r) / ENNReal.ofReal ((r / ρ) ^ β) := (mul_div_assoc _ _ _).symm
      _ ≤ μ (ball z r) / ENNReal.ofReal ((r / ρ) ^ β) :=
          ENNReal.div_le_div_right (h.le_apply (annulusBallMassSize_ball_subset_annulus hρ hz hr)) _
  · unfold annulusBallMassSize
    simp_rw [ENNReal.mul_iInf_of_ne hKc0 hKct]
    refine iInf₂_mono fun z hz => iInf₂_mono fun r hr => ?_
    calc μ (ball z r) / ENNReal.ofReal ((r / ρ) ^ β) ≤
        K * c * ν (ball z r) / ENNReal.ofReal ((r / ρ) ^ β) :=
          ENNReal.div_le_div_right (h.apply_le (annulusBallMassSize_ball_subset_annulus hρ hz hr)) _
      _ = K * c * (ν (ball z r) / ENNReal.ofReal ((r / ρ) ^ β)) := mul_div_assoc _ _ _

/-- The Green-potential supremum inherits general comparison on its annulus. -/
theorem annulusGreenPotentialSup_comparableWith {μ ν : Measure ℂ} {x₀ : ℂ}
    {s₁ s₂ : ℝ} {c K : ℝ≥0∞}
    (h : IsComparableOnWith μ ν (annulus x₀ s₁ s₂) c K) :
    c * annulusGreenPotentialSup ν x₀ s₁ s₂ ≤ annulusGreenPotentialSup μ x₀ s₁ s₂ ∧
      annulusGreenPotentialSup μ x₀ s₁ s₂ ≤ K * c * annulusGreenPotentialSup ν x₀ s₁ s₂ := by
  unfold annulusGreenPotentialSup
  constructor
  · simp_rw [ENNReal.mul_iSup]
    refine iSup₂_mono fun x _ => ?_
    rw [← smul_eq_mul c, ← lintegral_smul_measure]
    exact lintegral_mono' h.lower le_rfl
  · simp_rw [ENNReal.mul_iSup]
    refine iSup₂_mono fun x _ => ?_
    rw [← smul_eq_mul (K * c), ← lintegral_smul_measure]
    exact lintegral_mono' h.upper le_rfl

/-- General ratio comparison, allowing zero or infinite numerators and denominators. -/
theorem ratio_mem_of_comparableWith {X X' Y Y' c K lo hi : ℝ≥0∞}
    (hc0 : c ≠ 0) (hct : c ≠ ∞) (hK0 : K ≠ 0) (hKt : K ≠ ∞)
    (hX : c * X ≤ X') (hX' : X' ≤ K * c * X)
    (hY : c * Y ≤ Y') (hY' : Y' ≤ K * c * Y)
    (h : X / Y ∈ Icc lo hi) : X' / Y' ∈ Icc (lo / K) (K * hi) := by
  constructor
  · calc lo / K ≤ X / Y / K := ENNReal.div_le_div_right h.1 K
      _ = c * X / (c * (K * Y)) := by
          rw [ENNReal.mul_div_mul_left _ _ hc0 hct, div_eq_mul_inv, div_eq_mul_inv,
            div_eq_mul_inv, ENNReal.mul_inv (Or.inl hK0) (Or.inl hKt),
            mul_comm K⁻¹ Y⁻¹, mul_assoc]
      _ ≤ X' / Y' := ENNReal.div_le_div hX (hY'.trans_eq (by ring))
  · calc X' / Y' ≤ K * c * X / (c * Y) := ENNReal.div_le_div hX' hY
      _ = K * (X / Y) := by
          rw [mul_comm K c, mul_assoc, ENNReal.mul_div_mul_left _ _ hc0 hct, mul_div_assoc]
      _ ≤ K * hi := by gcongr; exact h.2

/-- Both normalized size windows transfer with the same distortion. -/
theorem veryGood_size_windows_of_comparableWith_on_annulus
    {μ ν : Measure ℂ} {x₀ : ℂ} {ρ β : ℝ} {c K lo₁ hi₁ lo₂ hi₂ : ℝ≥0∞}
    (h : IsComparableOnWith μ ν (annulus x₀ (ρ / 4) (2 * ρ)) c K) (hρ : 0 < ρ)
    (hM : annulusBallMassSize ν β ρ x₀ / ν (annulus x₀ (ρ / 4) (2 * ρ)) ∈ Icc lo₁ hi₁)
    (hG : annulusGreenPotentialSup ν x₀ (ρ / 4) (2 * ρ) /
      ν (annulus x₀ (ρ / 4) (2 * ρ)) ∈ Icc lo₂ hi₂) :
    annulusBallMassSize μ β ρ x₀ / μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈ Icc (lo₁ / K) (K * hi₁) ∧
    annulusGreenPotentialSup μ x₀ (ρ / 4) (2 * ρ) /
      μ (annulus x₀ (ρ / 4) (2 * ρ)) ∈ Icc (lo₂ / K) (K * hi₂) := by
  have hM' := annulusBallMassSize_comparableWith_on_annulus h hρ β
  have hG' := annulusGreenPotentialSup_comparableWith h
  exact ⟨ratio_mem_of_comparableWith h.scale_ne_zero h.scale_ne_top h.distortion_ne_zero
      h.distortion_ne_top hM'.1 hM'.2 (h.le_apply Subset.rfl) (h.apply_le Subset.rfl) hM,
    ratio_mem_of_comparableWith h.scale_ne_zero h.scale_ne_top h.distortion_ne_zero
      h.distortion_ne_top hG'.1 hG'.2 (h.le_apply Subset.rfl) (h.apply_le Subset.rfl) hG⟩

end HarmonicBalls.Section6
