import HarmonicBalls.Proofs.Sec11.CountableCenteredBaseLocality
import HarmonicBalls.Steps.Sec11.ContinuousMetricVersions

/-! # Locality of the normalized base metric

The base metric, normalized by a local reference pairing, has internal
metric versions measurable in the field modulo additive constants. The
Section 8 inputs use Leonardo Bonanno's LatticeProb code.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- The normalized base metric has a simultaneous local version modulo
constants without a samplewise linearity assumption on the field pairings. -/
theorem IsWholePlaneGFF.exists_modConst_internal_baseMetric
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {U : Set ℂ} (hU : IsOpen U) (ψ : ℂ → ℝ)
    (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1) :
    ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
      (∀ᵐ ω ∂P, 0 < c ω) ∧
      (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC U] (fun ω => G ω x y)) ∧
      (∀ᵐ ω ∂P, ∀ x ∈ U, ∀ y ∈ U,
        internalMetric (fun x y => c ω * 𝔇 (hC ω) x y) U x y = G ω x y) := by
  classical
  let c : Ω → ℝ := fun ω => -hC ω ψ
  have hc : Measurable c := (h.measurable_pairing ψ (hψ.mono_set (subset_univ _))).neg
  have hne : U.Nonempty := by
    by_contra hn
    have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hzero : ψ = 0 := by
      funext x
      by_contra hx
      have hmem : x ∈ U := hψ.2.2 (subset_closure hx)
      rw [hUempty] at hmem
      exact hmem
    simp [hzero] at hψint
  have hshift := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 h
    (fun ω _ => c ω) (fun _ => continuous_const) (fun _ => hc)
  have heq := h.ae_baseMetric_add_random_constant 𝔇 h𝔇 c hc
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric
      (fun x y => Real.exp (ξ * c ω) * 𝔇 (hC ω) x y) := by
    filter_upwards [hshift, heq] with ω hs he
    have hf : 𝔇 (addFunPairing (hC ω) (fun _ => c ω)) =
        fun x y => Real.exp (ξ * c ω) * 𝔇 (hC ω) x y := by
      funext x y
      exact he x y
    rw [← hf]
    exact hs.2.1
  have hcount := fun (p : ℕ → ℂ × ℂ) hp =>
    h.exists_modConst_countable_internal_baseMetric (α := α) 𝔇 h𝔇 hU ψ hψ hψint p hp
  obtain ⟨G, hG, hGeq⟩ := exists_internalMetric_version_of_countable
    (Section6.fieldSigmaAlgebraModConst α hC U) hU hne hmetric hcount
  exact ⟨fun ω => Real.exp (ξ * c ω), G,
    Filter.Eventually.of_forall (fun _ => Real.exp_pos _), hG, hGeq⟩

/-- The reference-centered internal metric is measurable in any larger
field restriction modulo constants. -/
theorem IsWholePlaneGFF.exists_modConst_internal_baseMetric_subset
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {U V : Set ℂ} (hU : IsOpen U) (hUV : U ⊆ V)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1) :
    ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
      (∀ᵐ ω ∂P, 0 < c ω) ∧
      (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC V] (fun ω => G ω x y)) ∧
      (∀ᵐ ω ∂P, ∀ x ∈ U, ∀ y ∈ U,
        internalMetric (fun x y => c ω * 𝔇 (hC ω) x y) U x y = G ω x y) := by
  obtain ⟨c, G, hc, hG, heq⟩ :=
    h.exists_modConst_internal_baseMetric (α := α) 𝔇 h𝔇 hU ψ hψ hψint
  exact ⟨c, G, hc, fun x y => (hG x y).mono
    (fieldSigmaAlgebraModConst_mono α hC hUV) le_rfl, heq⟩



end HarmonicBalls
