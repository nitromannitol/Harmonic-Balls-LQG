import HarmonicBalls.Proofs.Sec11.ShiftedPuncturedMetricLocality
import HarmonicBalls.Steps.Sec11.InternalMetricExhaustion

/-! # Locality on increasing open domains

The Section 8 inputs use Leonardo Bonanno's LatticeProb code.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- A path constrained to a set must start and end in that set. -/
theorem internalMetric_eq_top_of_not_mem_endpoints
    (D : ℂ → ℂ → ℝ) (U : Set ℂ) (x y : ℂ)
    (h : x ∉ U ∨ y ∉ U) : internalMetric D U x y = ⊤ := by
  unfold internalMetric
  apply iInf_eq_top.mpr
  intro p
  apply iInf_eq_top.mpr
  intro hp
  exfalso
  rcases h with hx | hy
  · exact hx (p.source ▸ hp 0)
  · exact hy (p.target ▸ hp 1)

/-- Local internal-metric representatives glue over an increasing countable
open cover, with a common almost-everywhere event for all pairs of points. -/
theorem exists_internalMetric_version_iUnion
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (m : MeasurableSpace Ω)
    (D : Ω → ℂ → ℂ → ℝ) (U : ℕ → Set ℂ)
    (hopen : ∀ n, IsOpen (U n)) (hmono : Monotone U)
    (hlocal : ∀ n, ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ x y, Measurable[m] (fun ω => G ω x y)) ∧
      ∀ᵐ ω ∂P, ∀ x ∈ U n, ∀ y ∈ U n,
        internalMetric (D ω) (U n) x y = G ω x y) :
    ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ x y, Measurable[m] (fun ω => G ω x y)) ∧
      ∀ᵐ ω ∂P, ∀ x y, internalMetric (D ω) (⋃ n, U n) x y = G ω x y := by
  classical
  choose G hG hGeq using hlocal
  let H : Ω → ℂ → ℂ → ℝ≥0∞ := fun ω x y =>
    ⨅ n, if x ∈ U n ∧ y ∈ U n then G n ω x y else ⊤
  refine ⟨H, ?_, ?_⟩
  · intro x y
    exact Measurable.iInf fun n => by
      by_cases hxy : x ∈ U n ∧ y ∈ U n
      · simpa [H, hxy] using hG n x y
      · simp only [hxy, ↓reduceIte]
        exact measurable_const
  · filter_upwards [ae_all_iff.mpr hGeq] with ω hω x y
    rw [internalMetric_iUnion_of_monotone_isOpen (D ω) U hopen hmono]
    change (⨅ n, internalMetric (D ω) (U n) x y) =
      ⨅ n, if x ∈ U n ∧ y ∈ U n then G n ω x y else ⊤
    apply iInf_congr
    intro n
    by_cases hxy : x ∈ U n ∧ y ∈ U n
    · simp only [hxy]
      exact hω n x hxy.1 y hxy.2
    · simp only [hxy, ↓reduceIte]
      exact internalMetric_eq_top_of_not_mem_endpoints (D ω) (U n) x y (by tauto)

/-- Singular-metric locality extends to an entire punctured open set. The
observation set may contain the origin; the paths still avoid it. -/
theorem IsWholePlaneGFF.exists_shifted_internal_singularMetric_punctured
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (c : Ω → ℝ) (hc : Measurable c)
    {U V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U) :
    ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ x y, Measurable[fieldSigmaAlgebra α
        (fun ω => addFunPairing (hC ω) (fun _ => c ω)) U] (fun ω => G ω x y)) ∧
      ∀ᵐ ω ∂P, ∀ x y,
        internalMetric (fun u v =>
          (weylScaling (𝔇 (addFunPairing (hC ω) (fun _ => c ω))) ξ
            (fun z => -α * Real.log ‖z‖) u v).toReal) (V \ {0}) x y = G ω x y := by
  let W : ℕ → Set ℂ := fun n => V ∩ {z | 1 / (n + 1 : ℝ) < ‖z‖}
  have hopen : ∀ n, IsOpen (W n) := fun n =>
    hV.inter (isOpen_lt continuous_const continuous_norm)
  have hmono : Monotone W := by
    intro n m hnm z hz
    change z ∈ V ∧ 1 / (n + 1 : ℝ) < ‖z‖ at hz
    change z ∈ V ∧ 1 / (m + 1 : ℝ) < ‖z‖
    refine ⟨hz.1, lt_of_le_of_lt ?_ hz.2⟩
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hcover : (⋃ n, W n) = V \ {0} := by
    ext z
    constructor
    · intro hz
      obtain ⟨n, hz⟩ := mem_iUnion.mp hz
      refine ⟨hz.1, ?_⟩
      simp only [mem_singleton_iff]
      intro hz0
      subst z
      have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
      have hlt : 1 / (n + 1 : ℝ) < ‖(0 : ℂ)‖ := hz.2
      simp only [norm_zero] at hlt
      linarith
    · intro hz
      have hz0 : z ≠ 0 := by simpa using hz.2
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hz0)
      exact mem_iUnion.mpr ⟨n, hz.1, hn⟩
  have hlocal (n : ℕ) := h.exists_shifted_internal_singularMetric_away_zero
    𝔇 h𝔇 hD hmetric c hc (hopen n) (fun _ hz => hVU hz.1)
    (r := 1 / (n + 1 : ℝ)) (by positivity) (fun _ hz => le_of_lt hz.2)
  obtain ⟨G, hG, hGeq⟩ := exists_internalMetric_version_iUnion P
    (fieldSigmaAlgebra α (fun ω => addFunPairing (hC ω) (fun _ => c ω)) U)
    (fun ω u v => (weylScaling (𝔇 (addFunPairing (hC ω) (fun _ => c ω))) ξ
      (fun z => -α * Real.log ‖z‖) u v).toReal) W hopen hmono hlocal
  exact ⟨G, hG, hcover ▸ hGeq⟩

/-- The normalized singular internal metric on a punctured open set has a
version measurable with respect to the field modulo constants on the larger
observation set. -/
theorem IsWholePlaneGFF.exists_modConst_internal_singularMetric_punctured
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {U V : Set ℂ} (hV : IsOpen V) (hne : (V \ {0}).Nonempty) (hVU : V ⊆ U)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1) :
    ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
      (∀ᵐ ω ∂P, 0 < c ω) ∧
      (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC U] (fun ω => G ω x y)) ∧
      (∀ᵐ ω ∂P, ∀ x ∈ V \ {0}, ∀ y ∈ V \ {0},
        internalMetric (fun x y => c ω * D ω x y) (V \ {0}) x y = G ω x y) := by
  have hc : Measurable (fun ω => -hC ω ψ) :=
    (h.measurable_pairing ψ (hψ.mono_set (subset_univ _))).neg
  obtain ⟨G, hG, hGeq⟩ := h.exists_shifted_internal_singularMetric_punctured
    𝔇 h𝔇 hD hmetric (fun ω => -hC ω ψ) hc hV hVU
  apply h.exists_modConst_internalMetric_of_shifted_locality 𝔇 h𝔇 hD hmetric
    (hV.sdiff isClosed_singleton) hne ψ hψ hψint
  refine ⟨G, hG, ?_⟩
  filter_upwards [hGeq] with ω hω x hx y hy
  exact hω x y


end HarmonicBalls
