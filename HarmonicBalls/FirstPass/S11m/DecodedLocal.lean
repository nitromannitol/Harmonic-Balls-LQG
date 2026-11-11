import HarmonicBalls.FirstPass.S11m.DecodedDomain
import HarmonicBalls.FirstPass.S11m.DecodedRaw

/-!
# Decoded internal distances on the local domains

Route: the bounded-domain interface (`DecodesOnSetsBall`). Given a decoded metric `Ψ ℓ : ℂ → ℂ → ℝ` that a.s. equals
`b · internalMetric D V` on the punctured ball `V = B_R(0) \ {0}` (`S11ac.metricDecoder_punctured_ball`), the family
`decodedVal V Ψ O x y ℓ` (the decoded internal distance `decInt` on any open `O ⊆ B_R` with `O \ {0} ⊆ V`) equals
`b · internalMetric D O` a.s., simultaneously for all such `O`, with one scale `b` per sample. Deterministic except for
the a.s. transfer; measurable in the pairing.
-/

namespace HarmonicBalls.S11m

open Set MeasureTheory Metric
open scoped ENNReal

open Classical in
/-- Radius of the root circles on an open domain `O` containing `0`: a positive radius with `B_ε(0) ⊆ O`
(`Classical.choose` on `Metric.isOpen_iff`); `1` otherwise, where it is not used. -/
noncomputable def localEps (O : Set ℂ) : ℝ :=
  if h : IsOpen O ∧ (0 : ℂ) ∈ O then Classical.choose (Metric.isOpen_iff.mp h.1 0 h.2) else 1

/-- Specification of `localEps`: a positive radius with the ball inside `O`. -/
theorem localEps_spec {O : Set ℂ} (hO : IsOpen O) (h0 : (0 : ℂ) ∈ O) :
    0 < localEps O ∧ ball (0 : ℂ) (localEps O) ⊆ O := by
  have h := Classical.choose_spec (Metric.isOpen_iff.mp hO 0 h0)
  have hd : IsOpen O ∧ (0 : ℂ) ∈ O := ⟨hO, h0⟩
  unfold localEps
  simp only [hd]
  exact h

/-- **Deterministic identity on a bounded domain** (route eq (16) with the root values). If the decoded metric
`ψ` equals `b · internalMetric D V` on the connected open punctured domain `V`, then the decoded internal distance on any
open `O` with `O \ {0} ⊆ V` (connected when `0 ∈ O`) equals `b · internalMetric D O`. -/
theorem decodedVal_eq_const_mul_internalMetric {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {V : Set ℂ} (hVo : IsOpen V) (hconnV : IsConnected V)
    {ψ : ℂ → ℂ → ℝ} {b : ℝ} (hb : 0 < b)
    (hψ : ∀ v ∈ V, ∀ w ∈ V, ENNReal.ofReal (ψ v w) = ENNReal.ofReal b * internalMetric D V v w)
    {O : Set ℂ} (hO : IsOpen O) (hOV : O \ {0} ⊆ V) (hconnO : (0 : ℂ) ∈ O → IsConnected O)
    {x y : ℂ} (hx : x ∈ O) (hy : y ∈ O) :
    decInt V (fun v w => (ENNReal.ofReal (ψ v w)).toReal) localEps O x y =
      ENNReal.ofReal b * internalMetric D O x y := by
  have hDh := toReal_ofReal_eq_const_mul_internalCost hb hψ
  by_cases h0 : (0 : ℂ) ∈ O
  · obtain ⟨hε, hball⟩ := localEps_spec hO h0
    exact decInt_eq_const_mul_internalMetric hD hnonneg hVo hconnV hO (hconnO h0) hOV hb hDh hε hball hx hy
  · unfold decInt
    simp only [h0, ↓reduceIte]
    have hOV' : O ⊆ V := fun v hv => hOV ⟨hv, fun h => h0 (Set.mem_singleton_iff.mp h ▸ hv)⟩
    exact decPunct_eq_const_mul_internalMetric hD hVo hconnV hO hOV' hb hDh hx hy

/-- **Almost sure decoded family.** If a.s. the decoded metric `Ψ (ℓ ω)` is `b_ω · internalMetric (D ω) V` on `V`
(one scale `b_ω` per sample) and `D ω` is a nonnegative Euclidean length metric, then a.s. there is one scale `b`
such that the decoded internal distances on every admissible open domain `O` are `b · internalMetric (D ω) O`. -/
theorem decodedVal_ae_family {Ω Pair : Type*} [MeasurableSpace Ω] {P : Measure Ω} (Ψ : Pair → ℂ → ℂ → ℝ)
    (ℓ : Ω → Pair) (D : Ω → ℂ → ℂ → ℝ) {V : Set ℂ} (hVo : IsOpen V) (hconnV : IsConnected V)
    (hgood : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) ∧ ∀ x y, 0 ≤ D ω x y)
    (hΨ : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ v ∈ V, ∀ w ∈ V, ENNReal.ofReal (Ψ (ℓ ω) v w) = ENNReal.ofReal b * internalMetric (D ω) V v w) :
    ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ O : Set ℂ, IsOpen O → O \ {0} ⊆ V → ((0 : ℂ) ∈ O → IsConnected O) →
      ∀ x ∈ O, ∀ y ∈ O, decInt V (fun v w => (ENNReal.ofReal (Ψ (ℓ ω) v w)).toReal) localEps O x y =
        ENNReal.ofReal b * internalMetric (D ω) O x y := by
  filter_upwards [hgood, hΨ] with ω hg hψ
  obtain ⟨b, hb, hψb⟩ := hψ
  exact ⟨b, hb, fun O hO hOV hc x hx y hy =>
    decodedVal_eq_const_mul_internalMetric hg.1 hg.2 hVo hconnV hb hψb hO hOV hc hx hy⟩

/-- **Measurability in the pairing.** For a family of measurable decoded metrics, every decoded internal distance
`decInt V (Ψ ℓ) localEps O x y` is measurable in `ℓ`. -/
theorem measurable_decodedVal {Pair : Type*} [MeasurableSpace Pair] (V : Set ℂ) {Ψ : Pair → ℂ → ℂ → ℝ}
    (hΨ : ∀ a b : ℂ, Measurable fun ℓ => Ψ ℓ a b) (O : Set ℂ) (x y : ℂ) :
    Measurable fun ℓ => decInt V (fun v w => (ENNReal.ofReal (Ψ ℓ v w)).toReal) localEps O x y :=
  measurable_decInt (Dh := fun ℓ v w => (ENNReal.ofReal (Ψ ℓ v w)).toReal)
    (fun a b => ((hΨ a b).ennreal_ofReal).ennreal_toReal) V localEps O x y

end HarmonicBalls.S11m
