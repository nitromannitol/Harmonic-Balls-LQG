import HarmonicBalls.Proofs.Sec11.MassDiameterCoreThreshold
import HarmonicBalls.Proofs.Sec11.MassDiameterCoreWeight
import HarmonicBalls.Steps.Sec11.WholePlaneWeylShift

/-! # Core shifts retaining an outside event

The whole-plane Weyl shift uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization. -/

namespace HarmonicBalls
open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- Uniform tile bounds and protected mass on a positive-measure seed event
give a core shift which keeps that seed event while making the diameter small. -/
theorem exists_positive_mass_small_diameter_wholePlane_shift_preserving_event
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (γ ξ : ℝ) (hξ : 0 < ξ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    {ι : Type*} {O O₀ O₁ K C S : Set ℂ} {H J : ι → Set ℂ}
    {δ a ε : ℝ} {c : ℝ≥0∞}
    (ha : 0 ≤ a) (hmargin : a + a < ε)
    (hO : IsOpen O) (hO₀ : IsOpen O₀) (hO₀conn : IsConnected O₀)
    (hO₀O : O₀ ⊆ O) (hO₁ : IsOpen O₁)
    (hO₀compact : IsCompact (closure O₀)) (hO₀O₁ : closure O₀ ⊆ O₁)
    (hdisjoint : Disjoint O₁ S) (hS : MeasurableSet S)
    (hJopen : ∀ i, IsOpen (J i)) (hJO : ∀ i, J i ⊆ O)
    (hCcompact : IsCompact C) (hCO₀ : C ⊆ O₀)
    (hbuffer : O ⊆ thickening δ K)
    (hcover : ∀ x ∈ K, x ∈ C ∨ ∃ i, x ∈ H i)
    (hattach : ∀ i, (H i ∩ C).Nonempty)
    (A : Set Ω) (hAp : 0 < P A)
    (hA : ∀ ω ∈ A, c < μ ω S ∧ ∀ i, ∀ x ∈ H i, ∀ y ∈ H i,
      internalMetric (𝔇 (hC ω)) (J i) x y ≤ ENNReal.ofReal a) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧ (∀ z, f z ≤ 0) ∧
      (∀ z ∉ O₁, f z = 0) ∧
      0 < P {ω | ω ∈ A ∧ c < ((μ ω).withDensity
        (fun z => ENNReal.ofReal (Real.exp (γ * f z)))) S ∧
        internalDiam (𝔇 (addFunPairing (hC ω) f)) δ K < ENNReal.ofReal ε} := by
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
    have h := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 hgff
      (fun _ _ => 0) (fun _ => continuous_const) (fun _ => measurable_const)
    exact h.mono fun _ hw => hw.1
  obtain ⟨n, hn⟩ := exists_positive_measure_core_internal_distance_bound P A
    (fun ω => 𝔇 (hC ω)) hCcompact hO₀ hO₀conn hCO₀ hAp hmetric
  obtain ⟨B, f, hf, hfnonpos, hfglobal, hfcore, hfS, hfoutside, hbudget⟩ :=
    exists_smooth_core_contraction_weight_with_budget hO₀compact hO₁ hO₀O₁ hdisjoint
      hξ ha (show 0 ≤ (n : ℝ) by positivity) hmargin
  have hw := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 hgff
    (fun _ => f) (fun _ => hf.1.continuous) (fun _ => measurable_const)
  let E : Set Ω := {ω | ω ∈ A ∧ ∀ x ∈ C, ∀ y ∈ C,
      internalMetric (𝔇 (hC ω)) O₀ x y < (n : ℝ≥0∞)}
  let G : Set Ω := {ω | IsEuclideanLengthMetric (𝔇 (hC ω)) ∧
      IsEuclideanLengthMetric (𝔇 (addFunPairing (hC ω) f)) ∧
      (∀ x y, weylScaling (𝔇 (hC ω)) ξ 0 x y = ENNReal.ofReal (𝔇 (hC ω) x y)) ∧
      (∀ x y, ENNReal.ofReal (𝔇 (addFunPairing (hC ω) f) x y) =
        weylScaling (𝔇 (hC ω)) ξ f x y)}
  have hG : ∀ᵐ ω ∂P, ω ∈ G := hw.mono fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  have heq : E =ᵐ[P] E ∩ G := by
    filter_upwards [hG] with ω hω
    simp [hω]
  have hp : 0 < P (E ∩ G) := by rwa [← measure_congr heq]
  refine ⟨f, hf, hfnonpos, hfoutside, hp.trans_le (measure_mono ?_)⟩
  intro ω hω
  have hnonneg : ∀ x y, 0 ≤ 𝔇 (addFunPairing (hC ω) f) x y := by
    intro x y
    have ht := hω.2.2.1.triangle x y x
    rw [hω.2.2.1.self_eq_zero, hω.2.2.1.symm y x] at ht
    linarith
  have hglue := hω.2.1.mass_and_internalDiam_of_weyl_core_gluing hω.2.2.1 hnonneg (γ := γ) (μ := μ ω)
    hO hO₀ hO₀O hJopen hJO (hCO₀.trans hO₀O) hbuffer hcover hattach
    hω.2.2.2.1 hω.2.2.2.2 hfglobal (fun z hz => (hfcore z hz).le)
    (hA ω hω.1.1).2 (by
      intro x hx y hy
      simpa using (hω.1.2 x hx y hy).le) hbudget hS hfS
  exact ⟨hω.1.1, hglue.1 ▸ (hA ω hω.1.1).1, hglue.2⟩

end HarmonicBalls
