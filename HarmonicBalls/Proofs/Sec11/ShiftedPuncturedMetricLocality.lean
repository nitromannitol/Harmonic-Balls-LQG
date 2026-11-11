import HarmonicBalls.Proofs.Sec11.PuncturedSingularMetricLocality
import HarmonicBalls.Proofs.Sec11.ShiftedSingularMetricLocality

/-! # Locality on nested punctured domains

The Section 8 inputs use Leonardo Bonanno's LatticeProb code. The results
here apply on domains separated from the origin; they do not establish
locality on neighborhoods of the origin.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- The internal singular metric on an open domain separated from zero has a
local version after an arbitrary measurable random constant shift. The field
may be observed on a larger set. -/
theorem IsWholePlaneGFF.exists_shifted_internal_singularMetric_away_zero
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (c : Ω → ℝ) (hc : Measurable c)
    {U V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U) {r : ℝ} (hr : 0 < r)
    (haway : ∀ z ∈ V, r ≤ ‖z‖) :
    ∃ G : Ω → ℂ → ℂ → ℝ≥0∞,
      (∀ x y, Measurable[fieldSigmaAlgebra α
        (fun ω => addFunPairing (hC ω) (fun _ => c ω)) U] (fun ω => G ω x y)) ∧
      ∀ᵐ ω ∂P, ∀ x ∈ V, ∀ y ∈ V,
        internalMetric (fun u v =>
          (weylScaling (𝔇 (addFunPairing (hC ω) (fun _ => c ω))) ξ
            (fun z => -α * Real.log ‖z‖) u v).toReal) V x y = G ω x y := by
  let f : ℂ → ℝ := fun z => -α * Real.log (max ‖z‖ r)
  have hf : Continuous f := by
    apply continuous_const.mul
    apply (continuous_norm.max continuous_const).log
    intro z
    exact ne_of_gt (lt_of_lt_of_le hr (le_max_right _ _))
  have hfg : ∀ z ∈ V, (fun x : ℂ => -α * Real.log ‖x‖) z = f z := by
    intro z hz
    dsimp only [f]
    rw [max_eq_left (haway z hz)]
  have ha := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun ω z => f z + c ω) h
    (fun _ => hf.add continuous_const) (fun _ => measurable_const.add hc)
  obtain ⟨G, hG, hGeq⟩ := ha.locality V hV
  have hGmeas (x y : ℂ) : Measurable[fieldSigmaAlgebra α
      (fun ω => addFunPairing (hC ω) (fun _ => c ω)) V] (fun ω => G ω x y) := by
    rw [← fieldSigmaAlgebra_background_add_random_constant α hC V f hf c]
    rw [fieldSigmaAlgebra_eq, fieldSigmaAlgebra_eq_pairingSigmaAlgebra]
    have heq : (fun ω => fieldPairing 0
        (addFunPairing (hC ω) (fun z => f z + c ω))) =
        (fun ω => addFunPairing (hC ω) (fun z => f z + c ω)) := by
      funext ω φ
      simp [fieldPairing]
    rw [heq]
    exact hG x y
  have hbase := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 h
    (fun ω z => f z + c ω) (fun _ => hf.add continuous_const)
    (fun _ => measurable_const.add hc)
  have hs := h.ae_internal_singularMetric_add_random_constant 𝔇 h𝔇 hD c hc
  refine ⟨G, fun x y => (hGmeas x y).mono (fieldSigmaAlgebra_mono α _ hVU) le_rfl, ?_⟩
  filter_upwards [hbase, hD, hmetric, hs, hGeq] with ω hb hd hm hs hg x hx y hy
  have hscale : ∀ u v, ENNReal.ofReal (Real.exp (ξ * c ω) * D ω u v) =
      weylScaling (𝔇 (hC ω)) ξ
        (fun z => -α * Real.log ‖z‖ + c ω) u v := by
    intro u v
    rw [ENNReal.ofReal_mul (Real.exp_nonneg _), (hd u v).2]
    exact (weylScaling_add_const _ ξ (c ω) (fun z => -α * Real.log ‖z‖) u v).symm
  have heq := hb.1.internalMetric_weylScaling_eq_of_eqOn
    (hm.const_mul (Real.exp_pos _)) hb.2.1 ξ
    (fun z => -α * Real.log ‖z‖ + c ω) (fun z => f z + c ω)
    hscale hb.2.2.2.1 hV (fun z hz => congrArg (fun a => a + c ω) (hfg z hz)) x y
  rw [hs V x y, ← internalMetric_const_mul (D ω) (Real.exp_pos _), heq]
  exact hg x hx y hy

/-- A single reference test on a larger set yields modulo-constant metric
locality on each nested open set separated from zero. -/
theorem IsWholePlaneGFF.exists_modConst_nested_internal_singularMetric_away_zero
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {U V : Set ℂ} (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U)
    {r : ℝ} (hr : 0 < r) (haway : ∀ z ∈ V, r ≤ ‖z‖)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1) :
    ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
      (∀ᵐ ω ∂P, 0 < c ω) ∧
      (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC U] (fun ω => G ω x y)) ∧
      (∀ᵐ ω ∂P, ∀ x ∈ V, ∀ y ∈ V,
        internalMetric (fun x y => c ω * D ω x y) V x y = G ω x y) := by
  have hc : Measurable (fun ω => -hC ω ψ) :=
    (h.measurable_pairing ψ (hψ.mono_set (subset_univ _))).neg
  exact h.exists_modConst_internalMetric_of_shifted_locality 𝔇 h𝔇 hD hmetric hV hne
    ψ hψ hψint
    (h.exists_shifted_internal_singularMetric_away_zero 𝔇 h𝔇 hD hmetric
      (fun ω => -hC ω ψ) hc hV hVU hr haway)


end HarmonicBalls
