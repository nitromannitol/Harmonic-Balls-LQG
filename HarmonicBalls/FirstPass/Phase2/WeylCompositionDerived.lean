import HarmonicBalls.Steps.Sec11.ContinuousFieldShift

/-! # Weyl composition for continuous weights (phase 2, fp-phase2-weyl-composition-derive, worker z6)

Partial result toward `WeylScalingCompositionFrozen` (`FirstPass/Frozen/S11d.lean:91`). For a whole-plane GFF `hC`
and a continuous shift `g`, the LQG metric of `hC + g` is the Weyl scaling of the metric of `hC` by `g`, and a second
Weyl scaling by a continuous weight `L` composes into the Weyl scaling by `g + L`. Both identities are the Weyl
axiom III (`SatisfiesLQGMetricAxioms.ae_weylScaling`, Defs/LQGMetric.lean) applied to the base fields `hC` and
`hC + g`, together with the field-shift identity `IsLQGMetric.addFunPairing_addFunPairing`.

Not covered here: the frozen statement uses the logarithmic weight `fun z => -α₀ * Real.log ‖z‖`, which is not
continuous at `0`, and it is stated for probability spaces `Ω : Type u` while the axioms quantify over `Ω : Type`. -/

namespace HarmonicBalls

open MeasureTheory Filter

/-- Weyl composition for continuous weights, almost surely: for a whole-plane GFF `hC`, an LQG metric `𝔇` and a
continuous `g`, almost surely, for every continuous weight `L` and all `x y`,
`weylScaling 𝔇(hC + g) ξ L x y = weylScaling 𝔇(hC) ξ (g + L) x y`. -/
theorem weylScaling_composition_continuous_ae {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hgff : IsWholePlaneGFF P hC hcirc)
    (g : ℂ → ℝ) (hg : Continuous g) :
    ∀ᵐ ω ∂P, ∀ L : ℂ → ℝ, Continuous L → ∀ x y : ℂ,
      weylScaling (𝔇 (addFunPairing (hC ω) g)) ξ L x y =
        weylScaling (𝔇 (hC ω)) ξ (fun z => g z + L z) x y := by
  have hzero : ∀ T : (ℂ → ℝ) → ℝ, addFunPairing T (fun _ => 0) = T := by
    intro T
    funext φ
    simp [addFunPairing]
  have hA := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) hgff
    (by intro ω; fun_prop) (by intro x; fun_prop)
  have hB := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ => g) hgff
    (by intro ω; exact hg) (by intro x; fun_prop)
  filter_upwards [hA.ae_weylScaling, hB.ae_weylScaling] with ω hAω hBω
  simp only [hzero] at hAω
  intro L hL x y
  have h1 : ENNReal.ofReal (𝔇 (addFunPairing (addFunPairing (hC ω) g) L) x y) =
      weylScaling (𝔇 (addFunPairing (hC ω) g)) ξ L x y := hBω L hL x y
  have h2 : 𝔇 (addFunPairing (addFunPairing (hC ω) g) L) =
      𝔇 (addFunPairing (hC ω) (fun z => g z + L z)) :=
    h𝔇.addFunPairing_addFunPairing (hC ω) hg hL
  have h3 : ENNReal.ofReal (𝔇 (addFunPairing (hC ω) (fun z => g z + L z)) x y) =
      weylScaling (𝔇 (hC ω)) ξ (fun z => g z + L z) x y := hAω (fun z => g z + L z) (hg.add hL) x y
  rw [← h1, h2]
  exact h3

end HarmonicBalls
