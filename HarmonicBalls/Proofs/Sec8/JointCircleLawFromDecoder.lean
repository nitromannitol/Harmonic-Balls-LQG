import HarmonicBalls.Proofs.Sec8.LocalCircleDecoder

/-! # Joint circle laws from a local field decoder

The imported Section 8 development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization.
-/

open MeasureTheory Filter Set Metric
open scoped Topology

namespace HarmonicBalls

/-- A local centered-circle decoder converts domination of local field laws
into domination of their joint field and circle laws, whenever the decoder
also represents the centered circle under the second law. -/
theorem IsWholePlaneGFF.exists_centeredCircle_decoder_for_joint_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α₀ ε r : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hr : 0 < r) :
    ∃ D : (Section6.LocalTest (ball 0 ε) → ℝ) → ℂ → ℝ,
      Measurable (Function.uncurry D) ∧
      (∀ᵐ ω ∂P, ∀ z, closedBall z r ⊆ ball 0 ε →
        D (Section6.localPairingProc (ball 0 ε) hC ω) z =
          fieldCircleAverage α₀ (hcirc ω) r z - fieldCircleAverage α₀ (hcirc ω) r 0) ∧
      ∀ {Ξ : Type*} [MeasurableSpace Ξ] (Q : Measure Ξ)
        (Y : Ξ → (Section6.LocalTest (ball 0 ε) → ℝ)) (_hY : Measurable Y)
        (_hdom : Q.map Y ≪ P.map (Section6.localPairingProc (ball 0 ε) hC))
        (g : Ξ → ℝ) (z : ℂ) (_hz : closedBall z r ⊆ ball 0 ε),
        (∀ᵐ ξ ∂Q, D (Y ξ) z = g ξ) →
        Q.map (fun ξ => (Y ξ, g ξ)) ≪
          P.map (fun ω => (Section6.localPairingProc (ball 0 ε) hC ω,
            fieldCircleAverage α₀ (hcirc ω) r z -
              fieldCircleAverage α₀ (hcirc ω) r 0)) := by
  obtain ⟨D, hDm, hDref⟩ := hGFF.exists_localPairing_centeredCircle_decoder
    (α₀ := α₀) (ε := ε) hr
  refine ⟨D, hDm, hDref, ?_⟩
  intro Ξ _ Q Y hY hdom g z hz hroot
  let X := Section6.localPairingProc (ball 0 ε) hC
  have hX : Measurable X := measurable_pi_iff.mpr fun φ =>
    hGFF.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)
  let F := fun x => (x, D x z)
  have hF : Measurable F :=
    measurable_id.prodMk (hDm.comp (measurable_id.prodMk measurable_const))
  have hrootmap : Q.map (fun ξ => (Y ξ, g ξ)) = Q.map (F ∘ Y) := by
    apply Measure.map_congr
    filter_upwards [hroot] with ξ hξ
    simp only [Function.comp_def, F, hξ]
  have hrefmap : P.map (fun ω => (X ω,
      fieldCircleAverage α₀ (hcirc ω) r z - fieldCircleAverage α₀ (hcirc ω) r 0)) =
      P.map (F ∘ X) := by
    apply Measure.map_congr
    filter_upwards [hDref] with ω hω
    change (X ω, _) = (X ω, D (X ω) z)
    rw [show D (X ω) z = _ from hω z hz]
  rw [hrootmap, hrefmap, ← Measure.map_map hF hY, ← Measure.map_map hF hX]
  exact hdom.map hF

#print axioms IsWholePlaneGFF.exists_centeredCircle_decoder_for_joint_law

end HarmonicBalls
