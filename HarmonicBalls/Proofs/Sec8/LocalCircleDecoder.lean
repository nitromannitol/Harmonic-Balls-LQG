import HarmonicBalls.Proofs.Sec8.CenteredCircleLocal
import HarmonicBalls.Proofs.Sec8.CenteredLQGApproximation
import HarmonicBalls.Proofs.Sec6.AnnulusLawTransfer
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! # Local decoders for centered circle averages

The imported Section 8 argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

open MeasureTheory Filter Set Metric
open scoped Topology

namespace HarmonicBalls

/-- A jointly measurable function of a sample and a point, measurable in the
sample through a given process, factors jointly through that process. -/
theorem exists_joint_measurable_factor_of_comap
    {Ω E Z : Type*} [MeasurableSpace E] [MeasurableSpace Z]
    (X : Ω → E) (d : Ω → Z → ℝ)
    (hd : @Measurable (Ω × Z) ℝ
      ((MeasurableSpace.comap X inferInstance).prod inferInstance) _ (Function.uncurry d)) :
    ∃ D : E → Z → ℝ, Measurable (Function.uncurry D) ∧
      ∀ ω z, D (X ω) z = d ω z := by
  have hd' : @Measurable (Ω × Z) ℝ
      (MeasurableSpace.comap (Prod.map X id) inferInstance) _ (Function.uncurry d) := by
    have hm : (MeasurableSpace.comap X inferInstance).prod (inferInstance : MeasurableSpace Z) =
        MeasurableSpace.comap (Prod.map X id) (inferInstance : MeasurableSpace (E × Z)) := by
      change (MeasurableSpace.comap X inferInstance).prod (inferInstance : MeasurableSpace Z) =
        ((inferInstance : MeasurableSpace E).prod (inferInstance : MeasurableSpace Z)).comap
          (Prod.map X id)
      rw [MeasurableSpace.comap_prodMap, MeasurableSpace.comap_id]
    exact hm ▸ hd
  obtain ⟨D, hD, heq⟩ := hd'.exists_eq_measurable_comp
  refine ⟨fun x z => D (x, z), hD, ?_⟩
  intro ω z
  exact (congrFun heq (ω, z)).symm

/-- A centered circle average has a jointly measurable decoder on local
mean-zero field pairings; its equality holds whenever the circle stays inside
the chosen field neighborhood. -/
theorem IsWholePlaneGFF.exists_localPairing_centeredCircle_decoder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {ε r : ℝ} (hr : 0 < r) :
    ∃ D : (Section6.LocalTest (ball 0 ε) → ℝ) → ℂ → ℝ,
      Measurable (Function.uncurry D) ∧
      ∀ᵐ ω ∂P, ∀ z, closedBall z r ⊆ ball 0 ε →
        D (Section6.localPairingProc (ball 0 ε) hC ω) z =
          fieldCircleAverage α₀ (hcirc ω) r z - fieldCircleAverage α₀ (hcirc ω) r 0 := by
  obtain ⟨d, hdm, hdeq⟩ := hGFF.exists_joint_centered_circle_version (α₀ := α₀) (ε := ε) hr
  rw [Section6.fieldSigmaAlgebraModConst_eq, Section6.fieldSigmaAlgebraModConst_eq_comap] at hdm
  obtain ⟨D, hD, heq⟩ := exists_joint_measurable_factor_of_comap
    (Section6.localPairingProc (ball 0 ε) hC) d hdm
  refine ⟨D, hD, ?_⟩
  filter_upwards [hdeq] with ω hω z hz
  exact (heq ω z).trans (hω z hz)

/-- Normalized circle-average approximations on buffered sets can be
realized simultaneously as measurable functions of the local field modulo
constants. -/
theorem IsWholePlaneGFF.exists_localPairing_normalizedLQGApprox
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (E : ℕ → Set ℂ)
    (hEm : ∀ n, MeasurableSet (E n))
    (hbuffer : ∀ n z, z ∈ E n → closedBall z (dyadicScale n) ⊆ ball 0 ε) :
    ∃ F : ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → Measure ℂ,
      (∀ n, Measurable (F n)) ∧ ∀ᵐ ω ∂P, ∀ n,
        F n (Section6.localPairingProc (ball 0 ε) hC ω) =
          normalizedRestriction (lqgApprox γ (fieldCircleAverage α₀ (hcirc ω))
            (dyadicScale n)) (E n) := by
  choose D hDm hDeq using fun n =>
    hGFF.exists_localPairing_centeredCircle_decoder (α₀ := α₀) (ε := ε) (dyadicScale_pos n)
  refine ⟨fun n x => normalizedRestriction
    (volume.withDensity fun z => ENNReal.ofReal (Real.exp (γ * D n x z))) (E n), ?_, ?_⟩
  · exact fun n => measurable_normalized_centeredLQGApprox γ (D n) (hDm n) (E n) (hEm n)
  · filter_upwards [ae_all_iff.mpr hDeq] with ω hω n
    exact (normalizedRestriction_lqgApprox_eq_of_centered_on γ
      (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale_pos n) 0 (hEm n)
      (D n (Section6.localPairingProc (ball 0 ε) hC ω))
      (fun z hz => hω n z (hbuffer n z hz))).symm

#print axioms exists_joint_measurable_factor_of_comap
#print axioms IsWholePlaneGFF.exists_localPairing_centeredCircle_decoder
#print axioms IsWholePlaneGFF.exists_localPairing_normalizedLQGApprox

end HarmonicBalls
