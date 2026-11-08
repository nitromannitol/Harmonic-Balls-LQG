import HarmonicBalls.Proofs.Sec8.AEGermTriviality
import HarmonicBalls.Proofs.Sec8.OriginGermZeroOne

/-! # Completed origin germ

The underlying whole-plane GFF germ theorem uses Leonardo Bonanno's
LatticeProb formalization. Radius-dependent event representatives suffice;
no simultaneous field realization is asserted here.
-/

open MeasureTheory Set Metric

namespace HarmonicBalls

/-- A trivial countably cofinal germ remains trivial for events admitting
radius-dependent almost-everywhere equal raw representatives. -/
theorem measure_zero_or_one_of_ae_local_germ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (germ : ℝ → MeasurableSpace Ω) (r : ℕ → ℝ)
    (hr : ∀ n, 0 < r n) (hcofinal : ∀ ε, 0 < ε → ∃ n, r n ≤ ε)
    (hrmono : Antitone r) (hgmono : Monotone germ)
    (htrivial : ∀ B : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] B) →
      P B = 0 ∨ P B = 1)
    (A : Set Ω)
    (hA : ∀ ε, 0 < ε → ∃ B : Set Ω, MeasurableSet[germ ε] B ∧ A =ᵐ[P] B) :
    P A = 0 ∨ P A = 1 := by
  obtain ⟨B, hB, hAB⟩ := exists_germ_measurable_event_of_ae_local P germ r hr
    hcofinal hrmono hgmono A hA
  rw [measure_congr hAB]
  exact htrivial B hB

/-- The completed origin germ of the whole-plane GFF modulo constants is
trivial, in the event-level almost-everywhere representative sense. -/
theorem IsWholePlaneGFF.completed_origin_germ_trivial
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (α₀ : ℝ) (A : Set Ω)
    (hA : ∀ ε : ℝ, 0 < ε → ∃ B : Set Ω,
      MeasurableSet[Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)] B ∧
        A =ᵐ[P] B) :
    P A = 0 ∨ P A = 1 := by
  exact measure_zero_or_one_of_ae_local_germ P
    (fun ε => Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε))
    dyadicScale dyadicScale_pos dyadicScale_germ_cofinal.2 dyadicScale_germ_cofinal.1
    (monotone_fieldSigmaAlgebraModConst_ball α₀ hC 0)
    (h.origin_germ_trivial α₀) A hA

end HarmonicBalls
