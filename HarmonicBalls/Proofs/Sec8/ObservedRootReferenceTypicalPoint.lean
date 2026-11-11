import HarmonicBalls.Proofs.Sec8.RootedBindTypicalPoint
import HarmonicBalls.Proofs.Sec11.PinchReferenceLaw

/-! # Typical points from observed rooted reference laws

Fixed-root estimates transfer to typical points using a comparison on the
observed field, without requiring a comparison of the underlying sample spaces.
The rooted-law comparison is an explicit hypothesis. The imported Section 6
development uses Leonardo Bonanno's whole-plane GFF formalization.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

/-- A fixed-root estimate for an observed field transfers through a rooted
reference-law comparison on each set of a countable cover. -/
theorem ae_ae_of_observed_root_reference_cover
    {Ω Ξ F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace F]
    (P : Measure Ω) (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (X : Ω → F) (hX : Measurable X) (B : ℕ → Set ℂ)
    (hB : ∀ n, MeasurableSet (B n)) (hcover : ∀ z, ∃ n, z ∈ B n)
    (hfin : ∀ n, ∀ᵐ ω ∂P, μ ω (B n) ≠ ∞)
    (ρ : ℕ → Measure ℂ) (Q : Measure Ξ) [SFinite Q]
    (shift : ℕ → ℂ × Ξ → F) (hshift : ∀ n, Measurable (shift n))
    (R : ℕ → ℂ → Measure F) {p : F × ℂ → Prop}
    (hp : MeasurableSet {x | p x})
    (hrooted : ∀ n, (P.bind fun ω => ((μ ω).restrict (B n)).map
      (fun z => (X ω, z))) ≪ shiftedRootReferenceLaw (ρ n) Q (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, Q.map (fun ω => shift n (z, ω)) ≪ R n z)
    (hfixed : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ f ∂(R n z), p (f, z)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, p (X ω, z) := by
  apply ae_ae_of_observed_restricted_bind_cover P μ hμ X hX B hB hcover hfin
  intro n
  exact (hrooted n).ae_le (ae_shiftedRootReferenceLaw_of_ae_comparison
    (ρ n) Q (shift n) (hshift n) (R n) hp (hac n) (hfixed n))

/-- The raw unit-disk rooted law transfers fixed-root estimates to LQG-typical
points in the unit disk. Both the rooted comparison and the fixed-root law
comparison remain explicit. -/
theorem IsWholePlaneGFF.ae_ae_mem_unitBall_of_root_reference
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    (ρ : Measure ℂ) (Q : Measure Ξ) [SFinite Q]
    (shift : ℂ × Ξ → RawMeanZeroTest → ℝ) (hshift : Measurable shift)
    (R : ℂ → Measure (RawMeanZeroTest → ℝ))
    {p : (RawMeanZeroTest → ℝ) × ℂ → Prop} (hp : MeasurableSet {x | p x})
    (hrooted : (P.bind fun ω => ((μ ω).restrict (ball 0 1)).map
      (fun z => ((fun φ : RawMeanZeroTest => hC ω φ.1), z))) ≪
        shiftedRootReferenceLaw ρ Q shift)
    (hac : ∀ᵐ z ∂ρ, Q.map (fun ω => shift (z, ω)) ≪ R z)
    (hfixed : ∀ᵐ z ∂ρ, ∀ᵐ f ∂(R z), p (f, z)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ ball 0 1 →
      p ((fun φ : RawMeanZeroTest => hC ω φ.1), z) := by
  apply hh.ae_ae_mem_unitBall_of_raw_rooted_bind hμ
  exact hrooted.ae_le (ae_shiftedRootReferenceLaw_of_ae_comparison
    ρ Q shift hshift R hp hac hfixed)

end HarmonicBalls
