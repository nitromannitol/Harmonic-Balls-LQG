import HarmonicBalls.Draft.Section11

/-!
# First pass, Section 11 pinch positivity (fp-S11e, owner n2)

Results of this file: Lemmas 11.12, 11.15, 11.16, 11.17 of the paper (`lemma:mu_h-pinch-positive-probability`,
`lemma:first-event-proof`, `lemma:second-event-proof`, `lemma:third-event-proof`). Current state:

* `firstPass_11_16` is PROVED-FP: Lemma 11.17 (`PinchThirdEventPositiveStmt`) implies Lemma 11.16
  (`PinchSecondEventPositiveStmt`) with the same configuration and the same witnesses, since `Ẽ₁ ∩ Ẽ₂ ∩ Ẽ₃ ⊆ Ẽ₁ ∩ Ẽ₂`
  (paper lines 3281-3285).
* Lemmas 11.15 and 11.17 and Lemma 11.12 remain OPEN (their NEW local-certificate steps are not yet formalized; see
  `reports/n2.md`).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- Lemma 11.16 (`lemma:second-event-proof`, paper line 3281), first-pass form. It follows from Lemma 11.17
(`PinchThirdEventPositiveStmt`, paper line 3285): the same configuration `U, V, W, T, Q', Q, δ₀` and the same
measurable witnesses `A`, because `Ẽ₁ ∩ Ẽ₂ ∩ Ẽ₃ ⊆ Ẽ₁ ∩ Ẽ₂` and `P A > 0` is unchanged. -/
theorem firstPass_11_16 (h : PinchThirdEventPositiveStmt.{u}) : PinchSecondEventPositiveStmt.{u} := by
  obtain ⟨U, V, W, T, Q', Q, δ, hconfig, hpos⟩ := h
  refine ⟨U, V, W, T, Q', Q, δ, hconfig, ?_⟩
  intro γ ξ hγ hγ₂ Ω inst P hC hcirc μ D hgff hμ hD M hM
  obtain ⟨A, hA, hmeas, hp⟩ := hpos γ ξ hγ hγ₂ Ω P hC hcirc μ D hgff hμ hD M hM
  exact ⟨A, fun ω hω => ⟨(hA hω).1, (hA hω).2.1⟩, hmeas, hp⟩

#print axioms firstPass_11_16

end HarmonicBalls
