import HarmonicBalls.Proofs.Sec5.FamilyUniqueness

/-!
# Determination of the regularized cluster family (Proposition 5.6, Lemma 5.8)

Audit chat 164 PRO, `notes/fp-gaps/CHATGPT-hb-sec5-audit-PRO.md` lines 184-239 (operator note 2026-11-10 09:07 UTC, item (3)):
Proposition 5.6 and Lemma 5.8 quantify over every family satisfying the compatibility clause of Theorem 5.5, so the family
must be determined. Argument (audit lines 196-197): for `t > 0` the closure of `Λ t` lies in a ball `B(0, s)` for each family
(field `isBounded` of `SatisfiesHarmonicBallConditions`, `Draft/Section5.lean`), and for every `r ≥ s` both families equal
`regularizedCluster μ r z t` (the clause of `IsRegularizedClusterFamily`, `Draft/Section5.lean:88`). Hence they agree on `(0, ∞)`.

The proof is the existing theorem `HarmonicBalls.IsRegularizedClusterFamily.eqOn` (`Proofs/Sec5/FamilyUniqueness.lean`), cited
here under the name used by Proposition 5.6 and Lemma 5.8. No hypothesis is added and no Prop is frozen.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- **Determination lemma (Proposition 5.6, Lemma 5.8).** Two families satisfying the compatibility clause of Theorem 5.5
(`IsRegularizedClusterFamily`) agree at every positive time: `Λ t = Λ' t` for all `t > 0`. -/
theorem isRegularizedClusterFamily_eqOn {μ : Measure ℂ} {Λ Λ' : ℝ → Set ℂ} {z : ℂ}
    (h : IsRegularizedClusterFamily μ Λ z) (h' : IsRegularizedClusterFamily μ Λ' z) :
    Set.EqOn Λ Λ' (Set.Ioi 0) :=
  IsRegularizedClusterFamily.eqOn h h'

end HarmonicBalls
