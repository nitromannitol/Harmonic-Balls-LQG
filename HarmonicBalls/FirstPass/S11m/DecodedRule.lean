import HarmonicBalls.FirstPass.S11m.DecodedRoot
import HarmonicBalls.FirstPass.S11m.ClearanceLocal

/-!
# Measurability of the decoded clearance quantities

A metric decoder gives
a family `Dh ℓ : ℂ → ℂ → ℝ` indexed by pairings `ℓ`, measurable in `ℓ` for each pair of points (no continuity in the points).
The decoded internal quantities are the localized clearance infima `localClearanceInf S Q (Dh ℓ)` over countable chain
vertices `S` and countable clearance sets `Q`, and the decoded root values are `limsup`s of countable infima over
countable circle sets. Both are measurable in `ℓ`, so the decoded rule is a measurable set of pairings.

Deterministic measurability lemmas; the set `S`, the sets `Q` and the circle sets `C n` are fixed countable sets chosen
independently of the pairing and of the metric.
-/

namespace HarmonicBalls.S11m

open Set Filter MeasureTheory
open scoped ENNReal

variable {Pair : Type*} [MeasurableSpace Pair]

/-- The localized clearance infimum of a measurable family of decoded metrics is measurable in the pairing. -/
theorem measurable_decClearanceInf {Dh : Pair → ℂ → ℂ → ℝ} (hDh : ∀ a b, Measurable fun ℓ => Dh ℓ a b)
    {S Q : Set ℂ} (hS : S.Countable) (hQ : Q.Countable) (x y : ℂ) :
    Measurable fun ℓ => localClearanceInf S Q (Dh ℓ) x y := by
  have := hS.to_subtype
  exact measurable_localClearanceInf hQ hDh x y

/-- The decoded root value along countable circle sets `C n` (the `limsup` of countable infima of decoded localized
clearance infima) is measurable in the pairing. -/
theorem measurable_decRoot {Dh : Pair → ℂ → ℂ → ℝ} (hDh : ∀ a b, Measurable fun ℓ => Dh ℓ a b)
    {S : Set ℂ} (hS : S.Countable) {Qn C : ℕ → Set ℂ} (hQn : ∀ n, (Qn n).Countable) (hC : ∀ n, (C n).Countable)
    (x : ℂ) :
    Measurable fun ℓ => limsup (fun n => ⨅ y ∈ C n, localClearanceInf S (Qn n) (Dh ℓ) y x) atTop := by
  refine measurable_limsup_nat _ fun n => ?_
  exact measurable_biInf_of_countable (hC n) (fun y ℓ => localClearanceInf S (Qn n) (Dh ℓ) y x)
    fun y => measurable_decClearanceInf hDh hS (hQn n) y x

end HarmonicBalls.S11m
