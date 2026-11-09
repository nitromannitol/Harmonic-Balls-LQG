import HarmonicBalls.Draft.Section11

/-!
# FIRST-PASS FROZEN inputs of Lemmas 11.7 and 11.10 (task fp-S11c-11-7-redo-11-10, worker n1)

Each `Prop` here is EXTERNAL: a general GFF / LQG / measure-theory / potential-theory fact, not a statement about
this paper's clusters, odometers, harmonic balls or IDLA processes. Its docstring gives the source locator, or
"standard; locator pending". Used by the `firstPass_11_10` route in `FirstPass/S11c.lean`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- The Weyl shift of an LQG pair `(ν, d)` (a measure and a metric on `ℂ`) by a function `f`: the measure acquires
the density `exp (γ f)` and the metric is the `d`-length weighted metric with weight `exp (ξ f)`, that is
`weylScaling d ξ f` (`Defs/LQGMetric.lean`). Paper Facts 2.1 and 2.2 give this as the transformation of
`(μ_h, D_h)` under `h ↦ h + f`. Caveat: the metric component is real-valued, so `toReal` is applied; the frozen
statement below is used only where the weighted distances are finite. -/
noncomputable def weylShiftPair (γ ξ : ℝ) (f : ℂ → ℝ) (p : Measure ℂ × (ℂ → ℂ → ℝ)) :
    Measure ℂ × (ℂ → ℂ → ℝ) :=
  (p.1.withDensity (fun z => ENNReal.ofReal (Real.exp (γ * f z))),
    fun u v => (weylScaling p.2 ξ f u v).toReal)

/-- The enlargement `Ŝ` of the dyadic cell `closedDyadicSquare n j k` used in the proof of Lemma 11.10 (paper
line 3010): the closed square with the same centre and side `2^{-n} + 2^{-n-2}`. -/
def enlargedDyadicCell (n j k : ℤ) : Set ℂ :=
  {z : ℂ | |z.re - ((j : ℝ) + 1 / 2) * (2 : ℝ) ^ (-n)| ≤ ((2 : ℝ) ^ (-n) + (2 : ℝ) ^ (-n - 2)) / 2 ∧
    |z.im - ((k : ℝ) + 1 / 2) * (2 : ℝ) ^ (-n)| ≤ ((2 : ℝ) ^ (-n) + (2 : ℝ) ^ (-n - 2)) / 2}

/-- FIRST-PASS FROZEN. Cameron-Martin positivity transfer for the joint law of the LQG measure and LQG metric
(candidate form of the wave-3 ruling, 2026-11-09; the metric component is corrected to `weylScaling`, see
`weylShiftPair`). Let `f` be smooth, compactly supported and zero on the unit circle. If the event that the shifted
pair `weylShiftPair γ ξ f (μ, D)` lies in a measurable set `B` has positive probability, then so does the event that
`(μ, D)` lies in `B`. Measurability of `ω ↦ (μ ω, D ω)` is an explicit hypothesis.
Why it holds: the Weyl scaling of the LQG measure and metric under `h ↦ h + f` (paper Facts 2.1, 2.2) identifies the
pair for `h + f` with `weylShiftPair γ ξ f (μ_h, D_h)`, and the laws of the whole-plane GFF `h` and `h + f` are
mutually absolutely continuous (Cameron-Martin for smooth compactly supported `f` vanishing on the unit circle).
Source: Miller-Sheffield, Imaginary Geometry IV, arXiv:1302.4738v2, Proposition 2.9 (printed page 49; the cited form
`MillerSheffieldIG4Prop29` in `Proposed/MillerSheffieldIG4.lean` is Hilbert-space level only), with the Weyl scaling
of Duplantier-Sheffield 2011 for the LQG measure and of the LQG metric (paper Facts 2.1, 2.2; locator pending).
Used by: firstPass_11_10. -/
def CameronMartinPositivityTransferFrozen : Prop :=
  ∀ (γ α₀ ξ : ℝ) (f : ℂ → ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ContDiff ℝ ⊤ f → HasCompactSupport f → (∀ z : ℂ, ‖z‖ = 1 → f z = 0) →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
    Measurable (fun ω => (μ ω, D ω)) →
    ∀ B : Set (Measure ℂ × (ℂ → ℂ → ℝ)), MeasurableSet B →
      0 < (P.map (fun ω => (μ ω, D ω))) (weylShiftPair γ ξ f ⁻¹' B) →
      0 < (P.map (fun ω => (μ ω, D ω))) B

/-- FIRST-PASS FROZEN. Small internal diameter of the enlarged dyadic cells, simultaneously for all cells of one
level inside a closed dyadic square `S2` disjoint from the unit circle, in inner-probability form.
Why it holds (as printed): each cell has internal diameter tending to zero in probability as the level grows
(the pointwise small-scale continuity of the LQG metric).
FLAG (defect (b) of the Lemma 11.10 proof, paper lines 3010-3016, reported 2026-11-09): the printed step passes from
the pointwise statement to the simultaneous statement over about `4^N` cells by a union bound, which needs a
quantitative tail that the printed statement does not give. This Prop is therefore the printed simultaneous form
and must be ruled on by the operator before it is used as an external input.
Source: Ding-Dubédat-Dunlap-Falconet, Tightness of Liouville first passage percolation for γ < 2 (Publ. IHES 2020),
Lemma 3.19, as cited by paper `dubedat2020weak` (locator pending).
Used by: firstPass_11_10. -/
def DyadicCellDiamSmallFrozen : Prop :=
  ∀ (γ α₀ ξ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ S2 : Set ℂ, IsClosedDyadicSquare S2 → Disjoint S2 (sphere 0 1) →
  ∀ ε η : ℝ, 0 < ε → 0 < η →
  ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    ∃ A ⊆ {ω | ∀ j k : ℤ, closedDyadicSquare (N : ℤ) j k ⊆ S2 →
        ∀ u ∈ enlargedDyadicCell (N : ℤ) j k ∩ S2, ∀ v ∈ enlargedDyadicCell (N : ℤ) j k ∩ S2,
          internalMetric (D ω) (enlargedDyadicCell (N : ℤ) j k ∩ S2) u v ≤ ENNReal.ofReal ε},
      MeasurableSet A ∧ ENNReal.ofReal (1 - η) ≤ P A

/-- FIRST-PASS FROZEN. Finite diameter of the closure of a connected finite union of closed dyadic squares, for the
LQG metric: almost surely there is a finite bound on the internal distances within the union.
Why it holds: the metric is finite and continuous on a compact connected union of cells (the metric is a length
metric whose local distances are finite on compact sets).
Source: Ding-Dubédat-Dunlap-Falconet (Publ. IHES 2020), Lemma 3.9, as cited by paper `dubedat2020weak` in the proof of
Lemma 11.10 (paper lines 3026-3028; locator pending).
Used by: firstPass_11_10. -/
def ConnectedSquareUnionDiamFiniteFrozen : Prop :=
  ∀ (γ α₀ ξ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ K : Set ℂ, (∃ F : Finset (Set ℂ), (∀ S ∈ F, IsClosedDyadicSquare S) ∧ K = ⋃ S ∈ F, S) → IsConnected K →
  ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ u ∈ K, ∀ v ∈ K, internalMetric (D ω) K u v ≤ ENNReal.ofReal A

end HarmonicBalls
