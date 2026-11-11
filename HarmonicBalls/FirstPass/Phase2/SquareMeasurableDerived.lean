import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.Frozen.S11e
import HarmonicBalls.Proofs.Sec6.MeasureEvaluation
import HarmonicBalls.Proposed.LQG

/-!
# Derived measurability inputs of triage group A

Two frozen Props of `HarmonicBalls/FirstPass/Frozen` are derived here, each from one literature input of
`HarmonicBalls/Proposed/LQG.lean`, taken as an explicit hypothesis in its universally quantified form (the binder form
of `closure_1_3_derivedInputs`, `HarmonicBalls/FirstPass/Phase2/DerivedInputsSec1to10.lean`). No frozen Prop of `HarmonicBalls/FirstPass`
is used, and no Prop is frozen here.

* `lqgMeasureSquareMeasurable_derived` proves `LQGMeasureSquareMeasurableFrozen` (`Frozen/S11c.lean:117`) from the
  Proposed input `LQGMeasureLocality` (Fact 2.1 II, `Proposed/LQG.lean:97`).
* `lqgMetricPointwiseAEMeasurable_derived` proves `LQGMetricPointwiseAEMeasurableFrozen` (`Frozen/S11e.lean:27`) from
  the Proposed input `LQGMetricFieldAxioms` (Fact 2.2 I-II, `Proposed/LQG.lean:225`).

Both conclusions are the frozen Props exactly as typed.
-/

namespace HarmonicBalls

open MeasureTheory Set

universe u

/-- **Derived: `LQGMeasureSquareMeasurableFrozen`** (`Frozen/S11c.lean:117`). For every closed dyadic square `S`, the map
`ω ↦ μ_ω(S)` is almost everywhere measurable, where `μ` is the γ-LQG area measure of `h = h^ℂ - α₀ log |·|`.

Input: `hmeasure`, the Proposed input `LQGMeasureLocality` (Fact 2.1 II, paper line 407, `Proposed/LQG.lean:97`), in its
universally quantified form. Written argument (locality, Fact 2.1 II, and continuity of the finite-mass evaluations):
for open `U`, `μ_ω(U)` is a.s. equal to a `σ(h|_U)`-measurable variable. The Borel evaluation at the closed set `S` is
then a.e. measurable by the open-to-Borel extension `Section6.aemeasurable_lqg_measure_borel`
(`Proofs/Sec6/MeasureEvaluation.lean:71`): a Dynkin induction from open sets, finite mass of the balls `B(0, n)`
(`IsLQGMeasureOfField`, local finiteness), and monotone limits in `n`. `S` is compact, hence closed, hence Borel. -/
theorem lqgMeasureSquareMeasurable_derived
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureLocality P γ α₀ hC hcirc) :
    LQGMeasureSquareMeasurableFrozen.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ S hS
  exact Section6.aemeasurable_lqg_measure_borel hγ hγ2 hα hGFF hμ
    (hmeasure γ α₀ Ω P hC hcirc) S hS.isCompact.isClosed.measurableSet

/-- **Derived: `LQGMetricPointwiseAEMeasurableFrozen`** (`Frozen/S11e.lean:27`). For a whole-plane GFF realization
`(hC, hcirc)` with `γ ∈ (0, 2)` and a realized LQG metric `D` of the field with zero exponent (`IsLQGMetricOfField P γ ξ 0
hC D`), every evaluation `ω ↦ D ω x y` is almost everywhere measurable.

Input: `hFA`, the Proposed input `LQGMetricFieldAxioms` (Fact 2.2 I-II, paper lines 432-453, `Proposed/LQG.lean:225`), in
its universally quantified form. Written argument (Gwynne-Miller 2021, Section 1.2, Axioms I-II; Bou-Rabee-Gwynne Fact 2.2):
the metric `D_h` of the field is finite a.s. (I). Locality (II) with `U = ℂ` gives `G ω x y`, measurable with respect to
`σ(h|_ℂ)`, and a.s. equal to the internal metric of `D_h` over `ℂ`. Since `D_h` is a length metric,
`IsEuclideanLengthMetric.ofReal_eq_internalMetric` (`Defs/LQGMetric.lean`) identifies that internal metric with `D_h`, so
`D_h(x, y) = G(x, y)` a.s. Each pairing is measurable (`IsWholePlaneGFF.measurable_pairing`), so `σ(h|_ℂ)` is contained
in the ambient σ-algebra, and `G ω x y` is measurable. Finally `D ω x y = (D_h ω x y).toReal` a.s. by `IsLQGMetricOfField`
at `α₀ = 0` (the Weyl factor is `e^0 = 1`). -/
theorem lqgMetricPointwiseAEMeasurable_derived
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc) :
    LQGMetricPointwiseAEMeasurableFrozen := by
  intro γ ξ Ω mΩ P _ hC hcirc D hGFF hγ hγ2 hD x y
  obtain ⟨𝔇, hM, hae⟩ := hD
  have hα : (0 : ℝ) < lqgQ γ := by
    unfold lqgQ
    exact add_pos (div_pos two_pos hγ) (half_pos hγ)
  obtain ⟨hI, hII, -, -⟩ := hFA γ ξ 0 Ω P hC hcirc hGFF hγ hγ2 hα 𝔇 hM
  obtain ⟨G, hGm, hG⟩ := hII Set.univ isOpen_univ
  have hle : fieldSigmaAlgebra 0 hC Set.univ ≤ mΩ := by
    unfold fieldSigmaAlgebra
    refine iSup₂_le fun φ hφ => ?_
    refine Measurable.comap_le ?_
    simpa [fieldPairing] using hGFF.measurable_pairing φ hφ
  have hGmeas : Measurable (fun ω => G ω x y) := (hGm x y).mono hle le_rfl
  have hEq : (fun ω => D ω x y) =ᵐ[P] (fun ω => (G ω x y).toReal) := by
    filter_upwards [hae, hI, hG] with ω hωae hωI hωG
    have hωD := hωae x y
    have h1 : ENNReal.ofReal (D ω x y) = G ω x y := by
      rw [hωD.2, ← hωG x (mem_univ x) y (mem_univ y), ← hωI.2.ofReal_eq_internalMetric x y,
        ENNReal.ofReal_toReal (hωI.1 x y).ne]
    rw [← h1, ENNReal.toReal_ofReal hωD.1]
  exact hGmeas.ennreal_toReal.aemeasurable.congr hEq.symm

end HarmonicBalls
