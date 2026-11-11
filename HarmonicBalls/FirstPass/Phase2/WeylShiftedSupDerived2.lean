import HarmonicBalls.FirstPass.Phase2.WeylShiftedSupDerived
import HarmonicBalls.FirstPass.Phase2.WeylScaledEuclideanDerived
import HarmonicBalls.FirstPass.Phase2.InternalMetricClosedDerived
import HarmonicBalls.Steps.Sec11.InternalMetricContinuity
import LatticeProb.Prob.WeylSupMeasurable

/-!
# The supremum of the Weyl-shifted internal metric over a closed dyadic square is a.e. measurable

Derivation of `WeylShiftedSupMeasurableFrozen` (`FirstPass/Frozen/S11c.lean:217`). For a closed dyadic square `S`, the
supremum `⨆ u ∈ S, ⨆ v ∈ S, internalMetric (weylShiftPair γ ξ f (μ, D)).2 S u v` is a.s. measurable. The route:

1. Closed-set exhaustion for bounded closed sets (`internalMetric_closed_eq_iSup_thickening_of_bounded`): the internal
   metric of `C` is the supremum over `k` of the internal metrics of the open neighbourhoods `thickening ((k+1)⁻¹) C`.
   It follows from `internalMetricClosedEqIInfThickening_derived` (`FirstPass/Phase2/InternalMetricClosedDerived.lean`),
   taking `n` with `C ⊆ closedBall 0 (n+1)`.
2. Each open neighbourhood `U` gives a function `(x, y) ↦ internalMetric D U x y` that is continuous on `U ×ˢ U` for a
   Euclidean length metric `D` (`IsEuclideanLengthMetric.continuousOn_internalMetric_pair`,
   `HarmonicBalls/Steps/Sec11/InternalMetricContinuity.lean`). A supremum of functions that are lower semicontinuous on
   `C ×ˢ C` is lower semicontinuous there, so `(x, y) ↦ internalMetric D C x y` is lower semicontinuous on `C ×ˢ C`.
3. The Weyl scaling `e^{ξ f} · D` of the a.s. Euclidean length metric `D` of the LQG metric is a Euclidean length metric
   (`weylScaledEuclidean_derived`, `FirstPass/Phase2/WeylScaledEuclideanDerived.lean`). Its a.s. lower semicontinuity on
   `S ×ˢ S` follows from 2.
4. A countable dense `D₀ ⊆ S` reduces the supremum to `D₀ ×ˢ D₀`
   (`LatticeProb.Prob.aemeasurable_iSup_mem_of_lowerSemicontinuousOn`, `HarmonicBalls/LPStage/WeylSupMeasurable.lean`), and
   each term is a.e. measurable (`weylShiftInternalMetric_aemeasurable_closed`, `FirstPass/Phase2/WeylShiftedSupDerived.lean`).

Inputs. The Euclidean length property of `D ω` (clause I of `LQGMetricFieldAxiomsUnivFrozen`), the Weyl composition
`WeylScalingCompositionFrozen` and the a.e. measurability `LQGInternalMetricWeylAeMeasurableFrozen` are
explicit hypotheses, as in `WeylShiftedSupDerived.lean`. The closed-set exhaustion and the Weyl scaling property are proved
here or in the imported files, with no hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

universe u

/-- Closed-set exhaustion for a bounded closed set `C`: the internal metric of `C` is the supremum over `k` of the internal
metrics of the open neighbourhoods `thickening ((k+1)⁻¹) C`. The inequality `≥` holds since `C` is contained in each
neighbourhood; the inequality `≤` is `internalMetricClosedEqIInfThickening_derived` with `n` such that `C ⊆ closedBall 0 (n+1)`. -/
theorem internalMetric_closed_eq_iSup_thickening_of_bounded {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {C : Set ℂ} (hC : IsClosed C) (hb : Bornology.IsBounded C) (x y : ℂ) :
    internalMetric D C x y = ⨆ k : ℕ, internalMetric D (Metric.thickening (((k : ℝ) + 1)⁻¹) C) x y := by
  obtain ⟨r, hr⟩ := hb.subset_closedBall 0
  have hN : C ⊆ Metric.closedBall 0 (((⌈r⌉₊ : ℕ) : ℝ) + 1) :=
    hr.trans (Metric.closedBall_subset_closedBall (by linarith [Nat.le_ceil r]))
  apply le_antisymm
  · calc internalMetric D C x y
        = ⨅ n : ℕ, ⨆ k : ℕ, internalMetric D
            (Metric.thickening (((k : ℝ) + 1)⁻¹) (C ∩ Metric.closedBall 0 ((n : ℝ) + 1))) x y :=
          internalMetric_closed_eq_iInf_sup hD C hC x y
      _ ≤ ⨆ k : ℕ, internalMetric D
            (Metric.thickening (((k : ℝ) + 1)⁻¹) (C ∩ Metric.closedBall 0 (((⌈r⌉₊ : ℕ) : ℝ) + 1))) x y :=
          iInf_le _ _
      _ = ⨆ k : ℕ, internalMetric D (Metric.thickening (((k : ℝ) + 1)⁻¹) C) x y := by
          rw [Set.inter_eq_left.mpr hN]
  · refine iSup_le fun k => ?_
    have hδ : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
    exact internalMetric_anti_set (Metric.self_subset_thickening hδ C) x y

/-- A Euclidean length metric `D` with nonnegative values has an internal metric of a bounded closed set `C` that is
lower semicontinuous on `C ×ˢ C`. Proof: by the closed-set exhaustion, the internal metric of `C` is the supremum over `k` of
the internal metrics of the open neighbourhoods `U_k = thickening ((k+1)⁻¹) C`; each is continuous on `U_k ×ˢ U_k`
(`continuousOn_internalMetric_pair`), hence lower semicontinuous on `C ×ˢ C`, and a supremum of such functions is lower
semicontinuous. -/
theorem IsEuclideanLengthMetric.lowerSemicontinuousOn_internalMetric_pair_closed {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) (hnonneg : ∀ x y, 0 ≤ D x y) {C : Set ℂ} (hC : IsClosed C)
    (hb : Bornology.IsBounded C) :
    LowerSemicontinuousOn (fun p : ℂ × ℂ => internalMetric D C p.1 p.2) (C ×ˢ C) := by
  have hk : ∀ k : ℕ, LowerSemicontinuousOn
      (fun p : ℂ × ℂ => internalMetric D (Metric.thickening (((k : ℝ) + 1)⁻¹) C) p.1 p.2) (C ×ˢ C) := by
    intro k
    have hδ : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
    have hsub : C ×ˢ C ⊆ Metric.thickening (((k : ℝ) + 1)⁻¹) C ×ˢ Metric.thickening (((k : ℝ) + 1)⁻¹) C :=
      Set.prod_mono (Metric.self_subset_thickening hδ C) (Metric.self_subset_thickening hδ C)
    exact ((hD.continuousOn_internalMetric_pair hnonneg Metric.isOpen_thickening).mono hsub).lowerSemicontinuousOn
  intro p hp a ha
  have ha' : a < ⨆ k : ℕ, internalMetric D (Metric.thickening (((k : ℝ) + 1)⁻¹) C) p.1 p.2 := by
    rw [← internalMetric_closed_eq_iSup_thickening_of_bounded hD hC hb]
    exact ha
  obtain ⟨k, hk_lt⟩ := lt_iSup_iff.mp ha'
  filter_upwards [hk k p hp a hk_lt] with q hq
  have hδ : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
  exact lt_of_lt_of_le hq (internalMetric_anti_set (Metric.self_subset_thickening hδ C) q.1 q.2)

/-- A closed dyadic square is closed and bounded. -/
theorem isClosed_and_isBounded_of_isClosedDyadicSquare {S : Set ℂ} (hS : IsClosedDyadicSquare S) :
    IsClosed S ∧ Bornology.IsBounded S := by
  obtain ⟨n, j, k, rfl⟩ := hS
  unfold closedDyadicSquare
  refine ⟨?_, ?_⟩
  · exact (isClosed_Icc.preimage Complex.continuous_re).inter (isClosed_Icc.preimage Complex.continuous_im)
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨|(j : ℝ) * 2 ^ (-n)| + |((j : ℝ) + 1) * 2 ^ (-n)| + (|(k : ℝ) * 2 ^ (-n)| + |((k : ℝ) + 1) * 2 ^ (-n)|),
      fun z hz => ?_⟩
    obtain ⟨hre, him⟩ := hz
    rw [mem_closedBall_zero_iff]
    have h1 : |z.re| ≤ |(j : ℝ) * 2 ^ (-n)| + |((j : ℝ) + 1) * 2 ^ (-n)| :=
      abs_le.mpr ⟨by linarith [hre.1, neg_abs_le ((j : ℝ) * 2 ^ (-n)), abs_nonneg (((j : ℝ) + 1) * 2 ^ (-n))],
        by linarith [hre.2, le_abs_self (((j : ℝ) + 1) * 2 ^ (-n)), abs_nonneg ((j : ℝ) * 2 ^ (-n))]⟩
    have h2 : |z.im| ≤ |(k : ℝ) * 2 ^ (-n)| + |((k : ℝ) + 1) * 2 ^ (-n)| :=
      abs_le.mpr ⟨by linarith [him.1, neg_abs_le ((k : ℝ) * 2 ^ (-n)), abs_nonneg (((k : ℝ) + 1) * 2 ^ (-n))],
        by linarith [him.2, le_abs_self (((k : ℝ) + 1) * 2 ^ (-n)), abs_nonneg ((k : ℝ) * 2 ^ (-n))]⟩
    exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)

/-- Every subset of `ℂ` has a countable subset which is dense in it. -/
theorem exists_countable_dense_subset_of_set (S : Set ℂ) :
    ∃ D₀ ⊆ S, D₀.Countable ∧ S ⊆ closure D₀ := by
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense S
  refine ⟨Subtype.val '' s, Subtype.coe_image_subset S s, hsc.image _, fun x hx => ?_⟩
  have hmem : (⟨x, hx⟩ : S) ∈ closure s := by
    rw [hsd.closure_eq]
    exact mem_univ _
  exact closure_subtype.mp hmem

/-- **Derived**: the supremum over a closed dyadic square `S` of the internal metric of the Weyl-shifted LQG metric
is a.s. measurable, `WeylShiftedSupMeasurableFrozen` (`FirstPass/Frozen/S11c.lean:217`). The explicit hypotheses are the
TRUE frozen inputs of `WeylShiftedSupDerived.lean`: the Euclidean length property of the LQG metric (clause I of
`LQGMetricFieldAxiomsUnivFrozen`), the Weyl composition and the a.e. measurability. The closed-set
exhaustion and the Weyl scaling property (`weylScaledEuclidean_derived`) are proved in the imported files. -/
theorem weylShiftedSupMeasurable_derived
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) (hWSC : WeylScalingCompositionFrozen.{u})
    (hInt : LQGInternalMetricWeylAeMeasurableFrozen.{u}) : WeylShiftedSupMeasurableFrozen.{u} := by
  intro γ α₀ ξ hγ0 hγ2 hα Ω _ P hC hcirc μ D hW _ hLQG f hf hfc _ S hS
  have : IsProbabilityMeasure P := hW.isProbabilityMeasure
  obtain ⟨𝔇, h𝔇, hD⟩ := hLQG
  obtain ⟨hSc, hSb⟩ := isClosed_and_isBounded_of_isClosedDyadicSquare hS
  -- the LQG metric is a.s. a Euclidean length metric (clause I of `LQGMetricFieldAxiomsUnivFrozen`)
  have hEucD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) := by
    filter_upwards [(hAx Ω P γ ξ α₀ hC hcirc hW hγ0 hγ2 hα 𝔇 h𝔇).1, hD] with ω hI hDω
    have hDeq : D ω = fun a b => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) a b).toReal := by
      funext a b
      obtain ⟨h0, h1⟩ := hDω a b
      rw [← h1, ENNReal.toReal_ofReal h0]
    rw [hDeq]
    exact hI.2
  -- a.s. lower semicontinuity on `S ×ˢ S` of the endpoint function of the Weyl-shifted metric
  have hlsc : ∀ᵐ ω ∂P, LowerSemicontinuousOn
      (fun p : ℂ × ℂ => internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S p.1 p.2) (S ×ˢ S) := by
    filter_upwards [hEucD] with ω hω
    exact IsEuclideanLengthMetric.lowerSemicontinuousOn_internalMetric_pair_closed
      (weylScaledEuclidean_derived (D ω) ξ f hω hf hfc) (fun _ _ => ENNReal.toReal_nonneg) hSc hSb
  obtain ⟨D₀, hD₀S, hD₀c, hSD₀⟩ := exists_countable_dense_subset_of_set S
  have key := LatticeProb.Prob.aemeasurable_iSup_mem_of_lowerSemicontinuousOn (P := P)
    (F := fun ω p => internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S p.1 p.2)
    (S := S ×ˢ S) (D := D₀ ×ˢ D₀) (hD₀c.prod hD₀c) (Set.prod_mono hD₀S hD₀S)
    (by rw [closure_prod_eq]; exact Set.prod_mono hSD₀ hSD₀)
    (fun p hp => weylShiftInternalMetric_aemeasurable_closed P γ ξ α₀ hC hcirc hW hγ0 hγ2 hα hAx hWSC hInt
      internalMetricClosedEqIInfThickening_derived weylScaledEuclidean_derived 𝔇 h𝔇 D μ hD f hf hfc S hSc p.1 p.2
      (hD₀S hp.1) (hD₀S hp.2))
    hlsc
  refine key.congr (Eventually.of_forall fun ω => ?_)
  exact biSup_prod

end HarmonicBalls
