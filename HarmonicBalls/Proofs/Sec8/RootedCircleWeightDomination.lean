import HarmonicBalls.Proofs.Sec8.RootedCircleMeasurableVersion
import HarmonicBalls.Proofs.Sec8.RootedSamplingEquivalence
import HarmonicBalls.Proofs.Sec8.RootedWeightDomination

/-! # Domination of rooted circle observation laws

The imported Section 8 development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A weighted rooted observation on a set is dominated by the corresponding
unweighted rooted observation on a larger set. The measurable version of the
translated circle is used to transfer domination to the observation laws. -/
theorem IsWholePlaneGFF.rooted_centeredCircle_law_ac_of_subset
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {γ α : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hm : AEMeasurable μ P)
    (B U : Set ℂ) (hB : MeasurableSet B) (hU : MeasurableSet U) (hBU : B ⊆ U)
    (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hfinB : ∀ᵐ ω ∂P, ((μ ω).withDensity w) B ≠ ∞)
    (hfinU : ∀ᵐ ω ∂P, (μ ω) U ≠ ∞)
    (Y : Ω × ℂ → E) (hY : Measurable Y) (n : ℕ) (z : ℂ) :
    (P ⊗ₘ unnormalizedWeightedRestrictionKernel P μ hm B hB w hw).map (fun x => (Y x,
      fieldCircleAverage α (hcirc x.1) (dyadicScale n) (z + x.2) -
        fieldCircleAverage α (hcirc x.1) (dyadicScale n) x.2)) ≪
    (P ⊗ₘ unnormalizedWeightedRestrictionKernel P μ hm U hU (fun _ => 1)
      measurable_const).map (fun x => (Y x,
      fieldCircleAverage α (hcirc x.1) (dyadicScale n) (z + x.2) -
        fieldCircleAverage α (hcirc x.1) (dyadicScale n) x.2)) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let K := weightedRestrictionKernel P μ hm U hU (fun _ => 1) measurable_const
  let L := unnormalizedWeightedRestrictionKernel P μ hm U hU (fun _ => 1) measurable_const
  let J := unnormalizedWeightedRestrictionKernel P μ hm B hB w hw
  have hfinU' : ∀ᵐ ω ∂P, ((μ ω).withDensity (fun _ => 1)) U ≠ ∞ := by
    simpa only [withDensity_const, one_smul] using hfinU
  have hLK : P ⊗ₘ L ≪ P ⊗ₘ K :=
    unnormalizedWeightedRestrictionKernel_compProd_ac_normalized P μ hm U hU
      (fun _ => 1) measurable_const hfinU'
  have hJL : P ⊗ₘ J ≪ P ⊗ₘ L :=
    unnormalizedWeightedRestrictionKernel_compProd_ac_of_subset P μ hm B U hB hU hBU
      w hw hfinB hfinU
  obtain ⟨g, hgm, hgeq⟩ :=
    hGFF.exists_rooted_circle_measurable_version hμ hm U hU (fun _ => 1) measurable_const
  let f : Ω × ℂ → E × ℝ := fun x => (Y x, g x (dyadicScale n) z - g x (dyadicScale n) 0)
  have hpoint (v : ℂ) : Measurable (fun x => g x (dyadicScale n) v) :=
    (hgm n).comp (measurable_id.prodMk measurable_const)
  have hf : Measurable f := hY.prodMk ((hpoint z).sub (hpoint 0))
  have heqK : ∀ᵐ x ∂(P ⊗ₘ K), f x = (Y x,
      fieldCircleAverage α (hcirc x.1) (dyadicScale n) (z + x.2) -
        fieldCircleAverage α (hcirc x.1) (dyadicScale n) x.2) := by
    filter_upwards [hgeq] with x hx
    simp only [f, hx.1 n z, hx.1 n 0, zero_add]
  have heqL := hLK.ae_le heqK
  have heqJ := hJL.ae_le heqL
  have hac := hJL.map hf
  rw [Measure.map_congr heqJ, Measure.map_congr heqL] at hac
  exact hac

/-- The preceding domination applies to each weighted localization, using
local finiteness of the Liouville measure. -/
theorem IsWholePlaneGFF.rooted_centeredCircle_law_ac_weightedLocalization_ball
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {γ α : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hm : AEMeasurable μ P)
    (w : ℂ → ℝ≥0∞) (hw : Measurable w) (k : ℕ)
    (Y : Ω × ℂ → E) (hY : Measurable Y) (n : ℕ) (z : ℂ) :
    (P ⊗ₘ unnormalizedWeightedRestrictionKernel P μ hm (weightedLocalization w k)
      (measurableSet_weightedLocalization hw k) w hw).map (fun x => (Y x,
      fieldCircleAverage α (hcirc x.1) (dyadicScale n) (z + x.2) -
        fieldCircleAverage α (hcirc x.1) (dyadicScale n) x.2)) ≪
    (P ⊗ₘ unnormalizedWeightedRestrictionKernel P μ hm (ball 0 ((k : ℝ) + 1))
      measurableSet_ball (fun _ => 1) measurable_const).map (fun x => (Y x,
      fieldCircleAverage α (hcirc x.1) (dyadicScale n) (z + x.2) -
        fieldCircleAverage α (hcirc x.1) (dyadicScale n) x.2)) := by
  apply hGFF.rooted_centeredCircle_law_ac_of_subset hμ hm _ _
    (measurableSet_weightedLocalization hw k) measurableSet_ball inter_subset_left w hw
  · filter_upwards [hμ] with ω hω
    let : IsLocallyFiniteMeasure (μ ω) := hω.isLocallyFiniteMeasure
    exact weightedLocalization_measure_ne_top (μ ω) hw k
  · filter_upwards [hμ] with ω hω
    let : IsLocallyFiniteMeasure (μ ω) := hω.isLocallyFiniteMeasure
    exact measure_ball_lt_top.ne
  · exact hY

#print axioms IsWholePlaneGFF.rooted_centeredCircle_law_ac_of_subset
#print axioms IsWholePlaneGFF.rooted_centeredCircle_law_ac_weightedLocalization_ball

end HarmonicBalls
