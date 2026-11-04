import HarmonicBalls.Proofs.Sec8.RootedSamplingProbability
import HarmonicBalls.Proofs.Sec8.ObservedLocalRootTransfer

/-! # Positive local mass at a sampled root

The imported Section 8 argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Under a normalized weighted rooted law, every fixed positive-radius ball
centered at the sampled root has positive finite mass. -/
theorem ae_recentered_ball_mass_weightedRestriction_compProd
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂(P ⊗ₘ weightedRestrictionKernel P μ hμ B hB w hw),
      ((μ x.1).map (fun v : ℂ => v - x.2)) (ball 0 ε) ≠ 0 ∧
      ((μ x.1).map (fun v : ℂ => v - x.2)) (ball 0 ε) ≠ ∞ := by
  let κ := weightedRestrictionKernel P μ hμ B hB w hw
  obtain ⟨F, hF, hFeq⟩ := exists_jointlyMeasurable_centeredMeasure P hμ hloc
  have hFm : Measurable (fun x : Ω × ℂ => (F (x.2, x.1)).val) :=
    measurable_subtype_coe.comp (hF.comp (measurable_snd.prodMk measurable_fst))
  let g : Ω × ℂ → ℝ≥0∞ := fun x => (F (x.2, x.1)).val (ball 0 ε)
  have hgm : Measurable g := (Measure.measurable_coe measurableSet_ball).comp hFm
  have hset : MeasurableSet {x : Ω × ℂ | g x ≠ 0 ∧ g x ≠ ∞} :=
    (measurableSet_eq_fun hgm measurable_const).compl.inter
      (measurableSet_eq_fun hgm measurable_const).compl
  have hroot : ∀ᵐ x ∂(P ⊗ₘ κ), g x ≠ 0 ∧ g x ≠ ∞ := by
    apply Measure.ae_compProd_of_ae_ae hset
    filter_upwards [hFeq, hloc, ae_weightedRestrictionKernel_eq P μ hμ B hB w hw]
      with ω heq hl hk
    let : IsLocallyFiniteMeasure (μ ω) := hl
    have hac : κ ω ≪ μ ω := by
      rw [show κ ω = normalizedRestriction ((μ ω).withDensity w) B from hk,
        normalizedRestriction]
      exact Measure.smul_absolutelyContinuous.trans
        (Measure.absolutelyContinuous_restrict.trans (withDensity_absolutelyContinuous _ _))
    filter_upwards [hac.ae_le (ae_recentered_ball_mass_ne_zero_ne_top (μ ω) hε)] with z hz
    change (F (z, ω)).val (ball 0 ε) ≠ 0 ∧ (F (z, ω)).val (ball 0 ε) ≠ ∞
    rw [← heq z]
    exact hz
  filter_upwards [hroot, ae_fst_of_ae_compProd P κ hFeq] with x hx heq
  simpa only [g, ← heq x.2] using hx

#print axioms ae_recentered_ball_mass_weightedRestriction_compProd

end HarmonicBalls
