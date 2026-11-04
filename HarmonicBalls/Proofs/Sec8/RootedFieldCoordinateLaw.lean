import HarmonicBalls.Proofs.Sec8.RootedObservedBindLaw

/-! # Rooted laws in equivalent field coordinates

Reindexing an observed field commutes with the unnormalized rooted law, and
normalized root sampling is dominated by that law. These statements do not
assume the rooted change-of-measure formula. The imported Section 6 development
uses Leonardo Bonanno's whole-plane GFF formalization.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

/-- Measurable reindexing of the observed field commutes with binding the
restricted random measure. -/
theorem map_observed_restricted_bind
    {Ω F G : Type*} [MeasurableSpace Ω] [MeasurableSpace F] [MeasurableSpace G]
    (P : Measure Ω) [SFinite P] (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (X : Ω → F) (hX : Measurable X) (e : F → G) (he : Measurable e)
    (B : Set ℂ) (hB : MeasurableSet B) (hfin : ∀ᵐ ω ∂P, μ ω B ≠ ∞) :
    (P.bind fun ω => ((μ ω).restrict B).map (fun z => (X ω, z))).map
      (fun p => (e p.1, p.2)) =
    P.bind (fun ω => ((μ ω).restrict B).map (fun z => (e (X ω), z))) := by
  have h := observed_restricted_bind_eq_compProd_map P μ hμ (e ∘ X) (he.comp hX) B hB hfin
  simp only [Function.comp_apply] at h
  rw [observed_restricted_bind_eq_compProd_map P μ hμ X hX B hB hfin, h]
  have hemap : Measurable (fun p : F × ℂ => (e p.1, p.2)) :=
    (he.comp measurable_fst).prodMk measurable_snd
  have hXmap : Measurable (fun p : Ω × ℂ => (X p.1, p.2)) :=
    (hX.comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_map hemap hXmap]
  rfl

/-- Sampling a normalized root and observing a reindexed field is dominated
by the reindexed unnormalized rooted law. The restricted mass may vanish. -/
theorem observed_normalized_compProd_ac_map_restricted_bind
    {Ω F G : Type*} [MeasurableSpace Ω] [MeasurableSpace F] [MeasurableSpace G]
    (P : Measure Ω) [SFinite P] (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (X : Ω → F) (hX : Measurable X) (e : F → G) (he : Measurable e)
    (B : Set ℂ) (hB : MeasurableSet B) (hfin : ∀ᵐ ω ∂P, μ ω B ≠ ∞) :
    (P ⊗ₘ weightedRestrictionKernel P μ hμ B hB (fun _ => 1) measurable_const).map
      (fun p => (e (X p.1), p.2)) ≪
    (P.bind fun ω => ((μ ω).restrict B).map (fun z => (X ω, z))).map
      (fun p => (e p.1, p.2)) := by
  rw [map_observed_restricted_bind P μ hμ X hX e he B hB hfin]
  exact observed_normalized_compProd_ac_restricted_bind P μ hμ (e ∘ X) (he.comp hX)
    B hB hfin

/-- The raw whole-plane GFF rooted bind becomes the bundled pairing-process
rooted bind under the canonical measurable field equivalence. -/
theorem IsWholePlaneGFF.map_raw_rooted_unitBall_bind
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P] {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ) :
    (P.bind fun ω => ((μ ω).restrict (ball 0 1)).map
      (fun z => ((fun φ : RawMeanZeroTest => hC ω φ.1), z))).map
      (fun p => (meanZeroFieldEquiv p.1, p.2)) =
    P.bind (fun ω => ((μ ω).restrict (ball 0 1)).map
      (fun z => (Section6.pairingProc hC ω, z))) := by
  have hfc : (fun ω => fieldCircleAverage 0 (hcirc ω)) = hcirc := by
    funext ω r z
    simp [fieldCircleAverage]
  have hμ' : IsLQGMeasureOfField P γ 0 hcirc μ := by
    simpa only [IsLQGMeasureOfField, hfc] using hμ
  have hmeas : AEMeasurable μ P := hh.aemeasurable_lqgMeasure hμ'
  have hfield : Measurable (fun ω => fun φ : RawMeanZeroTest => hC ω φ.1) := by
    apply measurable_pi_iff.mpr
    intro φ
    exact hh.measurable_pairing φ.1 φ.2.1
  have hfin : ∀ᵐ ω ∂P, μ ω (ball 0 1) ≠ ∞ := by
    filter_upwards [hμ] with ω hω
    let : IsLocallyFiniteMeasure (μ ω) := hω.isLocallyFiniteMeasure
    exact measure_ball_ne_top
  exact map_observed_restricted_bind P μ hmeas _ hfield meanZeroFieldEquiv
    meanZeroFieldEquiv.measurable _ measurableSet_ball hfin

#print axioms map_observed_restricted_bind
#print axioms observed_normalized_compProd_ac_map_restricted_bind
#print axioms IsWholePlaneGFF.map_raw_rooted_unitBall_bind

end HarmonicBalls
