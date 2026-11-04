import HarmonicBalls.Proofs.Sec8.LocalCircleDecoder
import HarmonicBalls.Proofs.Sec8.LQGUniversalApproximationLaw

/-! # Law of whole-plane GFF observables

The imported Section 8 argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ProbabilityTheory

namespace HarmonicBalls

/-- All admissible test-function pairings and positive-radius circle averages
of the whole-plane field. -/
def wholePlaneObservableProc {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) : GFFObservable.Admissible → ℝ :=
  fun o => o.1.eval (hC ω) (hcirc ω)

/-- The whole-plane observable process is measurable for the product
sigma-algebra. -/
theorem IsWholePlaneGFF.measurable_wholePlaneObservableProc
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) : Measurable (wholePlaneObservableProc hC hcirc) := by
  apply measurable_pi_iff.mpr
  rintro ⟨o, ho⟩
  cases o with
  | pairing φ => exact hGFF.measurable_pairing φ ho
  | circle r z => exact hGFF.measurable_circle r z ho

/-- The covariance specification uniquely determines the joint law of all
admissible whole-plane GFF observables. -/
theorem IsWholePlaneGFF.map_wholePlaneObservableProc_eq
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {gC : Ξ → (ℂ → ℝ) → ℝ} {gcirc : Ξ → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (gGFF : IsWholePlaneGFF Q gC gcirc) :
    P.map (wholePlaneObservableProc hC hcirc) = Q.map (wholePlaneObservableProc gC gcirc) := by
  exact (hGFF.identDistrib_observables_across_spaces gGFF).map_eq

/-- A centered-circle decoder chosen under one whole-plane GFF has the same
pointwise almost-sure interpretation under every other whole-plane GFF. -/
theorem IsWholePlaneGFF.exists_common_centeredCircle_decoder
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} {α₀ ε r : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {gC : Ξ → (ℂ → ℝ) → ℝ} {gcirc : Ξ → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (gGFF : IsWholePlaneGFF Q gC gcirc)
    (hr : 0 < r) :
    ∃ D : (Section6.LocalTest (ball 0 ε) → ℝ) → ℂ → ℝ,
      Measurable (Function.uncurry D) ∧
      (∀ᵐ ω ∂P, ∀ z, closedBall z r ⊆ ball 0 ε →
        D (Section6.localPairingProc (ball 0 ε) hC ω) z =
          fieldCircleAverage α₀ (hcirc ω) r z - fieldCircleAverage α₀ (hcirc ω) r 0) ∧
      ∀ z, closedBall z r ⊆ ball 0 ε → ∀ᵐ ω ∂Q,
        D (Section6.localPairingProc (ball 0 ε) gC ω) z =
          fieldCircleAverage α₀ (gcirc ω) r z - fieldCircleAverage α₀ (gcirc ω) r 0 := by
  obtain ⟨D, hDm, hDeq⟩ :=
    hGFF.exists_localPairing_centeredCircle_decoder (α₀ := α₀) (ε := ε) hr
  refine ⟨D, hDm, hDeq, ?_⟩
  intro z hz
  let L : (GFFObservable.Admissible → ℝ) → Section6.LocalTest (ball 0 ε) → ℝ :=
    fun x φ => x ⟨.pairing φ.1.1, Section6.isTestFunction_of_testC φ.1.1⟩
  have hL : Measurable L := measurable_pi_iff.mpr fun φ => measurable_pi_apply _
  let t : GFFObservable.Admissible := ⟨.circle r z, hr⟩
  let t₀ : GFFObservable.Admissible := ⟨.circle r 0, hr⟩
  let A : Set (GFFObservable.Admissible → ℝ) := {x |
    D (L x) z = (x t - α₀ * Real.circleAverage (fun w => Real.log ‖w‖) z r) -
      (x t₀ - α₀ * Real.circleAverage (fun w => Real.log ‖w‖) 0 r)}
  have hA : MeasurableSet A := by
    apply measurableSet_eq_fun
    · exact hDm.comp (hL.prodMk measurable_const)
    · exact ((measurable_pi_apply t).sub measurable_const).sub
        ((measurable_pi_apply t₀).sub measurable_const)
  have hP : ∀ᵐ x ∂(P.map (wholePlaneObservableProc hC hcirc)), x ∈ A := by
    apply (ae_map_iff hGFF.measurable_wholePlaneObservableProc.aemeasurable hA).2
    filter_upwards [hDeq] with ω hω
    have hh := hω z hz
    change D (fun φ : Section6.LocalTest (ball 0 ε) => hC ω φ.1.1) z = _ at hh
    simpa only [A, mem_ofPred_eq, L, wholePlaneObservableProc, t, t₀,
      GFFObservable.eval, fieldCircleAverage] using hh
  rw [hGFF.map_wholePlaneObservableProc_eq gGFF] at hP
  have hQ := (ae_map_iff gGFF.measurable_wholePlaneObservableProc.aemeasurable hA).1 hP
  filter_upwards [hQ] with ω hω
  change D (fun φ : Section6.LocalTest (ball 0 ε) => gC ω φ.1.1) z = _
  simpa only [A, mem_ofPred_eq, L, wholePlaneObservableProc, t, t₀,
    GFFObservable.eval, fieldCircleAverage] using hω

#print axioms IsWholePlaneGFF.map_wholePlaneObservableProc_eq
#print axioms IsWholePlaneGFF.exists_common_centeredCircle_decoder

end HarmonicBalls
