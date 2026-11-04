import HarmonicBalls.Proofs.Sec8.WholePlaneObservableLaw
import HarmonicBalls.Proofs.Sec8.CenteredLQGApproximation

/-! # Common circle-average approximations

The imported Section 8 argument uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A decoder that is pointwise almost surely correct on a buffered measurable
set is correct for almost every sample and almost every point on that set. -/
theorem IsWholePlaneGFF.ae_ae_centeredCircle_decoder
    {Ξ : Type*} [MeasurableSpace Ξ] {Q : Measure Ξ} {α₀ ε r : ℝ}
    {gC : Ξ → (ℂ → ℝ) → ℝ} {gcirc : Ξ → ℝ → ℂ → ℝ}
    (gGFF : IsWholePlaneGFF Q gC gcirc) (hr : 0 < r)
    (E : Set ℂ) (hE : MeasurableSet E)
    (hbuffer : ∀ z ∈ E, closedBall z r ⊆ ball 0 ε)
    (D : (Section6.LocalTest (ball 0 ε) → ℝ) → ℂ → ℝ)
    (hD : Measurable (Function.uncurry D))
    (heq : ∀ z ∈ E, ∀ᵐ ω ∂Q,
      D (Section6.localPairingProc (ball 0 ε) gC ω) z =
        fieldCircleAverage α₀ (gcirc ω) r z - fieldCircleAverage α₀ (gcirc ω) r 0) :
    ∀ᵐ ω ∂Q, ∀ᵐ z ∂(volume.restrict E),
      D (Section6.localPairingProc (ball 0 ε) gC ω) z =
        fieldCircleAverage α₀ (gcirc ω) r z - fieldCircleAverage α₀ (gcirc ω) r 0 := by
  let : IsProbabilityMeasure Q := gGFF.isProbabilityMeasure
  obtain ⟨D', hD', heq'⟩ :=
    gGFF.exists_localPairing_centeredCircle_decoder (α₀ := α₀) (ε := ε) hr
  have hX : Measurable (Section6.localPairingProc (ball 0 ε) gC) :=
    measurable_pi_iff.mpr fun φ => gGFF.measurable_pairing φ.1.1
      (Section6.isTestFunction_of_testC φ.1.1)
  have hDm : Measurable (fun p : Ξ × ℂ => D (Section6.localPairingProc (ball 0 ε) gC p.1) p.2) :=
    hD.comp ((hX.comp measurable_fst).prodMk measurable_snd)
  have hD'm : Measurable (fun p : Ξ × ℂ => D' (Section6.localPairingProc (ball 0 ε) gC p.1) p.2) :=
    hD'.comp ((hX.comp measurable_fst).prodMk measurable_snd)
  have hmeas : MeasurableSet {p : Ξ × ℂ |
      D (Section6.localPairingProc (ball 0 ε) gC p.1) p.2 =
        D' (Section6.localPairingProc (ball 0 ε) gC p.1) p.2} :=
    measurableSet_eq_fun hDm hD'm
  have hpoint : ∀ᵐ z ∂(volume.restrict E), ∀ᵐ ω ∂Q,
      D (Section6.localPairingProc (ball 0 ε) gC ω) z =
        D' (Section6.localPairingProc (ball 0 ε) gC ω) z := by
    filter_upwards [ae_restrict_mem hE] with z hz
    filter_upwards [heq z hz, heq'] with ω hω hω'
    exact hω.trans (hω' z (hbuffer z hz)).symm
  have hpair := (Measure.ae_ae_comm hmeas).2 hpoint
  filter_upwards [hpair, heq'] with ω hω hω'
  filter_upwards [hω, ae_restrict_mem hE] with z hz hzin
  exact hz.trans (hω' z (hbuffer z hzin))

/-- Almost-everywhere agreement of centered circle averages on the
reference set gives the same normalized approximation. -/
theorem normalizedRestriction_lqgApprox_eq_of_centered_ae (γ : ℝ)
    (hε : ℝ → ℂ → ℝ) {ε : ℝ} (hεpos : 0 < ε) (z₀ : ℂ)
    {U : Set ℂ} (hU : MeasurableSet U) (d : ℂ → ℝ)
    (hd : ∀ᵐ z ∂(volume.restrict U), d z = hε ε z - hε ε z₀) :
    normalizedRestriction (lqgApprox γ hε ε) U =
      normalizedRestriction (volume.withDensity fun z =>
        ENNReal.ofReal (Real.exp (γ * d z))) U := by
  rw [normalizedRestriction_lqgApprox_eq_centered γ hε hεpos z₀ U]
  apply normalizedRestriction_eq_of_restrict_eq_smul hU (c := 1) one_ne_zero ENNReal.one_ne_top
  rw [one_smul, centeredLQGApprox, restrict_withDensity hU, restrict_withDensity hU]
  apply withDensity_congr_ae
  filter_upwards [hd] with z hz
  rw [hz]

/-- The same measurable normalized approximation works for any two
whole-plane GFF realizations with the same logarithmic singularity. -/
theorem IsWholePlaneGFF.exists_common_normalizedLQGApprox
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} {γ α₀ ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {gC : Ξ → (ℂ → ℝ) → ℝ} {gcirc : Ξ → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (gGFF : IsWholePlaneGFF Q gC gcirc)
    (E : ℕ → Set ℂ) (hEm : ∀ n, MeasurableSet (E n))
    (hbuffer : ∀ n z, z ∈ E n → closedBall z (dyadicScale n) ⊆ ball 0 ε) :
    ∃ F : ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → Measure ℂ,
      (∀ n, Measurable (F n)) ∧
      (∀ᵐ ω ∂P, ∀ n, F n (Section6.localPairingProc (ball 0 ε) hC ω) =
        normalizedRestriction (lqgApprox γ (fieldCircleAverage α₀ (hcirc ω))
          (dyadicScale n)) (E n)) ∧
      ∀ᵐ ω ∂Q, ∀ n, F n (Section6.localPairingProc (ball 0 ε) gC ω) =
        normalizedRestriction (lqgApprox γ (fieldCircleAverage α₀ (gcirc ω))
          (dyadicScale n)) (E n) := by
  choose D hDm hDP hDQ using fun n =>
    hGFF.exists_common_centeredCircle_decoder (α₀ := α₀) (ε := ε) gGFF (dyadicScale_pos n)
  have hQ (n : ℕ) : ∀ᵐ ω ∂Q, ∀ᵐ z ∂(volume.restrict (E n)),
      D n (Section6.localPairingProc (ball 0 ε) gC ω) z =
        fieldCircleAverage α₀ (gcirc ω) (dyadicScale n) z -
          fieldCircleAverage α₀ (gcirc ω) (dyadicScale n) 0 :=
    gGFF.ae_ae_centeredCircle_decoder (dyadicScale_pos n) (E n) (hEm n)
      (hbuffer n) (D n) (hDm n) (fun z hz => hDQ n z (hbuffer n z hz))
  refine ⟨fun n x => normalizedRestriction
    (volume.withDensity fun z => ENNReal.ofReal (Real.exp (γ * D n x z))) (E n), ?_, ?_, ?_⟩
  · exact fun n => measurable_normalized_centeredLQGApprox γ (D n) (hDm n) (E n) (hEm n)
  · filter_upwards [ae_all_iff.mpr hDP] with ω hω n
    exact (normalizedRestriction_lqgApprox_eq_of_centered_on γ
      (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale_pos n) 0 (hEm n)
      (D n (Section6.localPairingProc (ball 0 ε) hC ω))
      (fun z hz => hω n z (hbuffer n z hz))).symm
  · filter_upwards [ae_all_iff.mpr hQ] with ω hω n
    exact (normalizedRestriction_lqgApprox_eq_of_centered_ae γ
      (fieldCircleAverage α₀ (gcirc ω)) (dyadicScale_pos n) 0 (hEm n)
      (D n (Section6.localPairingProc (ball 0 ε) gC ω)) (hω n)).symm

#print axioms IsWholePlaneGFF.ae_ae_centeredCircle_decoder
#print axioms normalizedRestriction_lqgApprox_eq_of_centered_ae
#print axioms IsWholePlaneGFF.exists_common_normalizedLQGApprox

end HarmonicBalls
