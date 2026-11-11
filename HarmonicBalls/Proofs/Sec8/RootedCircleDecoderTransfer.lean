import HarmonicBalls.Proofs.Sec8.CommonCircleApproximation

/-! # Transfer of centered-circle decoders

The imported Section 8 development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. The joint observation-law
domination below is an explicit hypothesis, not a literature input.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Joint domination of the local observation and each centered circle
average transfers one decoder to a second law. -/
theorem IsWholePlaneGFF.exists_dominated_normalizedLQGApprox
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ξ} (Q : Measure Ω) [SFinite Q]
    {γ α₀ ε : ℝ} {hC : Ξ → (ℂ → ℝ) → ℝ} {hcirc : Ξ → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (Y : Ω → (Section6.LocalTest (ball 0 ε) → ℝ)) (hY : Measurable Y)
    (g : Ω → ℝ → ℂ → ℝ)
    (hg : ∀ n z, Measurable (fun ω => g ω (dyadicScale n) z))
    (hgcont : ∀ n, ∀ᵐ ω ∂Q, Continuous (g ω (dyadicScale n)))
    (E : ℕ → Set ℂ) (hEm : ∀ n, MeasurableSet (E n))
    (hbuffer : ∀ n z, z ∈ E n → closedBall z (dyadicScale n) ⊆ ball 0 ε)
    (hdom : ∀ n z, z ∈ E n →
      Q.map (fun ω => (Y ω, g ω (dyadicScale n) z - g ω (dyadicScale n) 0)) ≪
      P.map (fun ω => (Section6.localPairingProc (ball 0 ε) hC ω,
        fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z -
          fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) 0))) :
    ∃ F : ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → Measure ℂ,
      (∀ n, Measurable (F n)) ∧
      (∀ᵐ ω ∂P, ∀ n, F n (Section6.localPairingProc (ball 0 ε) hC ω) =
        normalizedRestriction (lqgApprox γ (fieldCircleAverage α₀ (hcirc ω))
          (dyadicScale n)) (E n)) ∧
      ∀ᵐ ω ∂Q, ∀ n, F n (Y ω) =
        normalizedRestriction (lqgApprox γ (g ω) (dyadicScale n)) (E n) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let X := Section6.localPairingProc (ball 0 ε) hC
  have hX : Measurable X := measurable_pi_iff.mpr fun φ =>
    hGFF.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)
  choose D hDm hDref using fun n : ℕ =>
    hGFF.exists_localPairing_centeredCircle_decoder (α₀ := α₀) (ε := ε) (dyadicScale_pos n)
  have hv (n : ℕ) : ∃ d : Ω → ℂ → ℝ,
      Measurable (Function.uncurry d) ∧ ∀ᵐ ω ∂Q, ∀ z,
        d ω z = g ω (dyadicScale n) z - g ω (dyadicScale n) 0 := by
    have hc : ∀ᵐ ω ∂Q, Continuous (fun z =>
        g ω (dyadicScale n) z - g ω (dyadicScale n) 0) := by
      filter_upwards [hgcont n] with ω hω
      exact hω.sub continuous_const
    obtain ⟨d, hdm, hdeq⟩ := exists_joint_local_version_of_pointwise
      (inferInstance : MeasurableSpace Ω) isOpen_univ
      (fun ω z => g ω (dyadicScale n) z - g ω (dyadicScale n) 0) hc
      (fun z _ => ⟨_, (hg n z).sub (hg n 0), Filter.Eventually.of_forall fun _ => rfl⟩)
    exact ⟨d, hdm, hdeq.mono fun _ h z => h z (mem_univ z)⟩
  choose d hdm hdeq using hv
  have hpoint (n : ℕ) (z : ℂ) (hz : z ∈ E n) : ∀ᵐ ω ∂Q,
      D n (Y ω) z = g ω (dyadicScale n) z - g ω (dyadicScale n) 0 := by
    let A : Set ((Section6.LocalTest (ball 0 ε) → ℝ) × ℝ) :=
      {p | D n p.1 z = p.2}
    have hA : MeasurableSet A := measurableSet_eq_fun
      ((hDm n).comp (measurable_fst.prodMk measurable_const)) measurable_snd
    have hR : Measurable (fun ω => (X ω,
        fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z -
          fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) 0)) := by
      apply hX.prodMk
      simp only [fieldCircleAverage]
      exact ((hGFF.measurable_circle _ _ (dyadicScale_pos n)).sub_const _).sub
        ((hGFF.measurable_circle _ _ (dyadicScale_pos n)).sub_const _)
    have hP : ∀ᵐ p ∂(P.map (fun ω => (X ω,
        fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z -
          fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) 0))), p ∈ A := by
      apply (ae_map_iff hR.aemeasurable hA).2
      filter_upwards [hDref n] with ω hω
      exact hω z (hbuffer n z hz)
    have hQ := (hdom n z hz).ae_le hP
    have hYz : Measurable (fun ω => (Y ω,
        g ω (dyadicScale n) z - g ω (dyadicScale n) 0)) :=
      hY.prodMk ((hg n z).sub (hg n 0))
    exact (ae_map_iff hYz.aemeasurable hA).1 hQ
  have hae (n : ℕ) : ∀ᵐ ω ∂Q, ∀ᵐ z ∂(volume.restrict (E n)),
      D n (Y ω) z = g ω (dyadicScale n) z - g ω (dyadicScale n) 0 := by
    have hm : MeasurableSet {p : Ω × ℂ | D n (Y p.1) p.2 = d n p.1 p.2} :=
      measurableSet_eq_fun ((hDm n).comp ((hY.comp measurable_fst).prodMk measurable_snd)) (hdm n)
    have hpair : ∀ᵐ ω ∂Q, ∀ᵐ z ∂(volume.restrict (E n)), D n (Y ω) z = d n ω z := by
      apply (Measure.ae_ae_comm hm).2
      filter_upwards [ae_restrict_mem (hEm n)] with z hz
      filter_upwards [hpoint n z hz, hdeq n] with ω hω hdω
      exact hω.trans (hdω z).symm
    filter_upwards [hpair, hdeq n] with ω hω hdω
    filter_upwards [hω] with z hz
    exact hz.trans (hdω z)
  refine ⟨fun n x => normalizedRestriction
    (volume.withDensity fun z => ENNReal.ofReal (Real.exp (γ * D n x z))) (E n), ?_, ?_, ?_⟩
  · exact fun n => measurable_normalized_centeredLQGApprox γ (D n) (hDm n) (E n) (hEm n)
  · filter_upwards [ae_all_iff.mpr hDref] with ω hω n
    exact (normalizedRestriction_lqgApprox_eq_of_centered_on γ
      (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale_pos n) 0 (hEm n)
      (D n (X ω)) (fun z hz => hω n z (hbuffer n z hz))).symm
  · filter_upwards [ae_all_iff.mpr hae] with ω hω n
    exact (normalizedRestriction_lqgApprox_eq_of_centered_ae γ (g ω)
      (dyadicScale_pos n) 0 (hEm n) (D n (Y ω)) (hω n)).symm

end HarmonicBalls
