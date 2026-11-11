import HarmonicBalls.Proofs.Sec8.LocalCirclePairingApproximation
import HarmonicBalls.Proofs.Sec8.JointCircleLawFromDecoder

/-! # Pairing convergence under dominated local field laws

The imported Section 8 development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Convergence in measure of measurable functions of an observation passes
to a finite measure whose observation law is absolutely continuous. -/
theorem tendstoInMeasure_of_dominated_observation
    {Ω Ξ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace E]
    (P : Measure Ω) (Q : Measure Ξ) [IsFiniteMeasure Q]
    (X : Ω → E) (Y : Ξ → E) (hX : Measurable X) (hY : Measurable Y)
    (hdom : Q.map Y ≪ P.map X) (f : ℕ → E → ℝ) (hf : ∀ n, Measurable (f n))
    (g : E → ℝ) (hg : Measurable g)
    (hlim : TendstoInMeasure P (fun n ω => f n (X ω)) atTop (fun ω => g (X ω))) :
    TendstoInMeasure Q (fun n ξ => f n (Y ξ)) atTop (fun ξ => g (Y ξ)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => ((hf n).comp hY).aestronglyMeasurable)).2
  intro ns hns
  obtain ⟨ns', hns', hae⟩ := (hlim.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ns', hns', ?_⟩
  have hset : MeasurableSet {x | Tendsto (fun i => f (ns (ns' i)) x) atTop (𝓝 (g x))} :=
    measurableSet_tendsto_fun (fun i => hf (ns (ns' i))) hg
  have hmap : ∀ᵐ x ∂P.map X, Tendsto (fun i => f (ns (ns' i)) x) atTop (𝓝 (g x)) :=
    (ae_map_iff hX.aemeasurable hset).2 hae
  exact ae_of_ae_map hY.aemeasurable (hdom.ae_le hmap)

/-- Under a dominated finite observation law, the local annular pairings
converge to the reference circle decoder. Convergence to another proposed
circle value is equivalent to almost-everywhere agreement with that decoder. -/
theorem IsWholePlaneGFF.exists_dominated_circle_pairing_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α₀ ε r : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hr : 0 < r) (z : ℂ)
    (hz : closedBall z r ⊆ ball 0 ε) :
    ∃ (φ : ℕ → Section6.LocalTest (ball 0 ε))
      (D : (Section6.LocalTest (ball 0 ε) → ℝ) → ℂ → ℝ),
      Measurable (Function.uncurry D) ∧
      (∀ᵐ ω ∂P, D (Section6.localPairingProc (ball 0 ε) hC ω) z =
        fieldCircleAverage α₀ (hcirc ω) r z - fieldCircleAverage α₀ (hcirc ω) r 0) ∧
      ∀ {Ξ : Type*} [MeasurableSpace Ξ] (Q : Measure Ξ) [IsFiniteMeasure Q]
        (Y : Ξ → (Section6.LocalTest (ball 0 ε) → ℝ)), Measurable Y →
        Q.map Y ≪ P.map (Section6.localPairingProc (ball 0 ε) hC) →
        ∀ g : Ξ → ℝ,
          TendstoInMeasure Q (fun j ξ => Y ξ (φ j)) atTop
            (fun ξ => g ξ + α₀ * (Real.circleAverage (fun v => Real.log ‖v‖) z r -
              Real.circleAverage (fun v => Real.log ‖v‖) 0 r)) ↔
          ∀ᵐ ξ ∂Q, D (Y ξ) z = g ξ := by
  obtain ⟨φ, hφ⟩ := hGFF.exists_localPairing_centeredCircle_approximation hr z hz
  obtain ⟨D, hDm, hDref⟩ := hGFF.exists_localPairing_centeredCircle_decoder
    (α₀ := α₀) (ε := ε) hr
  have hDrefz : ∀ᵐ ω ∂P, D (Section6.localPairingProc (ball 0 ε) hC ω) z =
      fieldCircleAverage α₀ (hcirc ω) r z - fieldCircleAverage α₀ (hcirc ω) r 0 :=
    hDref.mono fun _ h => h z hz
  refine ⟨φ, D, hDm, hDrefz, ?_⟩
  intro Ξ _ Q _ Y hY hdom g
  let X := Section6.localPairingProc (ball 0 ε) hC
  let c := α₀ * (Real.circleAverage (fun v => Real.log ‖v‖) z r -
    Real.circleAverage (fun v => Real.log ‖v‖) 0 r)
  let G := fun x => D x z + c
  have hX : Measurable X := measurable_pi_iff.mpr fun v =>
    hGFF.measurable_pairing v.1.1 (Section6.isTestFunction_of_testC v.1.1)
  have hG : Measurable G :=
    (hDm.comp (measurable_id.prodMk measurable_const)).add_const c
  have hreference : TendstoInMeasure P (fun j ω => X ω (φ j)) atTop (fun ω => G (X ω)) := by
    apply hφ.congr_right
    filter_upwards [hDrefz] with ω hω
    change _ = D (X ω) z + c
    rw [hω]
    simp only [fieldCircleAverage, c]
    ring
  have hroot : TendstoInMeasure Q (fun j ξ => Y ξ (φ j)) atTop (fun ξ => G (Y ξ)) :=
    tendstoInMeasure_of_dominated_observation P Q X Y hX hY hdom
      (fun j x => x (φ j)) (fun j => measurable_pi_apply (φ j)) G hG hreference
  constructor
  · intro hg
    filter_upwards [tendstoInMeasure_ae_unique hroot hg] with ξ hξ
    change D (Y ξ) z + c = g ξ + c at hξ
    exact add_right_cancel hξ
  · intro hg
    apply hroot.congr_right
    filter_upwards [hg] with ξ hξ
    change D (Y ξ) z + c = g ξ + c
    rw [hξ]

end HarmonicBalls
