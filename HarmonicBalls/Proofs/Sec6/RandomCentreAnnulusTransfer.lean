import HarmonicBalls.Proofs.Sec6.NearbyGoodAnnulusProbability
import HarmonicBalls.Proofs.Sec6.RootedGoodAnnulusContinuity

/-! # Good-annulus transfer at random centres

The imported LQG regularity development uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal Topology

/-- At random reference centres, good-annulus transfer failure has probability
converging to zero along any measurable sequence of perturbed centres that
converges almost surely. -/
theorem tendsto_randomCentre_goodAnnulus_transfer_failure
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure (Ω × ℂ)) [IsFiniteMeasure Q]
    (μ : Ω → Measure ℂ) (hμ : Measurable μ)
    (hloc : ∀ ω, IsLocallyFiniteMeasure (μ ω))
    {r a a' b b' : ℝ} (hr : 0 < r)
    (ha' : 0 < a') (ha : a' < a) (hb : 0 ≤ b) (hbb : b < b')
    (hreg : ∀ᵐ p ∂Q, μ p.1 (sphere p.2 (3*r)) = 0 ∧
      μ p.1 (sphere p.2 (5*r)) = 0 ∧ 0 < μ p.1 (annulus p.2 (3*r) (5*r)))
    (w : ℕ → Ω × ℂ → ℂ) (hwmeas : ∀ n, Measurable (w n))
    (hw : ∀ᵐ p ∂Q, Tendsto (fun n => w n p) atTop (𝓝 p.2)) :
    Tendsto (fun n => Q {p | IsGoodAnnulus (μ p.1) r p.2 a b ∧
      ¬ IsGoodAnnulus (μ p.1) r (w n p) a' b'}) atTop (𝓝 0) := by
  let E : ℕ → Set (Ω × ℂ) := fun n => {p | IsGoodAnnulus (μ p.1) r p.2 a b ∧
    ¬ IsGoodAnnulus (μ p.1) r (w n p) a' b'}
  have hE (n : ℕ) : MeasurableSet (E n) := by
    have h1 := measurableSet_isGoodAnnulus_joint (hμ.comp measurable_fst)
      (fun p => hloc p.1) measurable_snd measurable_const (fun _ => hr) (ha'.trans ha) b
    have h2 := measurableSet_isGoodAnnulus_joint (hμ.comp measurable_fst)
      (fun p => hloc p.1) (hwmeas n) measurable_const (fun _ => hr) ha' b'
    exact h1.inter h2.compl
  have hlim : ∀ᵐ p ∂Q, ∀ᶠ n in atTop, p ∈ E n ↔ p ∈ (∅ : Set (Ω × ℂ)) := by
    filter_upwards [hreg, hw] with p ⟨h3, h5, hp⟩ hw
    by_cases hg : IsGoodAnnulus (μ p.1) r p.2 a b
    · let : IsLocallyFiniteMeasure (μ p.1) := hloc p.1
      have hf : μ p.1 (annulus p.2 (3*r) (5*r)) ≠ ∞ :=
        ne_top_of_le_ne_top measure_ball_ne_top (measure_mono sdiff_subset)
      obtain ⟨δ, hδ, hnear⟩ := exists_nearby_goodAnnulus (μ p.1) p.2 hr h3 h5 hp hf
        ha'.le ha hb hbb hg
      filter_upwards [(Metric.tendsto_nhds.mp hw) δ hδ] with n hn
      simp only [E, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
      exact fun _ => hnear (w n p) hn
    · exact Eventually.of_forall fun n => by simp [E, hg]
  simpa only [measure_empty] using
    tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop MeasurableSet.empty hE hlim

end HarmonicBalls.Section6
