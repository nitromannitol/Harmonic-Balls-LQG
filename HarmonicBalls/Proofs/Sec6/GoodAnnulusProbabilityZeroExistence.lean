import HarmonicBalls.Proofs.Sec6.CompactPhaseProbability
import HarmonicBalls.Proofs.Sec6.SimultaneousPrevalenceZeroExistence
import HarmonicBalls.Proofs.Sec6.GoodAnnulusReduction

/-! # Good-annulus probability from zero-strength existence

The annulus iteration imported above uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. Zero-strength LQG
existence is a staged input pending source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

universe u

/-- The zero-singularity probability bound and existence at zero imply the
full bound. The singularity weight is derived from the limits themselves. -/
theorem goodAnnulusProbabilityStmt_of_zero_and_zero_existence
    (hzero : ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ b ∈ Ioo (0 : ℝ) 1, ∀ p ∈ Ioo (0 : ℝ) 1, ∃ a ∈ Ioo (0 : ℝ) 1,
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      ∀ r : ℝ, 0 < r → ∀ z : ℂ, r / 100 ≤ infDist (0 : ℂ) (annulus z (3 * r) (5 * r)) →
        P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} ≤ ENNReal.ofReal (1 - p))
    (hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc) : GoodAnnulusProbabilityStmt.{u} := by
  intro γ α hγ hγ2 hα b hb p hp
  obtain ⟨a, ha, hgood⟩ := hzero γ hγ hγ2 b hb p hp
  let t : ℝ := (1001 : ℝ) ^ |-(γ * α)|
  have ht : 1 ≤ t := Real.one_le_rpow (by norm_num) (abs_nonneg _)
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  refine ⟨a / t ^ 2, ⟨div_pos ha.1 (sq_pos_of_pos htpos), ?_⟩, ?_⟩
  · rw [div_lt_one (sq_pos_of_pos htpos)]
    nlinarith [ha.2]
  intro Ω _ P hC hcirc μ hG hμ r hr z hd
  obtain ⟨μ₀, hμ₀, hrepr⟩ :=
    exists_ae_singular_limits_restrict_eq_weight_of_zero_existence P γ hγ hγ2 hC hcirc
      hG (hE0 Ω P γ hC hcirc)
  have hweight : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((μ₀ ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ := by
    filter_upwards [hrepr, hμ] with ω hw hm
    exact hw α (μ ω) hm
  exact (badGoodAnnulus_measure_le_of_singular_weight P hr hd hweight).trans
    (hgood Ω P hC hcirc μ₀ hG hμ₀ r hr z hd)

/-- A phase-uniform bound at the origin controls every positive radius and
centre. This isolates the remaining scale-uniform probability estimate. -/
theorem goodAnnulus_zero_probability_of_dyadic_phase
    (hphase : ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ b ∈ Ioo (0 : ℝ) 1,
      ∀ p ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω]
        (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc →
        IsLQGMeasureOfField P γ 0 hcirc μ →
        ∃ a ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Ioc (1 / 2 : ℝ) 1,
          P {ω | ¬ IsGoodAnnulus (μ ω) s 0 a b} ≤ ENNReal.ofReal (1 - p)) :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ b ∈ Ioo (0 : ℝ) 1, ∀ p ∈ Ioo (0 : ℝ) 1, ∃ a ∈ Ioo (0 : ℝ) 1,
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      ∀ r : ℝ, 0 < r → ∀ z : ℂ, r / 100 ≤ infDist (0 : ℂ) (annulus z (3 * r) (5 * r)) →
        P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} ≤ ENNReal.ofReal (1 - p) := by
  intro γ hγ hγ2 b hb p hp
  classical
  by_cases hex : ∃ (Ω : Type u) (m : MeasurableSpace Ω), letI := m
      ∃ (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc ∧
          IsLQGMeasureOfField P γ 0 hcirc μ
  · obtain ⟨Ω₀, m₀, P₀, hC₀, hcirc₀, μ₀, h₀, hμ₀⟩ := hex
    let : MeasurableSpace Ω₀ := m₀
    obtain ⟨a, ha, hbound⟩ := hphase γ hγ hγ2 b hb p hp Ω₀ P₀ hC₀ hcirc₀ μ₀ h₀ hμ₀
    refine ⟨a, ha, ?_⟩
    intro Ω _ P hC hcirc μ h hμ r hr z hd
    have hevent : ∀ᶠ n : ℕ in atTop, dyadicScale n < r⁻¹ :=
      (tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
        (Iio_mem_nhds (inv_pos.mpr hr))
    obtain ⟨n, hn⟩ := hevent.exists
    have hs : 0 < r * dyadicScale n := mul_pos hr (dyadicScale_pos n)
    have hs1 : r * dyadicScale n ≤ 1 := by
      have hmul := mul_lt_mul_of_pos_left hn hr
      rw [mul_inv_cancel₀ hr.ne'] at hmul
      exact hmul.le
    obtain ⟨s, hsmem, heq⟩ := exists_dyadic_phase_goodAnnulus_probability hγ h₀ hμ₀ hs hs1 ha.1 b
    rw [goodAnnulus_failure_probability_eq_reference h₀ hμ₀ h hμ hr ha.1 z]
    rw [← badGoodAnnulus_probability_eq_dyadic_orbit hγ h₀ hμ₀ hr n ha.1 b, heq]
    exact hbound s hsmem
  · refine ⟨1 / 2, by norm_num, ?_⟩
    intro Ω m P hC hcirc μ h hμ r hr z hd
    exact False.elim (hex ⟨Ω, m, P, hC, hcirc, μ, h, hμ⟩)


/-- Lemma 6.4 follows from the phase-uniform zero-strength estimate and
staged zero-strength existence, without an additional Weyl-scaling input. -/
theorem goodAnnulusProbabilityStmt_of_dyadic_phase_and_zero_existence
    (hphase : ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ b ∈ Ioo (0 : ℝ) 1,
      ∀ p ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω]
        (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc →
        IsLQGMeasureOfField P γ 0 hcirc μ →
        ∃ a ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Ioc (1 / 2 : ℝ) 1,
          P {ω | ¬ IsGoodAnnulus (μ ω) s 0 a b} ≤ ENNReal.ofReal (1 - p))
    (hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc) : GoodAnnulusProbabilityStmt.{u} :=
  goodAnnulusProbabilityStmt_of_zero_and_zero_existence
    (goodAnnulus_zero_probability_of_dyadic_phase hphase) hE0

end HarmonicBalls.Section6
