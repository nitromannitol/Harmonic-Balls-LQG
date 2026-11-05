import HarmonicBalls.Proofs.Sec6.GoodAnnulusPhaseProbability
import HarmonicBalls.Proofs.Sec6.CompactPhaseProbability

/-! # Uniform good-annulus probability

The imported annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- A single threshold controls the good-annulus failure probability at all
positive radii and deterministic centres of every whole-plane realization. -/
theorem exists_universal_goodAnnulus_probability_all_radii
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {b p : ℝ} (hb : 0 < b) (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      ∀ r : ℝ, 0 < r → ∀ z : ℂ,
      P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} ≤ ENNReal.ofReal (1 - p) := by
  obtain ⟨a, ha, hphase⟩ :=
    uniform_goodAnnulus_probability_of_volumeGrowth hgrowth hγ hγ₂ h₀ hμ₀ hb hp
  refine ⟨a, ha, ?_⟩
  have hsmall : ∀ r : ℝ, 0 < r → r ≤ 1 →
      P₀ {ω | ¬ IsGoodAnnulus (μ₀ ω) r 0 a b} ≤ ENNReal.ofReal (1 - p) := by
    intro r hr hr1
    obtain ⟨s, hs, heq⟩ := exists_dyadic_phase_goodAnnulus_probability hγ h₀ hμ₀ hr hr1 ha.1 b
    rw [heq]
    exact hphase s ⟨hs.1.le, hs.2⟩
  intro Ω _ P hC hcirc μ hgff hμ r hr z
  rw [goodAnnulus_failure_probability_eq_reference h₀ hμ₀ hgff hμ hr ha.1 z]
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have hnpow : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast Nat.le_of_lt n.lt_two_pow_self
  have hn' : r ≤ (2 : ℝ) ^ n := hn.le.trans hnpow
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have heq : r * dyadicScale n = r / (2 : ℝ) ^ n := by
    simp [dyadicScale, inv_pow, div_eq_mul_inv]
  have hpos : 0 < r * dyadicScale n := mul_pos hr (dyadicScale_pos n)
  have hle : r * dyadicScale n ≤ 1 := by rw [heq]; exact (div_le_one hpow).2 hn'
  rw [← badGoodAnnulus_probability_eq_dyadic_orbit hγ h₀ hμ₀ hr n ha.1 b]
  exact hsmall _ hpos hle

end HarmonicBalls.Section6
