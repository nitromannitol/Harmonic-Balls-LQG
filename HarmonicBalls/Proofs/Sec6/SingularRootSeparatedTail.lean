import HarmonicBalls.Proofs.Sec6.SingularRootZeroAnnulusTail
import HarmonicBalls.Proofs.Sec6.SingularCollarGoodAnnulusCounts

/-! # Singular good-annulus tails away from the origin

The countable-centre iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

/-- A ring sufficiently small compared with its centre's distance from the
origin satisfies the separation needed for singular power-weight comparison. -/
theorem annulus_separated_of_six_mul_le_norm {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hz : 6 * r ≤ ‖z‖) :
    r / 100 ≤ infDist (0 : ℂ) (annulus z (3*r) (5*r)) := by
  have hne : (annulus z (3*r) (5*r)).Nonempty := by
    refine ⟨z + ((4*r : ℝ) : ℂ), ?_⟩
    simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
    have he : dist (z + ((4*r : ℝ) : ℂ)) z = 4*r := by
      simp [dist_eq_norm, hr.le]
    rw [he]
    constructor <;> linarith
  apply (le_infDist hne).2
  intro y hy
  have hy' : dist y z < 5*r := hy.1
  have ht := dist_triangle (0 : ℂ) y z
  have hz' : dist (0 : ℂ) z = ‖z‖ := by simp [dist_eq_norm]
  rw [hz'] at ht
  linarith

/-- At singular LQG roots at least `t` from the origin, singular good annuli
satisfy a polynomial lower-count tail whenever the window lies inside the
separation scale. The constant may depend on the physical scale. -/
theorem exists_singular_unitDisc_root_separated_goodAnnuli_polynomial_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    {b : ℝ} (hb : 0 < b) (q β : ℝ) (hq : 0 < q) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ, 0 < s → ∃ C : ℝ, 0 < C ∧
    ∀ ε t : ℝ, 0 < ε → ε ≤ 1 → 16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      6 * s * ε ^ (3 / 4 : ℝ) ≤ t →
      (P ⊗ₘ weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        {p | t ≤ ‖p.2‖ ∧
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus (μ p.1) (s * r) p.2
              (a / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) (b + 1)}.ncard : ℝ) <
          (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤ ENNReal.ofReal (C * ε ^ q) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  obtain ⟨a, ha, ht⟩ := exists_singular_unitDisc_root_zero_goodAnnuli_polynomial_tail
    hgrowth hγ hγ2 hα h hμ hμ₀ hb q β hq hβ
  refine ⟨a, ha, ?_⟩
  intro s hs
  obtain ⟨C, hC, htail⟩ := ht s hs
  refine ⟨C, hC, ?_⟩
  intro ε t hε hε1 hlog hsmall
  let κ := weightedRestrictionKernel P μ (h.aemeasurable_lqgMeasure hμ)
    (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const
  have hweight := (quasiMeasurePreserving_fst_compProd P κ).ae
    (ae_singular_lqg_eq_power_weight hgrowth hγ hγ2 hα h hμ hμ₀)
  apply (measure_mono_ae ?_).trans (htail ε hε hε1 hlog)
  filter_upwards [hweight] with p hp hw
  obtain ⟨hroot, hbad⟩ := hw
  have hfinite : {r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
      IsGoodAnnulus (μ p.1) (s * r) p.2
        (a / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) (b + 1)}.Finite := by
    apply finite_of_geometric (q := (7 : ℝ)⁻¹) (A := 1) (lo := ε)
      (by norm_num) (by norm_num) hε
    intro r hr
    obtain ⟨n, hn⟩ := hr.2.1
    exact ⟨hr.1.1, n, by simpa using hn⟩
  have hcount : ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
      IsGoodAnnulus (μ₀ p.1) (s * r) p.2 a (b + 1)}.ncard : ℝ) ≤
    ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
      IsGoodAnnulus (μ p.1) (s * r) p.2
        (a / ((1001 : ℝ) ^ |-(γ * α)|) ^ 2) (b + 1)}.ncard : ℝ) := by
    norm_cast
    apply Set.ncard_le_ncard ?_ hfinite
    intro r hr
    refine ⟨hr.1, hr.2.1, ?_⟩
    have hrpos : 0 < s*r := mul_pos hs (hε.trans_le hr.1.1)
    have hsep : 6 * (s*r) ≤ ‖p.2‖ := by
      calc
        _ ≤ 6 * s * ε ^ (3 / 4 : ℝ) := by nlinarith [hr.1.2]
        _ ≤ t := hsmall
        _ ≤ _ := hroot
    apply isGoodAnnulus_of_singular_weight hrpos
      (annulus_separated_of_six_mul_le_norm hrpos hsep) ?_ hr.2.2
    rw [hp]
  exact lt_of_le_of_lt hcount hbad

end HarmonicBalls.Section6
