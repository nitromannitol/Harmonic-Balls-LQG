import HarmonicBalls.Proofs.Sec10.PrevalentPoleAvoidingCrossings
import HarmonicBalls.Proofs.Sec10.DoubleEndpointSelection

/-! # Near-pole crossing bounds at prevalent radii -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped ENNReal

universe u

/-- A prevalent good radius yields the crossing bound without pole separation. -/
theorem ae_eventually_pole_avoiding_crossings_at_good_radius
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h69 : OdometerHarmonicMeasureBoundStmt.{u})
    (h66 : ManyVeryGoodAnnuliStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc (2 * ε) (Real.sqrt ε),
        ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
          dist w 0 + (ρ + ρ / 50) < 1 →
          (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
            (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  obtain ⟨c, hc, h6⟩ := prevalent_displaced_crossing_events hI2 h69 h66
  intro γ hγ hγ2
  obtain ⟨α, hα, h6⟩ := h6 γ hγ hγ2
  let a : ℝ := min α (1 / 2)
  have ha : 0 < a := lt_min hα (by norm_num)
  have haα : a ≤ α := min_le_left _ _
  have ha1 : a < 1 := (min_le_right α (1 / 2)).trans_lt (by norm_num)
  refine ⟨a, ⟨ha, ha1⟩, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨E, hgood, hprev⟩ := h6 α₀ hα₀ Ω P hC hcirc μ hGFF hμ
  filter_upwards [ae_eventually_dyadic_three_good_radii hc hprev] with ω hgoodscale
  rw [eventually_atTop] at hgoodscale
  obtain ⟨N, hN⟩ := hgoodscale
  have hthreshold : 0 < min 1 (((2 : ℝ)⁻¹) ^ N) := by positivity
  filter_upwards [(eventually_lt_nhds hthreshold).filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hsmall hε
  change 0 < ε at hε
  have hε1 : ε < 1 := hsmall.trans_le (min_le_left _ _)
  have hεN : ε < ((2 : ℝ)⁻¹) ^ N := hsmall.trans_le (min_le_right _ _)
  obtain ⟨n, hnN, hnlo, hnhi⟩ := exists_late_dyadic_scale N hε hεN
  let δ : ℝ := ((2 : ℝ)⁻¹) ^ n
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ ≤ 2 * ε := hnhi.le
  have hsqrt : Real.sqrt δ ≤ (3 / 2 : ℝ) * Real.sqrt ε := by
    have hδsq := Real.sq_sqrt hδpos.le
    have hεsq := Real.sq_sqrt hε.le
    have hδnn := Real.sqrt_nonneg δ
    have hεnn := Real.sqrt_nonneg ε
    nlinarith
  have hεsqrt : ε ≤ Real.sqrt ε := by
    have hs := Real.sq_sqrt hε.le
    have hsn := Real.sqrt_nonneg ε
    nlinarith
  intro w hw
  have haw : 10 * Real.sqrt δ + δ ≤ dist w 0 := by
    have hw' : 20 * Real.sqrt ε ≤ dist w 0 := by
      simpa [mem_ball, not_lt] using hw.2
    linarith
  obtain ⟨x₀, hx₀, hnear⟩ := exists_prevalenceGrid_dist_lt hδpos hw.1 haw
  have hcount : 2 < {r : ℝ | r ∈ Icc δ (Real.sqrt δ) ∧
      (∃ k : ℕ, r = (8 : ℝ)⁻¹ ^ k) ∧ (δ ≤ r ∧ ω ∈ E r x₀)}.ncard := by
    convert hN n hnN x₀ hx₀ using 1
    congr 1
    ext r
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hr, hk, _, he⟩
      exact ⟨hr, hk, he⟩
    · rintro ⟨hr, hk, he⟩
      exact ⟨hr, hk, hr.1, he⟩
  obtain ⟨ρ, hρ, hδρ, hE⟩ := exists_good_radius_after_doubling_lower_endpoint hε hnlo hδε hcount
  have hρpos : 0 < ρ := by linarith [hρ.1]
  have hρlt : ρ < 1 := by
    have hs : Real.sqrt ε < 1 := by simpa using Real.sqrt_lt_sqrt hε.le hε1
    exact hρ.2.trans_lt hs
  have hnear50 : dist w x₀ < ρ / 50 := by linarith
  have hnear6 : dist w x₀ < ρ / 6 := by linarith
  refine ⟨ρ, hρ, ?_⟩
  intro z hz t ht hboundary
  have hdomain : closedBall x₀ ρ ⊆ ball (0 : ℂ) 1 := by
    intro y hy
    have hyx : dist y x₀ ≤ ρ := mem_closedBall.mp hy
    have hxw : dist x₀ w < ρ / 50 := by simpa [dist_comm] using hnear50
    have hyw : dist y w < ρ + ρ / 50 := by
      have := dist_triangle y x₀ w
      linarith
    apply mem_ball.mpr
    have := dist_triangle y w (0 : ℂ)
    linarith
  have hcount := hgood ω ρ ⟨hρpos, hρlt⟩ x₀ hE z hz t ht hdomain w hnear6
  exact hcount.trans (by exact_mod_cast Nat.ceil_mono (one_div_le_one_div_of_le ha haα))


end HarmonicBalls
