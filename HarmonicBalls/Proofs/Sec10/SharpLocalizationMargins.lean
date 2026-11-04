import HarmonicBalls.Proofs.Sec10.ExactRadiusSelection

/-!
# Smaller localization margins for crossing bounds

The Harnack estimate only requires the selected test ball to stay in the
unit disk and avoid the pole. Its center is within `ρ / 50` of the crossing
center, so a margin of `ρ + ρ / 50` suffices.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6

universe u

/-- The exact-radius crossing bound holds if the smaller Harnack ball, rather
than the double-radius crossing ball, is separated from the boundary and pole. -/
theorem ae_eventually_crossings_with_sharp_margins
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε),
        ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
          dist w 0 + (ρ + ρ / 50) < 1 → ρ + ρ / 50 < dist z w →
          (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
            (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  obtain ⟨c, hc, h6⟩ := h6
  intro γ hγ hγ2
  obtain ⟨α, hα, h6⟩ := h6 γ hγ hγ2
  let a : ℝ := min α (1 / 2)
  have ha : 0 < a := lt_min hα (by norm_num)
  have haα : a ≤ α := min_le_left _ _
  have ha1 : a < 1 := (min_le_right α (1 / 2)).trans_lt (by norm_num)
  refine ⟨a, ⟨ha, ha1⟩, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨E, hgood, hprev⟩ := h6 α₀ hα₀ Ω P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα₀ hGFF hμ
  filter_upwards [ae_eventually_dyadic_two_good_radii hc hprev, hV,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hgoodscale hV hopen
  let : IsLocallyFiniteMeasure (μ ω) := hV.1
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
  have hcount : 1 < {r : ℝ | r ∈ Icc δ (Real.sqrt δ) ∧
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
  obtain ⟨ρ, hρ, hδρ, hE⟩ := exists_exact_good_radius hε hnlo hδε hcount
  have hρpos : 0 < ρ := hε.trans_le hρ.1
  have hρlt : ρ < 1 := by
    have hs : Real.sqrt ε < 1 := by simpa using Real.sqrt_lt_sqrt hε.le hε1
    exact hρ.2.trans_lt hs
  have hnear50 : dist w x₀ < ρ / 50 := by linarith
  have hnear6 : dist w x₀ < ρ / 6 := by linarith
  refine ⟨ρ, hρ, ?_⟩
  intro z hz t ht hboundary hpole
  have hdomain : closedBall x₀ ρ ⊆ ball (0 : ℂ) 1 \ {z} := by
    intro y hy
    have hyx : dist y x₀ ≤ ρ := mem_closedBall.mp hy
    have hxw : dist x₀ w < ρ / 50 := by simpa [dist_comm] using hnear50
    have hyw : dist y w < ρ + ρ / 50 := by
      have := dist_triangle y x₀ w
      linarith
    refine ⟨mem_ball.mpr ?_, ?_⟩
    · have := dist_triangle y w (0 : ℂ)
      linarith
    · intro hyz
      have : y = z := mem_singleton_iff.mp hyz
      subst y
      linarith
  have hcount := encard_crossingComponents_of_nearby_harnack (μ ω) (cluster (μ ω) 1 z t)
    (hopen t 1 ht zero_lt_one z hz).1 hα w x₀ hρpos hnear6
    (ne_top_of_le_ne_top (measure_ball_lt_top (μ := μ ω)).ne (measure_mono sdiff_subset))
    (hgood ω ρ ⟨hρpos, hρlt⟩ x₀ hE z hz t ht hdomain)
  exact hcount.trans (by exact_mod_cast Nat.ceil_mono (one_div_le_one_div_of_le ha haα))

end HarmonicBalls
