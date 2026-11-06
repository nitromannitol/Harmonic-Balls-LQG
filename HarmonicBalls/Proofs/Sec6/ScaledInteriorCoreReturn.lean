import HarmonicBalls.Proofs.Sec6.ScaledAnnularReturn

/-! # Uniform annular return for arbitrary interior cores

The interior core may approach the annulus boundary. Its distance from the
boundary is fixed before selecting the displacement bound.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set MarkovProcess Filter
open scoped ENNReal NNReal Pointwise Topology

/-- A single relative collar width controls Brownian return probabilities on
all positive scales. The width depends on the core and prescribed error; the
starting point ranges over the scaled middle circle. -/
theorem exists_scale_uniform_radial_core_return_of_interior
    {s S : ℝ} (hs : 3 < s) (hS : S < 5)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ k : ℝ, 0 < k → ∀ x ∈ sphere (0 : ℂ) 4,
      planarBrownianMotion (k • x) {ω | ∃ t : ℝ≥0,
        ContinuousPath.exitTime (annulus 0 (k * (3 + η)) (k * (5 - η))) ω ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < ContinuousPath.exitTime (annulus 0 (k * (3 - η)) (k * (5 + η))) ω ∧
        k * s ≤ dist (ω t) 0 ∧ dist (ω t) 0 ≤ k * S} < ε := by
  let d : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hdpos (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have hdanti : Antitone d := by
    intro n m hnm
    dsimp [d]
    apply one_div_le_one_div_of_le (by positivity)
    simpa only [add_comm] using add_le_add_right (Nat.cast_le.mpr hnm : (n : ℝ) ≤ m) 1
  have hd : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hu := eventually_uniform_circle_radial_core_return (z := (0 : ℂ))
    (r := 3) (R := 5) (s := s) (S := S) (ρ := 4)
    (by norm_num) (by norm_num) (by norm_num) hs hS
    hdpos hdanti hd hε
  obtain ⟨n, hn⟩ := hu.exists
  refine ⟨d n, hdpos n, ?_⟩
  intro k hk x hx
  have h := planarBrownian_radial_core_return_dilation hk x 0
    (3 - d n) (5 + d n) (3 + d n) (5 - d n) s S
  simpa only [smul_zero] using h.trans_lt (hn x hx)

/-- The same relative width works at every centre and every positive scale. -/
theorem exists_scale_and_centre_uniform_radial_core_return_of_interior
    {s S : ℝ} (hs : 3 < s) (hS : S < 5)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ k : ℝ, 0 < k → ∀ z : ℂ, ∀ x ∈ sphere (0 : ℂ) 4,
      planarBrownianMotion (k • x + z) {ω | ∃ t : ℝ≥0,
        ContinuousPath.exitTime (annulus z (k * (3 + η)) (k * (5 - η))) ω ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < ContinuousPath.exitTime (annulus z (k * (3 - η)) (k * (5 + η))) ω ∧
        k * s ≤ dist (ω t) z ∧ dist (ω t) z ≤ k * S} < ε := by
  obtain ⟨η, hη, hbound⟩ := exists_scale_uniform_radial_core_return_of_interior hs hS hε
  refine ⟨η, hη, ?_⟩
  intro k hk z x hx
  have hAnn (a b : ℝ) : (fun y : ℂ => y + z) '' annulus 0 a b = annulus z a b := by
    ext y
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [annulus, dist_eq_norm] using hy
    · intro hy
      refine ⟨y - z, ?_, sub_add_cancel y z⟩
      simpa [annulus, dist_eq_norm] using hy
  have hCore (a b : ℝ) : (fun y : ℂ => y + z) ''
      {y | a ≤ dist y 0 ∧ dist y 0 ≤ b} =
      {y | a ≤ dist y z ∧ dist y z ≤ b} := by
    ext y
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [dist_eq_norm] using hy
    · intro hy
      refine ⟨y - z, ?_, sub_add_cancel y z⟩
      simpa [dist_eq_norm] using hy
  have h := planarBrownian_core_return_add (k • x) z
    (annulus 0 (k * (3 - η)) (k * (5 + η)))
    (annulus 0 (k * (3 + η)) (k * (5 - η)))
    {y | k * s ≤ dist y 0 ∧ dist y 0 ≤ k * S}
  rw [hAnn, hAnn, hCore] at h
  simpa only [mem_ofPred_eq] using h.trans_lt (hbound k hk x hx)


end HarmonicBalls.Section6
