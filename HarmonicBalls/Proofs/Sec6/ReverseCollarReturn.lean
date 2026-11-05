import HarmonicBalls.Proofs.Sec6.UniformCollarReturn

/-! # Reverse nearby-annulus collar comparison -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric MarkovProcess
open scoped ENNReal NNReal Topology

/-- Uniformly in the nearby centre and starting point, the probability of
exiting the fixed annulus and returning to its interior core before exiting
the nearby annulus tends to zero with the displacement. -/
theorem exists_uniform_nearby_annulus_reverse_core_return
    {z : ℂ} {r R s S : ℝ} (hr : 0 < r) (hrR : r < R)
    (hrs : r < s) (hSR : S < R) {K : Set ℂ} (hK : IsCompact K)
    (hKA : K ⊆ annulus z r R) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z < δ → ∀ y ∈ K,
      planarBrownianMotion y {ω | ∃ t : ℝ≥0,
        ContinuousPath.exitTime (annulus z r R) ω ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < ContinuousPath.exitTime (annulus w r R) ω ∧
        s ≤ dist (ω t) z ∧ dist (ω t) z ≤ S} < ε := by
  let d : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hdpos (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  have hdanti : Antitone d := by
    intro n m hnm
    dsimp [d]
    apply one_div_le_one_div_of_le (by positivity)
    simpa only [add_comm] using add_le_add_right (Nat.cast_le.mpr hnm : (n : ℝ) ≤ m) 1
  have hd : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨n, hn⟩ := (eventually_uniform_radial_core_return hr hrR hrs hSR
    hdpos hdanti hd hK hKA hε).exists
  refine ⟨d n, hdpos n, ?_⟩
  intro w hw y hy
  have hinner := (annulus_nearby_center_sandwich (r := r) (R := R)
    (show dist z z < d n by simpa using hdpos n)).1
  have houter := (annulus_nearby_center_sandwich (r := r) (R := R) hw).2
  apply lt_of_le_of_lt ?_ (hn y hy)
  apply measure_mono
  rintro ω ⟨t, htB, htA, htC⟩
  exact ⟨t, (ContinuousPath.exitTime_mono hinner ω).trans htB,
    htA.trans_le (ContinuousPath.exitTime_mono houter ω), htC⟩

/-- Uniform reverse avoidance comparison for any witness, with the collar
extended in the nearby annulus. -/
theorem exists_uniform_reverse_nearby_annulus_avoidance_comparison
    {z : ℂ} {r R s S : ℝ} (hr : 0 < r) (hrR : r < R)
    (hrs : r < s) (hSR : S < R) {K : Set ℂ} (hK : IsCompact K)
    (hKA : K ⊆ annulus z r R) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z < δ → ∀ y ∈ K, ∀ Y : Set ℂ,
      planarBrownianMotion y {ω | ContinuousPath.exitTime (annulus z r R) ω ≤
        ContinuousPath.exitTime Y ω} ≤
      planarBrownianMotion y {ω | ContinuousPath.exitTime (annulus w r R) ω ≤
        ContinuousPath.exitTime ((annulus w r R ∩ Y) ∪
          (annulus w r R \ {q | s ≤ dist q z ∧ dist q z ≤ S})) ω} + ε := by
  obtain ⟨δ, hδ, hret⟩ :=
    exists_uniform_nearby_annulus_reverse_core_return hr hrR hrs hSR hK hKA hε
  refine ⟨δ, hδ, ?_⟩
  intro w hw y hy Y
  apply (stay_probability_le_collar_avoidance_add_return (planarBrownianMotion y)
    (annulus w r R) (annulus z r R) {q | s ≤ dist q z ∧ dist q z ≤ S} Y).trans
  apply add_le_add le_rfl
  simpa only [mem_ofPred_eq] using (hret w hw y hy).le

end HarmonicBalls.Section6
