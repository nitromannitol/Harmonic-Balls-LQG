import HarmonicBalls.Proofs.Sec6.AnnulusBoundaryRegularity
import HarmonicBalls.Steps.Sec11.AnnulusComparison

/-! # Radial approximations of an annulus -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric MarkovProcess
open scoped Topology ENNReal NNReal

/-- The closure of a nondegenerate positive-radius annulus consists of the
points between its two boundary circles. -/
theorem closure_annulus_eq_radial_bounds (z : ℂ) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) :
    closure (annulus z r R) = {w : ℂ | r ≤ dist w z ∧ dist w z ≤ R} := by
  apply subset_antisymm (closure_annulus_subset_radial_bounds z r R)
  intro w hw
  rcases eq_or_lt_of_le hw.1 with hi | hi
  · apply HarmonicBalls.sphere_subset_closure_annulus z hr hrR
    simpa only [mem_sphere, dist_comm] using hi.symm
  rcases eq_or_lt_of_le hw.2 with ho | ho
  · have hb : w ∈ closure (ball z R) := by
      rw [closure_ball z (ne_of_gt (lt_trans hr hrR))]
      exact mem_closedBall.mpr ho.le
    have hc : w ∈ (closedBall z r)ᶜ := by
      simp only [mem_compl_iff, mem_closedBall, not_le]
      exact hi
    have hh := (isOpen_compl_iff.mpr isClosed_closedBall).closure_inter ⟨hb, hc⟩
    simpa only [annulus, Set.sdiff_eq] using hh
  · exact subset_closure (by
      simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
      exact ⟨ho, hi⟩)

/-- Positive shrinking margins exhaust the open annulus from inside. -/
theorem iUnion_annulus_shrink (z : ℂ) (r R : ℝ) {d : ℕ → ℝ}
    (hdpos : ∀ n, 0 < d n) (hd : Tendsto d atTop (𝓝 0)) :
    (⋃ n, annulus z (r + d n) (R - d n)) = annulus z r R := by
  ext w
  simp only [mem_iUnion, annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
  constructor
  · rintro ⟨n, hn₁, hn₂⟩
    exact ⟨by linarith [hdpos n], by linarith [hdpos n]⟩
  · rintro ⟨h₁, h₂⟩
    have he : 0 < min (R - dist w z) (dist w z - r) := lt_min (by linarith) (by linarith)
    obtain ⟨n, hn⟩ := (hd.eventually_lt_const he).exists
    exact ⟨n, by linarith [min_le_left (R - dist w z) (dist w z - r)],
      by linarith [min_le_right (R - dist w z) (dist w z - r)]⟩

/-- Positive shrinking margins approximate the annulus closure from outside. -/
theorem iInter_annulus_expand (z : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {d : ℕ → ℝ} (hdpos : ∀ n, 0 < d n) (hd : Tendsto d atTop (𝓝 0)) :
    (⋂ n, annulus z (r - d n) (R + d n)) = closure (annulus z r R) := by
  rw [closure_annulus_eq_radial_bounds z hr hrR]
  ext w
  simp only [mem_iInter, annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le, mem_ofPred_eq]
  constructor
  · intro h
    constructor
    · by_contra hn
      have he : 0 < r - dist w z := by linarith
      obtain ⟨n, hn'⟩ := (hd.eventually_lt_const he).exists
      have hh := (h n).2
      linarith
    · by_contra hn
      have he : 0 < dist w z - R := by linarith
      obtain ⟨n, hn'⟩ := (hd.eventually_lt_const he).exists
      have hh := (h n).1
      linarith
  · intro h n
    exact ⟨by linarith [hdpos n, h.2], by linarith [hdpos n, h.1]⟩

/-- Radial inner and outer approximations have vanishing core-return
probability for each fixed starting point in the annulus. -/
theorem tendsto_radial_annulus_core_return_probability
    {z x : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {d : ℕ → ℝ} (hdpos : ∀ n, 0 < d n) (hdanti : Antitone d)
    (hd : Tendsto d atTop (𝓝 0))
    {C : Set ℂ} (hC : IsClosed C) (hCA : C ⊆ annulus z r R)
    (hx : x ∈ annulus z r R) :
    Tendsto (fun n => planarBrownianMotion x {ω | ∃ t : ℝ≥0,
      ContinuousPath.exitTime (annulus z (r + d n) (R - d n)) ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (annulus z (r - d n) (R + d n)) ω ∧
      ω t ∈ C}) atTop (𝓝 0) := by
  apply tendsto_annulus_core_return_probability hr hrR
  · intro n; exact isOpen_ball.sdiff isClosed_closedBall
  · intro n m hnm w hw
    simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] at hw ⊢
    have hh := hdanti hnm
    constructor <;> linarith [hw.1, hw.2]
  · exact iUnion_annulus_shrink z r R hdpos hd
  · intro n; exact isOpen_ball.sdiff isClosed_closedBall
  · intro n m hnm w hw
    simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] at hw ⊢
    have hh := hdanti hnm
    constructor <;> linarith [hw.1, hw.2]
  · exact iInter_annulus_expand z hr hrR hdpos hd
  · exact hC
  · exact hCA
  · exact hx

/-- In particular, the margins may be chosen as `1 / (n + 1)`. -/
theorem tendsto_reciprocal_annulus_core_return_probability
    {z x : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {C : Set ℂ} (hC : IsClosed C) (hCA : C ⊆ annulus z r R)
    (hx : x ∈ annulus z r R) :
    Tendsto (fun n : ℕ => planarBrownianMotion x {ω | ∃ t : ℝ≥0,
      ContinuousPath.exitTime (annulus z (r + 1 / (n + 1 : ℝ)) (R - 1 / (n + 1 : ℝ))) ω ≤
        (t : ℝ≥0∞) ∧ (t : ℝ≥0∞) <
        ContinuousPath.exitTime (annulus z (r - 1 / (n + 1 : ℝ)) (R + 1 / (n + 1 : ℝ))) ω ∧
      ω t ∈ C}) atTop (𝓝 0) := by
  apply tendsto_radial_annulus_core_return_probability hr hrR (d := fun n => 1 / (n + 1 : ℝ))
  · intro n; positivity
  · intro n m hnm
    apply one_div_le_one_div_of_le (by positivity)
    simpa only [add_comm] using add_le_add_right (Nat.cast_le.mpr hnm : (n : ℝ) ≤ m) 1
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · exact hC
  · exact hCA
  · exact hx

end HarmonicBalls.Section6
