import HarmonicBalls.Proofs.Sec6.AnnulusRadialApproximation
import HarmonicBalls.Proofs.Sec6.CollarAvoidanceComparison

/-! # Uniform collar-return probabilities -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric MarkovProcess
open scoped Topology ENNReal NNReal

/-- A fixed-start collar-return estimate extends to a neighborhood of the
starting point, uniformly for sufficiently thin radial collars. -/
theorem locally_uniform_radial_core_return
    {z x : ℂ} {r R s S : ℝ} (hr : 0 < r) (hrR : r < R) (hrs : r < s) (hSR : S < R)
    {d : ℕ → ℝ} (hdpos : ∀ n, 0 < d n) (hdanti : Antitone d)
    (hd : Tendsto d atTop (𝓝 0)) (hx : x ∈ annulus z r R)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℂ, dist y x < δ → ∀ m ≥ N,
      planarBrownianMotion y {ω | ∃ t : ℝ≥0,
        ContinuousPath.exitTime (annulus z (r + d m) (R - d m)) ω ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < ContinuousPath.exitTime (annulus z (r - d m) (R + d m)) ω ∧
        s ≤ dist (ω t) z ∧ dist (ω t) z ≤ S} < ε := by
  let η : ℝ := min (s - r) (R - S) / 2
  have hη : 0 < η := by dsimp [η]; positivity
  let C : Set ℂ := {w | s - η ≤ dist w z ∧ dist w z ≤ S + η}
  have hC : IsClosed C :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le (continuous_id.dist continuous_const) continuous_const)
  have hCA : C ⊆ annulus z r R := by
    intro w hw
    simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
    dsimp [C] at hw
    have hη₁ : η ≤ (s - r) / 2 := by dsimp [η]; linarith [min_le_left (s - r) (R - S)]
    have hη₂ : η ≤ (R - S) / 2 := by dsimp [η]; linarith [min_le_right (s - r) (R - S)]
    constructor <;> linarith [hw.1, hw.2]
  have hp := tendsto_radial_annulus_core_return_probability hr hrR hdpos hdanti hd hC hCA hx
  have hevent := (hp.eventually (Iio_mem_nhds hε)).and (hd.eventually_lt_const hη)
  obtain ⟨n, hn, hnη⟩ := hevent.exists
  let δ : ℝ := d n / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith [hdpos n]
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hd.eventually_lt_const hδ)
  refine ⟨N, δ, hδ, ?_⟩
  intro y hy m hm
  have hmδ : d m < δ := hN m hm
  have hv : ‖y - x‖ < δ := by simpa [dist_eq_norm] using hy
  have hcomp := planarBrownian_annular_core_return_le_of_translation x z (y - x)
    (r - d m) (R + d m) (r + d m) (R - d m) s S δ hv
  rw [add_sub_cancel] at hcomp
  apply lt_of_le_of_lt (hcomp.trans ?_) hn
  apply measure_mono
  rintro ω ⟨t, htD, htA, hts, htS⟩
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · apply (ContinuousPath.exitTime_mono ?_ ω).trans htD
    intro w hw
    simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] at hw ⊢
    dsimp [δ] at *
    constructor <;> linarith [hw.1, hw.2]
  · apply htA.trans_le (ContinuousPath.exitTime_mono ?_ ω)
    intro w hw
    simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] at hw ⊢
    dsimp [δ] at *
    constructor <;> linarith [hw.1, hw.2]
  · dsimp [C, δ] at *; linarith
  · dsimp [C, δ] at *; linarith

/-- Collar-return probabilities converge uniformly over every compact set of
starting points contained in the annulus. -/
theorem eventually_uniform_radial_core_return
    {z : ℂ} {r R s S : ℝ} (hr : 0 < r) (hrR : r < R)
    (hrs : r < s) (hSR : S < R)
    {d : ℕ → ℝ} (hdpos : ∀ n, 0 < d n) (hdanti : Antitone d)
    (hd : Tendsto d atTop (𝓝 0)) {K : Set ℂ} (hK : IsCompact K)
    (hKA : K ⊆ annulus z r R) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ y ∈ K,
      planarBrownianMotion y {ω | ∃ t : ℝ≥0,
        ContinuousPath.exitTime (annulus z (r + d m) (R - d m)) ω ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < ContinuousPath.exitTime (annulus z (r - d m) (R + d m)) ω ∧
        s ≤ dist (ω t) z ∧ dist (ω t) z ≤ S} < ε := by
  let P : ℕ → ℂ → Prop := fun m y =>
    planarBrownianMotion y {ω | ∃ t : ℝ≥0,
      ContinuousPath.exitTime (annulus z (r + d m) (R - d m)) ω ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < ContinuousPath.exitTime (annulus z (r - d m) (R + d m)) ω ∧
      s ≤ dist (ω t) z ∧ dist (ω t) z ≤ S} < ε
  let U : ℕ → Set ℂ := fun n => interior {y | ∀ m ≥ n, P m y}
  have hcover : K ⊆ ⋃ n, U n := by
    intro x hx
    obtain ⟨N, δ, hδ, hlocal⟩ :=
      locally_uniform_radial_core_return hr hrR hrs hSR hdpos hdanti hd (hKA hx) hε
    apply mem_iUnion.mpr
    refine ⟨N, mem_interior_iff_mem_nhds.mpr ?_⟩
    apply mem_of_superset (ball_mem_nhds x hδ)
    intro y hy m hm
    exact hlocal y (by simpa only [mem_ball] using hy) m hm
  have hmono : Monotone U := by
    intro n m hnm
    apply interior_mono
    intro y hy k hmk
    exact hy k (hnm.trans hmk)
  obtain ⟨N, hN⟩ := hK.elim_directed_cover U (fun _ => isOpen_interior) hcover
    (directed_of_isDirected_le hmono)
  filter_upwards [eventually_ge_atTop N] with m hm y hy
  have h := interior_subset (hN hy)
  exact h m hm

/-- The compact starting set can in particular be a circle inside the annulus. -/
theorem eventually_uniform_circle_radial_core_return
    {z : ℂ} {r R s S ρ : ℝ} (hr : 0 < r) (hrρ : r < ρ) (hρR : ρ < R)
    (hrs : r < s) (hSR : S < R)
    {d : ℕ → ℝ} (hdpos : ∀ n, 0 < d n) (hdanti : Antitone d)
    (hd : Tendsto d atTop (𝓝 0)) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ y ∈ sphere z ρ,
      planarBrownianMotion y {ω | ∃ t : ℝ≥0,
        ContinuousPath.exitTime (annulus z (r + d m) (R - d m)) ω ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < ContinuousPath.exitTime (annulus z (r - d m) (R + d m)) ω ∧
        s ≤ dist (ω t) z ∧ dist (ω t) z ≤ S} < ε := by
  apply eventually_uniform_radial_core_return hr (hrρ.trans hρR) hrs hSR hdpos hdanti hd
    (isCompact_sphere z ρ) ?_ hε
  intro y hy
  simp only [mem_sphere] at hy
  simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
  rw [hy]
  exact ⟨hρR, hrρ⟩

/-- Return probabilities after exiting a nearby annulus are uniformly small
for compact sets of starting points and a fixed closed interior core. -/
theorem exists_uniform_nearby_annulus_core_return
    {z : ℂ} {r R s S : ℝ} (hr : 0 < r) (hrR : r < R)
    (hrs : r < s) (hSR : S < R) {K : Set ℂ} (hK : IsCompact K)
    (hKA : K ⊆ annulus z r R) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z < δ → ∀ y ∈ K,
      planarBrownianMotion y {ω | ∃ t : ℝ≥0,
        ContinuousPath.exitTime (annulus w r R) ω ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < ContinuousPath.exitTime (annulus z r R) ω ∧
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
  have hinner := (annulus_nearby_center_sandwich (r := r) (R := R) hw).1
  have houter := (annulus_nearby_center_sandwich (r := r) (R := R)
    (show dist z z < d n by simpa using hdpos n)).2
  apply lt_of_le_of_lt ?_ (hn y hy)
  apply measure_mono
  rintro ω ⟨t, htB, htA, htC⟩
  exact ⟨t, (ContinuousPath.exitTime_mono hinner ω).trans htB,
    htA.trans_le (ContinuousPath.exitTime_mono houter ω), htC⟩

/-- The avoidance comparison holds uniformly for all witnesses and all
starting points in a compact subset, with the same fixed interior core. -/
theorem exists_uniform_nearby_annulus_avoidance_comparison
    {z : ℂ} {r R s S : ℝ} (hr : 0 < r) (hrR : r < R)
    (hrs : r < s) (hSR : S < R) {K : Set ℂ} (hK : IsCompact K)
    (hKA : K ⊆ annulus z r R) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z < δ → ∀ y ∈ K, ∀ Y : Set ℂ,
      planarBrownianMotion y {ω | ContinuousPath.exitTime (annulus w r R) ω ≤
        ContinuousPath.exitTime Y ω} ≤
      planarBrownianMotion y {ω | ContinuousPath.exitTime (annulus z r R) ω ≤
        ContinuousPath.exitTime ((annulus z r R ∩ Y) ∪
          (annulus z r R \ {q | s ≤ dist q z ∧ dist q z ≤ S})) ω} + ε := by
  obtain ⟨δ, hδ, hret⟩ := exists_uniform_nearby_annulus_core_return hr hrR hrs hSR hK hKA hε
  refine ⟨δ, hδ, ?_⟩
  intro w hw y hy Y
  apply (stay_probability_le_collar_avoidance_add_return (planarBrownianMotion y)
    (annulus z r R) (annulus w r R) {q | s ≤ dist q z ∧ dist q z ≤ S} Y).trans
  apply add_le_add le_rfl
  simpa only [mem_ofPred_eq] using (hret w hw y hy).le

end HarmonicBalls.Section6
