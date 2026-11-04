import HarmonicBalls.Proofs.Sec8.RandomMeasureContinuitySets
import HarmonicBalls.Defs.Notation

/-! # Continuity-set exhaustions of annuli -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped Topology

/-- An annulus whose frontier is almost surely LQG-null admits an increasing
exhaustion by annuli with almost surely null frontiers. -/
theorem IsWholePlaneGFF.exists_ae_lqg_annular_continuity_exhaustion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (z : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (annulus z r R)) = 0) :
    ∃ E : ℕ → Set ℂ, (∀ n, IsOpen (E n)) ∧ Monotone E ∧
      (⋃ n, E n) = annulus z r R ∧ Bornology.IsBounded (⋃ n, E n) ∧
      ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (E n)) = 0) ∧
        μ ω (frontier (⋃ n, E n)) = 0 := by
  let m : ℝ := (r + R) / 2
  have hrm : r < m := by dsimp [m]; linarith
  have hmR : m < R := by dsimp [m]; linarith
  obtain ⟨s, hsanti, hsrange, hslim⟩ := exists_seq_strictAnti_tendsto' hrm
  obtain ⟨t, htmono, htrange, htlim⟩ := exists_seq_strictMono_tendsto' hmR
  obtain ⟨a, ha, hza⟩ := hgff.exists_ae_lqg_null_frontier_balls_unbounded P hμ
    (fun _ => z) (fun n => s (n + 1)) s (fun n => hsanti (Nat.lt_succ_self n))
  obtain ⟨b, hb, hzb⟩ := hgff.exists_ae_lqg_null_frontier_balls_unbounded P hμ
    (fun _ => z) t (fun n => t (n + 1)) (fun n => htmono (Nat.lt_succ_self n))
  have hanti : Antitone a := by
    exact (strictAnti_nat_of_succ_lt (fun n =>
      lt_trans (ha (n + 1)).2 (ha n).1)).antitone
  have hmono : Monotone b := by
    exact (strictMono_nat_of_lt_succ (fun n =>
      lt_trans (hb n).2 (hb (n + 1)).1)).monotone
  have halow (n : ℕ) : r < a n := lt_trans (hsrange (n + 1)).1 (ha n).1
  have hblt (n : ℕ) : b n < R := lt_trans (hb n).2 (htrange (n + 1)).2
  have halim : Tendsto a atTop (𝓝 r) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hslim
      (fun n => (halow n).le) (fun n => (ha n).2.le)
  have hblim : Tendsto b atTop (𝓝 R) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le htlim tendsto_const_nhds
      (fun n => (hb n).1.le) (fun n => (hblt n).le)
  let E : ℕ → Set ℂ := fun n => annulus z (a n) (b n)
  have hEunion : (⋃ n, E n) = annulus z r R := by
    ext w
    simp only [mem_iUnion, E, annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
    constructor
    · rintro ⟨n, hw1, hw2⟩
      exact ⟨lt_trans hw1 (hblt n), lt_trans (halow n) hw2⟩
    · rintro ⟨hw1, hw2⟩
      have he1 : ∀ᶠ n in atTop, dist w z < b n := hblim.eventually (Ioi_mem_nhds hw1)
      have he2 : ∀ᶠ n in atTop, a n < dist w z := halim.eventually (Iio_mem_nhds hw2)
      obtain ⟨n, hn1, hn2⟩ := (he1.and he2).exists
      exact ⟨n, hn1, hn2⟩
  refine ⟨E, ?_, ?_, hEunion, ?_, ?_⟩
  · intro n
    exact isOpen_ball.sdiff isClosed_closedBall
  · intro i j hij w hw
    have hw1 : dist w z < b i := hw.1
    have hw2 : a i < dist w z := not_le.mp hw.2
    exact ⟨lt_of_lt_of_le hw1 (hmono hij), not_le.mpr (lt_of_le_of_lt (hanti hij) hw2)⟩
  · rw [hEunion]
    exact (isBounded_ball : Bornology.IsBounded (ball z R)).subset sdiff_subset
  · filter_upwards [hza, hzb, hfront] with ω hzaω hzbω hfω
    refine ⟨?_, hEunion ▸ hfω⟩
    intro n
    have ha0 : a n ≠ 0 := (lt_of_le_of_lt hr (halow n)).ne'
    have hball : μ ω (frontier (ball z (a n))) = 0 := hzaω n
    have hclosed : μ ω (frontier (closedBall z (a n))) = 0 := by
      rw [frontier_closedBall z ha0, ← frontier_ball z ha0]
      exact hball
    have hsub : frontier (E n) ⊆
        frontier (ball z (b n)) ∪ frontier (closedBall z (a n)) := by
      simpa only [E, annulus, Set.sdiff_eq, frontier_compl] using
        (frontier_inter_subset (ball z (b n)) (closedBall z (a n))ᶜ).trans
          (union_subset_union inter_subset_left inter_subset_right)
    exact measure_mono_null hsub (measure_union_null (hzbω n) hclosed)

end HarmonicBalls.Section6
