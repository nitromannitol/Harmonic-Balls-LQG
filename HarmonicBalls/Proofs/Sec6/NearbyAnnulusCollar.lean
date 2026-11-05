import HarmonicBalls.Proofs.Sec6.NearbyAnnulusWitness

/-! # Witness extension across an annular collar

A positive-width collar around both boundary circles can be added to every
nearby witness while preserving a strict mass threshold. This supplies room
for a Brownian crossing estimate; it does not itself provide that estimate.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

/-- The mass of a shrinking annular boundary collar tends to zero. -/
theorem tendsto_annulus_collar_mass_zero
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (z : ℂ) (r R : ℝ)
    (hr : μ (sphere z r) = 0) (hR : μ (sphere z R) = 0) :
    Tendsto (fun n : ℕ => μ (annulus z r R \ annulus z
      (r + 1 / ((n : ℝ) + 1)) (R - 1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have he (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have ht : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun n => 2 * e n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ht
  have hl (s : ℝ) (hs : μ (sphere z s) = 0) :
      Tendsto (fun n => μ (annulus z (s - 2 * e n) (s + 2 * e n))) atTop (𝓝 0) := by
    have h := tendsto_annulus_mass_of_tendsto_boundaries μ
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => z) atTop (𝓝 z))
      (by simpa using tendsto_const_nhds.sub h2)
      (by simpa using tendsto_const_nhds.add h2) hs hs
    have hempty : annulus z s s = ∅ := sdiff_eq_empty.mpr ball_subset_closedBall
    simpa only [hempty, measure_empty] using h
  have hb := (hl r hr).add (hl R hR)
  have hbound (n : ℕ) :
      μ (annulus z r R \ annulus z (r + e n) (R - e n)) ≤
      μ (annulus z (r - 2 * e n) (r + 2 * e n)) +
        μ (annulus z (R - 2 * e n) (R + 2 * e n)) := by
    calc
      _ ≤ μ (annulus z (r - 2 * e n) (r + 2 * e n) ∪
          annulus z (R - 2 * e n) (R + 2 * e n)) := by
        apply measure_mono
        intro x hx
        simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le,
          mem_union] at hx ⊢
        by_cases h : dist x z < R - e n
        · left
          have hh : dist x z ≤ r + e n := le_of_not_gt (fun hh => hx.2 ⟨h, hh⟩)
          constructor <;> linarith [hx.1.1, hx.1.2, he n]
        · right; constructor <;> linarith [hx.1.1, hx.1.2, he n]
      _ ≤ _ := measure_union_le _ _
  change Tendsto (fun n => μ (annulus z r R \ annulus z (r + e n) (R - e n))) atTop (𝓝 0)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hb) (fun _ => bot_le) hbound

/-- A fixed positive-width collar can be added to every nearby witness while
retaining strict slack in the mass threshold. The inner core is contained in
every displaced annulus covered by the conclusion. -/
theorem exists_nearby_annulus_collar_witness_mass_transfer
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (z : ℂ) (r R : ℝ)
    (hr : μ (sphere z r) = 0) (hR : μ (sphere z R) = 0)
    (hpos : 0 < μ (annulus z r R)) (hfin : μ (annulus z r R) ≠ ∞)
    {a a' : ℝ≥0∞} (ha : a' < a) (ha' : a' ≠ ∞) :
    ∃ η ε : ℝ, 0 < ε ∧ ε < η ∧ ∀ w : ℂ, dist w z < ε →
      annulus z (r + η) (R - η) ⊆ annulus w r R ∧
      ∀ Y : Set ℂ, μ Y ≤ a' * μ (annulus w r R) →
        μ ((annulus z r R ∩ Y) ∪
          (annulus z r R \ annulus z (r + η) (R - η))) ≤ a * μ (annulus z r R) := by
  let A := annulus z r R
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let d : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (e n)
  have he (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have hd : Tendsto d atTop (𝓝 0) := by
    simpa only [d, e, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : Tendsto (fun n => μ (A \ annulus z (r + e n) (R - e n))) atTop (𝓝 0) :=
    tendsto_annulus_collar_mass_zero μ z r R hr hR
  have hf : Tendsto (fun n => a' * (μ A + d n) +
      μ (A \ annulus z (r + e n) (R - e n))) atTop (𝓝 (a' * μ A)) := by
    have hs : Tendsto (fun n => μ A + d n) atTop (𝓝 (μ A)) := by
      simpa using tendsto_const_nhds.add hd
    have hh := ((ENNReal.continuous_const_mul ha').tendsto (μ A)).comp hs
    simpa using hh.add hc
  have hlt : a' * μ A < a * μ A := ENNReal.mul_lt_mul_left hpos.ne' hfin ha
  obtain ⟨n, hn⟩ := (hf.eventually_lt_const hlt).exists
  have hdpos : 0 < d n := ENNReal.ofReal_pos.mpr (he n)
  obtain ⟨ε₀, hε₀, hδ⟩ := exists_nearby_annulus_symmDiff_mass_lt μ z r R hr hR hdpos
  let ε := min ε₀ (e n / 2)
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεη : ε < e n := lt_of_le_of_lt (min_le_right _ _) (by linarith [he n])
  refine ⟨e n, ε, hε, hεη, ?_⟩
  intro w hw
  have hw₀ : dist w z < ε₀ := hw.trans_le (min_le_left _ _)
  have hwη : dist w z < e n := hw.trans hεη
  refine ⟨(annulus_nearby_center_sandwich hwη).1, ?_⟩
  intro Y hY
  let B := annulus w r R
  let D := (A \ B) ∪ (B \ A)
  have hD : μ D ≤ d n := (hδ w hw₀).le
  have hBA : μ (B \ A) ≤ d n := (measure_mono (subset_union_right : B \ A ⊆ D)).trans hD
  have hB : μ B ≤ μ A + d n := by
    calc
      μ B ≤ μ (A ∪ (B \ A)) := measure_mono (by intro x hx; by_cases hxA : x ∈ A <;> simp_all)
      _ ≤ μ A + μ (B \ A) := measure_union_le _ _
      _ ≤ μ A + d n := add_le_add le_rfl hBA
  calc
    μ ((A ∩ Y) ∪ (A \ annulus z (r + e n) (R - e n))) ≤
        μ (A ∩ Y) + μ (A \ annulus z (r + e n) (R - e n)) := measure_union_le _ _
    _ ≤ a' * (μ A + d n) + μ (A \ annulus z (r + e n) (R - e n)) :=
      add_le_add ((measure_mono inter_subset_right).trans (hY.trans (by gcongr))) le_rfl
    _ ≤ a * μ A := hn.le

end HarmonicBalls.Section6
