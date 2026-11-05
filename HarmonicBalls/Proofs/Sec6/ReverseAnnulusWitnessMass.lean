import HarmonicBalls.Proofs.Sec6.NearbyAnnulusCollar

/-! # Reverse transfer of annular witness mass -/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

/-- A fixed collar in the nearby annulus can be added to a witness for the
reference annulus, uniformly over nearby centres, with a relaxed mass threshold. -/
theorem exists_reverse_nearby_annulus_collar_witness_mass_transfer
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (z : ℂ) (r R : ℝ)
    (hr : μ (sphere z r) = 0) (hR : μ (sphere z R) = 0)
    (hpos : 0 < μ (annulus z r R)) (hfin : μ (annulus z r R) ≠ ∞)
    {a a' : ℝ≥0∞} (ha : a' < a) (ha_top : a ≠ ∞) :
    ∃ η ε : ℝ, 0 < ε ∧ ε < η ∧ ∀ w : ℂ, dist w z < ε →
      ∀ Y : Set ℂ, μ Y ≤ a' * μ (annulus z r R) →
        μ ((annulus w r R ∩ Y) ∪
          (annulus w r R \ annulus z (r + η) (R - η))) ≤
            a * μ (annulus w r R) := by
  let A := annulus z r R
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let d : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (e n)
  have he (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have hd : Tendsto d atTop (𝓝 0) := by
    simpa only [d, e, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : Tendsto (fun n => μ (A \ annulus z (r + e n) (R - e n))) atTop (𝓝 0) :=
    tendsto_annulus_collar_mass_zero μ z r R hr hR
  have hf : Tendsto (fun n => (a' * μ A +
      μ (A \ annulus z (r + e n) (R - e n)) + d n) + a * d n)
      atTop (𝓝 (a' * μ A)) := by
    have hm := ((ENNReal.continuous_const_mul ha_top).tendsto 0).comp hd
    simpa using ((tendsto_const_nhds.add hc).add hd).add hm
  have hlt : a' * μ A < a * μ A := ENNReal.mul_lt_mul_left hpos.ne' hfin ha
  obtain ⟨n, hn⟩ := (hf.eventually_lt_const hlt).exists
  obtain ⟨ε₀, hε₀, hδ⟩ := exists_nearby_annulus_symmDiff_mass_lt μ z r R hr hR
    (ENNReal.ofReal_pos.mpr (he n))
  let ε := min ε₀ (e n / 2)
  refine ⟨e n, ε, lt_min hε₀ (by positivity),
    lt_of_le_of_lt (min_le_right _ _) (by linarith [he n]), ?_⟩
  intro w hw Y hY
  let B := annulus w r R
  let C := annulus z (r + e n) (R - e n)
  let D := (A \ B) ∪ (B \ A)
  have hD : μ D ≤ d n := (hδ w (hw.trans_le (min_le_left _ _))).le
  have hAB : μ (A \ B) ≤ d n := (measure_mono (subset_union_left : A \ B ⊆ D)).trans hD
  have hBA : μ (B \ A) ≤ d n := (measure_mono (subset_union_right : B \ A ⊆ D)).trans hD
  have hA : μ A ≤ μ B + d n := by
    calc
      μ A ≤ μ (B ∪ (A \ B)) := measure_mono (by intro x hx; by_cases h : x ∈ B <;> simp_all)
      _ ≤ μ B + μ (A \ B) := measure_union_le _ _
      _ ≤ μ B + d n := add_le_add le_rfl hAB
  have hcollar : μ (B \ C) ≤ μ (A \ C) + d n := by
    calc
      μ (B \ C) ≤ μ ((A \ C) ∪ (B \ A)) := measure_mono (by
        intro x hx; by_cases h : x ∈ A <;> simp_all)
      _ ≤ μ (A \ C) + μ (B \ A) := measure_union_le _ _
      _ ≤ μ (A \ C) + d n := add_le_add le_rfl hBA
  have hX : μ ((B ∩ Y) ∪ (B \ C)) ≤ a' * μ A + μ (A \ C) + d n := by
    calc
      _ ≤ μ (B ∩ Y) + μ (B \ C) := measure_union_le _ _
      _ ≤ a' * μ A + (μ (A \ C) + d n) :=
        add_le_add ((measure_mono inter_subset_right).trans hY) hcollar
      _ = _ := by rw [add_assoc]
  apply ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top ha_top ENNReal.ofReal_ne_top)
  calc
    μ ((B ∩ Y) ∪ (B \ C)) + a * d n ≤
        (a' * μ A + μ (A \ C) + d n) + a * d n := add_le_add hX le_rfl
    _ ≤ a * μ A := hn.le
    _ ≤ a * (μ B + d n) := by gcongr
    _ = a * μ B + a * d n := mul_add _ _ _

end HarmonicBalls.Section6
