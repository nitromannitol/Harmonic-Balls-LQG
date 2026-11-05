import HarmonicBalls.Proofs.Sec6.GreenSizeWindow

/-! # Uniform probability windows from almost-sure bounds -/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter
open scoped ENNReal

/-- Pointwise measurability and almost-sure bounds over an arbitrary index set
imply a uniform probability window. -/
theorem exists_uniform_ennreal_window_of_ae_bounds
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (S : Set ι) (F : Ω → ι → ℝ≥0∞)
    (hmeas : ∀ s ∈ S, AEMeasurable (fun ω => F ω s) P)
    (hbounds : ∀ᵐ ω ∂P, ∃ L U : ℝ≥0∞, 0 < L ∧ U ≠ ∞ ∧
      ∀ s ∈ S, L ≤ F ω s ∧ F ω s ≤ U)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ ∀ s ∈ S,
      P {ω | F ω s ∉ Icc (ENNReal.ofReal lo) (ENNReal.ofReal hi)} ≤ δ := by
  classical
  by_contra hnone
  have hex (n : ℕ) : ∃ s ∈ S, δ <
      P {ω | F ω s ∉ Icc (ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)))
        (ENNReal.ofReal (n + 1 : ℝ))} := by
    by_contra hn
    push Not at hn
    apply hnone
    exact ⟨_, _, by positivity, by positivity, hn⟩
  choose s hs hbad using hex
  let X : Ω → ℝ≥0∞ := fun ω => ⨅ i : ℕ, F ω (s i)
  let Y : Ω → ℝ≥0∞ := fun ω => ⨆ i : ℕ, F ω (s i)
  have hX : AEMeasurable X P := AEMeasurable.iInf fun i => hmeas (s i) (hs i)
  have hY : AEMeasurable Y P := AEMeasurable.iSup fun i => hmeas (s i) (hs i)
  have hpos : ∀ᵐ ω ∂P, (0 < X ω ∧ X ω ≠ ∞) ∧ (0 < Y ω ∧ Y ω ≠ ∞) := by
    filter_upwards [hbounds] with ω hω
    obtain ⟨L, U, hL, hU, hb⟩ := hω
    have hLX : L ≤ X ω := le_iInf fun i => (hb (s i) (hs i)).1
    have hYU : Y ω ≤ U := iSup_le fun i => (hb (s i) (hs i)).2
    have hXY : X ω ≤ Y ω := (iInf_le (fun i => F ω (s i)) 0).trans
      (le_iSup (fun i => F ω (s i)) 0)
    exact ⟨⟨hL.trans_le hLX, ne_top_of_le_ne_top hU (hXY.trans hYU)⟩,
      ⟨hL.trans_le (hLX.trans hXY), ne_top_of_le_ne_top hU hYU⟩⟩
  have hhalf : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨lo, lo', hlo, hlo', hlow⟩ :=
    exists_ennreal_window_of_ae_pos_ne_top P hX (hpos.mono fun _ h => h.1) hhalf
  obtain ⟨hi', hi, hhi', hhi, hhigh⟩ :=
    exists_ennreal_window_of_ae_pos_ne_top P hY (hpos.mono fun _ h => h.2) hhalf
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (hlim.eventually (eventually_lt_nhds hlo))
  obtain ⟨n₂, hn₂⟩ := exists_nat_gt hi
  let n := max n₁ n₂
  have hsmall : (1 / 2 : ℝ) ^ (n + 1) ≤ lo :=
    ((pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)).trans_lt
      (hn₁ n (le_max_left _ _))).le
  have hlarge : hi ≤ (n + 1 : ℝ) := by
    have : (n₂ : ℝ) ≤ n := by exact_mod_cast le_max_right n₁ n₂
    linarith
  have hsub : {ω | F ω (s n) ∉ Icc (ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)))
      (ENNReal.ofReal (n + 1 : ℝ))} ⊆
      {ω | X ω ∉ Icc (ENNReal.ofReal lo) (ENNReal.ofReal lo')} ∪
      {ω | Y ω ∉ Icc (ENNReal.ofReal hi') (ENNReal.ofReal hi)} := by
    intro ω hbadω
    by_contra h
    have hh : X ω ∈ Icc (ENNReal.ofReal lo) (ENNReal.ofReal lo') ∧
        Y ω ∈ Icc (ENNReal.ofReal hi') (ENNReal.ofReal hi) := by simpa using h
    apply hbadω
    exact ⟨(ENNReal.ofReal_le_ofReal hsmall).trans (hh.1.1.trans (iInf_le _ n)),
      ((le_iSup _ n).trans hh.2.2).trans (ENNReal.ofReal_le_ofReal hlarge)⟩
  have hle := (measure_mono hsub).trans (measure_union_le (μ := P) _ _)
  have hsum := add_le_add hlow hhigh
  rw [ENNReal.add_halves] at hsum
  exact (not_lt_of_ge (hle.trans hsum)) (hbad n)

end HarmonicBalls.Section6
