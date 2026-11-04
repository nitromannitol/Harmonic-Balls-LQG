import HarmonicBalls.Draft.Section6

/-! # Cardinality of the prevalence lattice -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

/-- The prevalence grid is contained in the image of a finite integer square. -/
theorem prevalenceGrid_subset_integer_square {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    prevalenceGrid ε ⊆ (fun p : ℤ × ℤ => ((ε / 100 : ℝ) : ℂ) *
      ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) ''
      ((Icc (-⌈200 / ε⌉) ⌈200 / ε⌉ : Set ℤ) ×ˢ
       (Icc (-⌈200 / ε⌉) ⌈200 / ε⌉ : Set ℤ)) := by
  intro z hz
  obtain ⟨j, k, rfl⟩ := hz.2
  have hn : ‖((ε / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)‖ < 2 := by
    have := mem_ball_zero_iff.mp hz.1.1
    linarith
  have hj : |(ε / 100) * (j : ℝ)| < 2 := by
    have h := (Complex.abs_re_le_norm
      (((ε / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I))).trans_lt hn
    simpa using h
  have hk : |(ε / 100) * (k : ℝ)| < 2 := by
    have h := (Complex.abs_im_le_norm
      (((ε / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I))).trans_lt hn
    simpa using h
  have hc : 200 / ε ≤ (⌈200 / ε⌉ : ℤ) := Int.le_ceil _
  have hj' : |(j : ℝ)| ≤ (⌈200 / ε⌉ : ℤ) := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < ε / 100)] at hj
    have : |(j : ℝ)| < 200 / ε := by
      apply (lt_div_iff₀ hε).2
      nlinarith
    exact this.le.trans hc
  have hk' : |(k : ℝ)| ≤ (⌈200 / ε⌉ : ℤ) := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < ε / 100)] at hk
    have : |(k : ℝ)| < 200 / ε := by
      apply (lt_div_iff₀ hε).2
      nlinarith
    exact this.le.trans hc
  refine ⟨(j, k), ⟨?_, ?_⟩, rfl⟩
  · have h := abs_le.mp hj'
    constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  · have h := abs_le.mp hk'
    constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2

/-- The prevalence grid is finite. -/
theorem finite_prevalenceGrid {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (prevalenceGrid ε).Finite := by
  let M : ℤ := ⌈200 / ε⌉
  have hf : (Icc (-M) M : Set ℤ).Finite := Set.finite_Icc _ _
  apply ((hf.prod hf).image _).subset
  exact prevalenceGrid_subset_integer_square hε hε1

/-- An explicit quadratic upper bound for the number of grid points. -/
theorem prevalenceGrid_ncard_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((prevalenceGrid ε).ncard : ℝ) ≤ (403 / ε) ^ 2 := by
  let M : ℤ := ⌈200 / ε⌉
  let S : Set ℤ := Icc (-M) M
  have hM : 0 ≤ M := by
    have h : (0 : ℝ) ≤ (M : ℝ) := (div_nonneg (by norm_num) hε.le).trans (Int.le_ceil _)
    exact_mod_cast h
  have hf : S.Finite := Set.finite_Icc _ _
  have hc : (S.ncard : ℝ) = 2 * (M : ℝ) + 1 := by
    have hcard := Int.card_Icc_of_le (a := -M) (b := M) (by omega)
    have hcast : ((Finset.Icc (-M) M).card : ℝ) = ((M + 1 - -M : ℤ) : ℝ) := by
      exact_mod_cast hcard
    have hcast' : (S.ncard : ℝ) = (M : ℝ) + 1 + (M : ℝ) := by
      simpa [S, ← Set.ncard_coe_finset, Int.cast_add, Int.cast_sub] using hcast
    linarith
  have hsub := prevalenceGrid_subset_integer_square hε hε1
  have hn : (prevalenceGrid ε).ncard ≤ (S ×ˢ S).ncard := by
    calc
      _ ≤ ((fun p : ℤ × ℤ => ((ε / 100 : ℝ) : ℂ) *
          ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) '' (S ×ˢ S)).ncard :=
        Set.ncard_le_ncard hsub ((hf.prod hf).image _)
      _ ≤ _ := Set.ncard_image_le (hf.prod hf)
  have hn' : ((prevalenceGrid ε).ncard : ℝ) ≤ (2 * (M : ℝ) + 1) ^ 2 := by
    have := (show ((prevalenceGrid ε).ncard : ℝ) ≤ ((S ×ˢ S).ncard : ℝ) by exact_mod_cast hn)
    simpa [Set.ncard_prod, Nat.cast_mul, hc, pow_two] using this
  have hceil : (M : ℝ) < 200 / ε + 1 := Int.ceil_lt_add_one _
  have hεinv : 1 ≤ 1 / ε := (le_div_iff₀ hε).2 (by linarith)
  have hbound : 2 * (M : ℝ) + 1 ≤ 403 / ε := by
    have hthree : 3 ≤ 3 / ε := by
      calc
        3 ≤ 3 * (1 / ε) := by linarith
        _ = 3 / ε := by ring
    have hid : 403 / ε = 2 * (200 / ε) + 3 / ε := by ring
    linarith
  have hnonneg : 0 ≤ 2 * (M : ℝ) + 1 := by exact_mod_cast (by omega : 0 ≤ 2 * M + 1)
  exact hn'.trans (pow_le_pow_left₀ hnonneg hbound 2)

/-- A union bound over the prevalence grid, for arbitrary events. -/
theorem measure_exists_mem_prevalenceGrid_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (E : ℂ → Set Ω) (q : ℝ≥0∞)
    (hq : ∀ z ∈ prevalenceGrid ε, P (E z) ≤ q) :
    P {ω | ∃ z ∈ prevalenceGrid ε, ω ∈ E z} ≤
      ENNReal.ofReal ((403 / ε) ^ 2) * q := by
  classical
  let hf := finite_prevalenceGrid hε hε1
  let s := hf.toFinset
  have hs : ∀ z, z ∈ s ↔ z ∈ prevalenceGrid ε := by
    intro z
    simp [s]
  have heq : {ω | ∃ z ∈ prevalenceGrid ε, ω ∈ E z} = ⋃ z ∈ s, E z := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, hs, exists_prop]
  rw [heq]
  calc
    _ ≤ ∑ z ∈ s, P (E z) := measure_biUnion_finset_le s E
    _ ≤ ∑ _z ∈ s, q := Finset.sum_le_sum (fun z hz => hq z ((hs z).1 hz))
    _ = (s.card : ℝ≥0∞) * q := by simp
    _ ≤ ENNReal.ofReal ((403 / ε) ^ 2) * q := by
      gcongr
      have hn := prevalenceGrid_ncard_le hε hε1
      have hc : (s.card : ℝ) = ((prevalenceGrid ε).ncard : ℝ) := by
        exact_mod_cast (Set.ncard_eq_toFinset_card _ hf).symm
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (by simpa only [hc] using hn)

end HarmonicBalls.Section6
