import HarmonicBalls.Proofs.Potential.BrownianDyadicModulus

/-! # Occupation bounds and sampled paths

Disjoint time cells turn occupation estimates into bounds on visits at separated times.
-/

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicBalls

/-- Separated sample times whose forward cells stay in the unit interval contribute
one cell of occupation each to a slightly enlarged ball. -/
theorem sample_cells_occupation_le {ι : Type*} [DecidableEq ι]
    (b : ℝ → ℂ) (S : Finset ι) (t : ι → ℝ) (z : ℂ) (δ r E R : ℝ)
    (ht : ∀ i ∈ S, 0 ≤ t i ∧ t i + δ ≤ 1)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |t i - t j|)
    (hvisit : ∀ i ∈ S, ‖b (t i) - z‖ ≤ r)
    (hmod : ∀ i ∈ S, ∀ u ∈ Ico (t i) (t i + δ), ‖b u - b (t i)‖ ≤ E)
    (hR : r + E < R) :
    (S.card : ℝ≥0∞) * ENNReal.ofReal δ ≤
      volume {u : ℝ | u ∈ Icc 0 1 ∧ ‖b u - z‖ < R} := by
  let cell : ι → Set ℝ := fun i => Ico (t i) (t i + δ)
  have hdis : (↑S : Set ι).PairwiseDisjoint cell := by
    intro i hi j hj hij
    apply Set.disjoint_left.2
    intro u hui huj
    have hs := hsep i hi j hj hij
    simp only [cell, mem_Ico] at hui huj
    rw [le_abs] at hs
    rcases hs with hs | hs <;> linarith
  have hsub : (⋃ i ∈ S, cell i) ⊆ {u : ℝ | u ∈ Icc 0 1 ∧ ‖b u - z‖ < R} := by
    intro u hu
    simp only [mem_iUnion] at hu
    obtain ⟨i, hi, hui⟩ := hu
    have hti := ht i hi
    have hm := hmod i hi u hui
    have hv := hvisit i hi
    have hn : ‖b u - z‖ ≤ ‖b u - b (t i)‖ + ‖b (t i) - z‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (b u - b (t i)) (b (t i) - z)
    simp only [cell, mem_Ico] at hui
    exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
  calc
    (S.card : ℝ≥0∞) * ENNReal.ofReal δ = ∑ i ∈ S, volume (cell i) := by
      simp [cell, Real.volume_Ico, mul_comm]
    _ = volume (⋃ i ∈ S, cell i) := by
      symm
      exact measure_biUnion_finset hdis (fun _ _ => measurableSet_Ico)
    _ ≤ _ := measure_mono hsub

/-- At most one separated sample is too close to the right endpoint to have a
full forward cell in the unit interval. -/
theorem sample_occupation_le_add_endpoint {ι : Type*} [DecidableEq ι]
    (b : ℝ → ℂ) (S : Finset ι) (t : ι → ℝ) (z : ℂ) (δ r E R : ℝ)
    (ht : ∀ i ∈ S, 0 ≤ t i ∧ t i ≤ 1)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |t i - t j|)
    (hvisit : ∀ i ∈ S, ‖b (t i) - z‖ ≤ r)
    (hmod : ∀ i ∈ S, ∀ u ∈ Ico (t i) (t i + δ), u ∈ Icc 0 1 →
      ‖b u - b (t i)‖ ≤ E)
    (hR : r + E < R) :
    (S.card : ℝ≥0∞) * ENNReal.ofReal δ ≤
      volume {u : ℝ | u ∈ Icc 0 1 ∧ ‖b u - z‖ < R} + ENNReal.ofReal δ := by
  classical
  let G := S.filter (fun i => t i + δ ≤ 1)
  let B := S.filter (fun i => ¬ t i + δ ≤ 1)
  have hB : B.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    simp only [B, Finset.mem_filter, not_le] at hi hj
    by_contra hij
    have hs := hsep i hi.1 j hj.1 hij
    have hti := ht i hi.1
    have htj := ht j hj.1
    rw [le_abs] at hs
    rcases hs with hs | hs <;> linarith
  have hG := sample_cells_occupation_le b G t z δ r E R
    (fun i hi => ⟨(ht i (Finset.mem_filter.mp hi).1).1, (Finset.mem_filter.mp hi).2⟩)
    (fun i hi j hj hij => hsep i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij)
    (fun i hi => hvisit i (Finset.mem_filter.mp hi).1)
    (by
      intro i hi u hu
      apply hmod i (Finset.mem_filter.mp hi).1 u hu
      have hti := ht i (Finset.mem_filter.mp hi).1
      have hgood := (Finset.mem_filter.mp hi).2
      simp only [mem_Ico] at hu
      exact ⟨by linarith, by linarith⟩) hR
  have hcard : S.card = G.card + B.card := by
    exact (Finset.card_filter_add_card_filter_not (fun i => t i + δ ≤ 1)).symm
  calc
    (S.card : ℝ≥0∞) * ENNReal.ofReal δ =
        (G.card : ℝ≥0∞) * ENNReal.ofReal δ +
          (B.card : ℝ≥0∞) * ENNReal.ofReal δ := by rw [hcard, Nat.cast_add, add_mul]
    _ ≤ volume {u : ℝ | u ∈ Icc 0 1 ∧ ‖b u - z‖ < R} + ENNReal.ofReal δ := by
      gcongr
      calc
        (B.card : ℝ≥0∞) * ENNReal.ofReal δ ≤ (1 : ℝ≥0∞) * ENNReal.ofReal δ := by
          gcongr
          exact_mod_cast hB
        _ = _ := one_mul _

/-- Distinct points of a shifted integer grid are separated by its mesh. -/
theorem shifted_integer_grid_separated (s δ : ℝ) (hδ : 0 ≤ δ)
    {i j : ℤ} (hij : i ≠ j) :
    δ ≤ |(s + δ * (i : ℝ)) - (s + δ * (j : ℝ))| := by
  rcases lt_or_gt_of_ne hij with h | h
  · have hij' : (1 : ℝ) ≤ (j : ℝ) - i := by
      have : i + 1 ≤ j := by omega
      exact_mod_cast (show (1 : ℤ) ≤ j - i by omega)
    have hm := mul_le_mul_of_nonneg_left hij' hδ
    rw [abs_of_nonpos (by nlinarith)]
    nlinarith
  · have hij' : (1 : ℝ) ≤ (i : ℝ) - j := by
      have : j + 1 ≤ i := by omega
      exact_mod_cast (show (1 : ℤ) ≤ i - j by omega)
    have hm := mul_le_mul_of_nonneg_left hij' hδ
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith

/-- An occupation bound controls the number of separated visits, including the
possible endpoint sample. -/
theorem sample_count_le_of_occupation {ι : Type*} [DecidableEq ι]
    (b : ℝ → ℂ) (S : Finset ι) (t : ι → ℝ) (z : ℂ) (δ r E R M : ℝ)
    (hδ : 0 < δ) (hM : 0 ≤ M)
    (ht : ∀ i ∈ S, 0 ≤ t i ∧ t i ≤ 1)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |t i - t j|)
    (hvisit : ∀ i ∈ S, ‖b (t i) - z‖ ≤ r)
    (hmod : ∀ i ∈ S, ∀ u ∈ Ico (t i) (t i + δ), u ∈ Icc 0 1 →
      ‖b u - b (t i)‖ ≤ E)
    (hR : r + E < R)
    (hocc : volume {u : ℝ | u ∈ Icc 0 1 ∧ ‖b u - z‖ < R} ≤
      ENNReal.ofReal (M * δ)) :
    (S.card : ℝ) ≤ M + 1 := by
  have h := (sample_occupation_le_add_endpoint b S t z δ r E R ht hsep hvisit hmod hR).trans
    (add_le_add hocc (le_refl (ENNReal.ofReal δ)))
  have hreal : (S.card : ℝ) * δ ≤ M * δ + δ := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    simpa only [ENNReal.ofReal_add (mul_nonneg hM hδ.le) hδ.le,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using h
  nlinarith

/-- A separated subset of the unit interval has at most one more point than
the reciprocal mesh size. -/
theorem separated_sample_count_le {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (t : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (ht : ∀ i ∈ S, 0 ≤ t i ∧ t i ≤ 1)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |t i - t j|) :
    (S.card : ℝ) ≤ δ⁻¹ + 1 := by
  apply sample_count_le_of_occupation (fun _ => (0 : ℂ)) S t 0 δ 0 0 1 δ⁻¹
    hδ (inv_nonneg.mpr hδ.le) ht hsep
  · simp
  · simp
  · norm_num
  · calc
      volume {u : ℝ | u ∈ Icc 0 1 ∧ ‖(0 : ℂ) - 0‖ < (1 : ℝ)} ≤ volume (Icc (0 : ℝ) 1) :=
        measure_mono (fun _ h => h.1)
      _ = ENNReal.ofReal (δ⁻¹ * δ) := by
        simp [Real.volume_Icc, inv_mul_cancel₀ hδ.ne']

/-- Number of ordered sample pairs whose path values are within a given radius. -/
noncomputable def sampledClosePairCount {ι : Type*} [DecidableEq ι]
    (b : ℝ → ℂ) (S : Finset ι) (t : ι → ℝ) (r : ℝ) : ℕ := by
  classical
  exact ∑ i ∈ S, (S.filter fun j => ‖b (t j) - b (t i)‖ ≤ r).card

/-- A uniform occupation bound controls the number of ordered close pairs. -/
theorem sampledClosePairCount_le {ι : Type*} [DecidableEq ι]
    (b : ℝ → ℂ) (S : Finset ι) (t : ι → ℝ) (δ r E R M : ℝ)
    (hδ : 0 < δ) (hM : 0 ≤ M)
    (ht : ∀ i ∈ S, 0 ≤ t i ∧ t i ≤ 1)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |t i - t j|)
    (hmod : ∀ i ∈ S, ∀ u ∈ Ico (t i) (t i + δ), u ∈ Icc 0 1 →
      ‖b u - b (t i)‖ ≤ E)
    (hR : r + E < R)
    (hocc : ∀ z : ℂ, volume {u : ℝ | u ∈ Icc 0 1 ∧ ‖b u - z‖ < R} ≤
      ENNReal.ofReal (M * δ)) :
    (sampledClosePairCount b S t r : ℝ) ≤ (δ⁻¹ + 1) * (M + 1) := by
  classical
  have hnear : ∀ i ∈ S, ((S.filter fun j => ‖b (t j) - b (t i)‖ ≤ r).card : ℝ) ≤ M + 1 := by
    intro i hi
    apply sample_count_le_of_occupation b _ t (b (t i)) δ r E R M hδ hM
    · intro j hj
      exact ht j (Finset.mem_filter.mp hj).1
    · intro j hj l hl hjl
      exact hsep j (Finset.mem_filter.mp hj).1 l (Finset.mem_filter.mp hl).1 hjl
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
    · intro j hj
      exact hmod j (Finset.mem_filter.mp hj).1
    · exact hR
    · exact hocc _
  calc
    (sampledClosePairCount b S t r : ℝ) =
        ∑ i ∈ S, ((S.filter fun j => ‖b (t j) - b (t i)‖ ≤ r).card : ℝ) := by
      simp [sampledClosePairCount]
    _ ≤ ∑ _i ∈ S, (M + 1) := Finset.sum_le_sum hnear
    _ = (S.card : ℝ) * (M + 1) := by simp [mul_add]
    _ ≤ (δ⁻¹ + 1) * (M + 1) :=
      mul_le_mul_of_nonneg_right (separated_sample_count_le S t δ hδ ht hsep) (by linarith)

end HarmonicBalls
