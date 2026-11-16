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

/-- Enlarged dyadic radii are eventually small, while their logarithms grow at
most linearly with the scale. -/
theorem enlarged_dyadic_radius_eventually (D ε : ℝ) (hD : 1 ≤ D) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k ≥ N, 1 ≤ k →
      let R := D * (1 / 2 : ℝ) ^ k * Real.sqrt k
      0 < R ∧ R ≤ ε ∧ R ≤ 1 ∧ (1 / 2 : ℝ) ^ k ≤ R ∧
        0 ≤ Real.log (1 / R) ∧ Real.log (1 / R) ≤ (k : ℝ) * Real.log 2 := by
  have hlim : Filter.Tendsto (fun k : ℕ => D * ((k : ℝ) * (1 / 2 : ℝ) ^ k))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_self_mul_const_pow_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul D
  have hev : ∀ᶠ k : ℕ in Filter.atTop, D * ((k : ℝ) * (1 / 2 : ℝ) ^ k) < min ε 1 :=
    hlim.eventually (Iio_mem_nhds (lt_min hε zero_lt_one))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N, ?_⟩
  intro k hk hk1
  dsimp only
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hsqrt1 : 1 ≤ Real.sqrt k := Real.one_le_sqrt.mpr hkreal
  have hsqrtk : Real.sqrt k ≤ k := Real.sqrt_le_self_iff.mpr (Or.inr hkreal)
  have hpow : 0 < (1 / 2 : ℝ) ^ k := by positivity
  have hD0 : 0 < D := by linarith
  have hbound : D * (1 / 2 : ℝ) ^ k * Real.sqrt k ≤
      D * ((k : ℝ) * (1 / 2 : ℝ) ^ k) := by
    nlinarith [mul_nonneg (mul_nonneg hD0.le hpow.le) (sub_nonneg.mpr hsqrtk)]
  have hsmall := hN k hk
  have hpos : 0 < D * (1 / 2 : ℝ) ^ k * Real.sqrt k := by positivity
  have hlarge : (1 / 2 : ℝ) ^ k ≤ D * (1 / 2 : ℝ) ^ k * Real.sqrt k := by
    nlinarith [mul_nonneg hpow.le (sub_nonneg.mpr hsqrt1),
      mul_nonneg (mul_nonneg hpow.le (by linarith : 0 ≤ Real.sqrt k)) (sub_nonneg.mpr hD)]
  have hsmallone : D * (1 / 2 : ℝ) ^ k * Real.sqrt k ≤ 1 := by
    exact (hbound.trans_lt (hsmall.trans_le (min_le_right _ _))).le
  refine ⟨hpos, (hbound.trans_lt (hsmall.trans_le (min_le_left _ _))).le, hsmallone,
    hlarge, ?_, ?_⟩
  · exact Real.log_nonneg (one_le_one_div hpos hsmallone)
  · have hinv : 1 / (D * (1 / 2 : ℝ) ^ k * Real.sqrt k) ≤
        1 / (1 / 2 : ℝ) ^ k := one_div_le_one_div_of_le hpow hlarge
    have hlog := Real.log_le_log (one_div_pos.mpr hpos) hinv
    have heq : 1 / (1 / 2 : ℝ) ^ k = (2 : ℝ) ^ k := by
      rw [one_div, ← inv_pow]
      norm_num
    simpa [heq, Real.log_pow] using hlog

/-- The sharp logarithmic occupation expression at the enlarged dyadic radius
is at most a cubic factor times the dyadic time mesh. -/
theorem enlarged_dyadic_occupation_le (A D ε : ℝ) (hA : 0 ≤ A)
    (hD : 1 ≤ D) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k ≥ N, 1 ≤ k →
      let R := D * (1 / 2 : ℝ) ^ k * Real.sqrt k
      R ≤ ε ∧ 0 < R ∧
        A * R ^ 2 * (Real.log (1 / R)) ^ 2 ≤
          (A * D ^ 2 * (Real.log 2) ^ 2 * (k : ℝ) ^ 3) * (1 / 4 : ℝ) ^ k := by
  obtain ⟨N, hN⟩ := enlarged_dyadic_radius_eventually D ε hD hε
  refine ⟨N, ?_⟩
  intro k hk hk1
  obtain ⟨hpos, hε', _, _, hlog0, hlog⟩ := hN k hk hk1
  dsimp only at *
  refine ⟨hε', hpos, ?_⟩
  have hpow : ((1 / 2 : ℝ) ^ k) ^ 2 = (1 / 4 : ℝ) ^ k := by
    calc
      ((1 / 2 : ℝ) ^ k) ^ 2 = ((1 / 2 : ℝ) ^ 2) ^ k := by
        rw [← pow_mul, ← pow_mul, mul_comm]
      _ = (1 / 4 : ℝ) ^ k := by norm_num
  have hr2 : (D * (1 / 2 : ℝ) ^ k * Real.sqrt k) ^ 2 =
      D ^ 2 * (1 / 4 : ℝ) ^ k * (k : ℝ) := by
    rw [mul_pow, mul_pow, hpow, Real.sq_sqrt (Nat.cast_nonneg k)]
  have hsquare : (Real.log (1 / (D * (1 / 2 : ℝ) ^ k * Real.sqrt k))) ^ 2 ≤
      ((k : ℝ) * Real.log 2) ^ 2 := by nlinarith
  calc
    A * (D * (1 / 2 : ℝ) ^ k * Real.sqrt k) ^ 2 *
        (Real.log (1 / (D * (1 / 2 : ℝ) ^ k * Real.sqrt k))) ^ 2
      ≤ A * (D ^ 2 * (1 / 4 : ℝ) ^ k * (k : ℝ)) * ((k : ℝ) * Real.log 2) ^ 2 := by
        rw [hr2]
        exact mul_le_mul_of_nonneg_left hsquare (by positivity)
    _ = _ := by ring

/-- The number of close ordered pairs is bounded by the square of the number
of sample points. -/
theorem sampledClosePairCount_le_card_sq {ι : Type*} [DecidableEq ι]
    (b : ℝ → ℂ) (S : Finset ι) (t : ι → ℝ) (r : ℝ) :
    sampledClosePairCount b S t r ≤ S.card ^ 2 := by
  classical
  calc
    sampledClosePairCount b S t r ≤ ∑ _i ∈ S, S.card := by
      unfold sampledClosePairCount
      apply Finset.sum_le_sum
      intro i _hi
      exact Finset.card_filter_le _ _
    _ = S.card ^ 2 := by simp [pow_two]

/-- At all sufficiently fine scales, the square-root modulus and sharp uniform
occupation estimate imply the cubic close-pair bound for every shifted grid. -/
theorem dyadic_close_pairs_eventually (b : ℝ → ℂ) (L A ε : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hε : 0 < ε)
    (hmod : ∀ k : ℕ, 1 ≤ k → ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |u - v| ≤ (1 / 4 : ℝ) ^ k →
      ‖b u - b v‖ ≤ L * (1 / 2 : ℝ) ^ k * Real.sqrt k)
    (hocc : ∀ z : ℂ, ∀ r : ℝ, 0 < r → r ≤ ε →
      volume {u : ℝ | u ∈ Icc 0 1 ∧ ‖b u - z‖ < r} ≤
        ENNReal.ofReal (A * r ^ 2 * (Real.log (1 / r)) ^ 2)) :
    ∃ N : ℕ, ∀ k ≥ N, 1 ≤ k → ∀ s : ℝ, ∀ S : Finset ℤ,
      (∀ i ∈ S, s + (1 / 4 : ℝ) ^ k * (i : ℝ) ∈ Icc (0 : ℝ) 1) →
      (sampledClosePairCount b S (fun i => s + (1 / 4 : ℝ) ^ k * (i : ℝ))
          ((1 / 2 : ℝ) ^ k) : ℝ) ≤
        2 * (A * (L + 2) ^ 2 * (Real.log 2) ^ 2 + 1) * (4 : ℝ) ^ k * (k : ℝ) ^ 3 := by
  let D := L + 2
  let Q := A * D ^ 2 * (Real.log 2) ^ 2
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  obtain ⟨N, hN⟩ := enlarged_dyadic_occupation_le A D ε hA hD hε
  refine ⟨N, ?_⟩
  intro k hk hk1 s S ht
  let δ : ℝ := (1 / 4 : ℝ) ^ k
  let q : ℝ := (1 / 2 : ℝ) ^ k
  let R : ℝ := D * q * Real.sqrt k
  let t : ℤ → ℝ := fun i => s + δ * (i : ℝ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hsqrt : 1 ≤ Real.sqrt k := Real.one_le_sqrt.mpr hkreal
  have hk3 : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ hkreal
  obtain ⟨hRε, hRpos, hscale⟩ := hN k hk hk1
  change R ≤ ε at hRε
  change 0 < R at hRpos
  change A * R ^ 2 * (Real.log (1 / R)) ^ 2 ≤ (Q * (k : ℝ) ^ 3) * δ at hscale
  have hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |t i - t j| := by
    intro i _hi j _hj hij
    exact shifted_integer_grid_separated s δ hδ.le hij
  have htime : ∀ i ∈ S, 0 ≤ t i ∧ t i ≤ 1 := ht
  have hosc : ∀ i ∈ S, ∀ u ∈ Ico (t i) (t i + δ), u ∈ Icc 0 1 →
      ‖b u - b (t i)‖ ≤ L * q * Real.sqrt k := by
    intro i hi u hu huunit
    apply hmod k hk1 u huunit (t i) (ht i hi)
    rw [abs_of_nonneg (by linarith [hu.1])]
    linarith [hu.2]
  have hr : q + L * q * Real.sqrt k < R := by
    dsimp [R, D]
    nlinarith [mul_nonneg hq.le (sub_nonneg.mpr hsqrt)]
  have hocc' : ∀ z : ℂ, volume {u : ℝ | u ∈ Icc 0 1 ∧ ‖b u - z‖ < R} ≤
      ENNReal.ofReal ((Q * (k : ℝ) ^ 3) * δ) := by
    intro z
    exact (hocc z R hRpos hRε).trans (ENNReal.ofReal_le_ofReal hscale)
  have hpair := sampledClosePairCount_le b S t δ q (L * q * Real.sqrt k) R
    (Q * (k : ℝ) ^ 3) hδ (by positivity) htime hsep hosc hr hocc'
  have hinv : δ⁻¹ = (4 : ℝ) ^ k := by
    dsimp [δ]
    rw [← inv_pow]
    norm_num
  have hfour : (1 : ℝ) ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hfirst : δ⁻¹ + 1 ≤ 2 * (4 : ℝ) ^ k := by rw [hinv]; linarith
  have hsecond : Q * (k : ℝ) ^ 3 + 1 ≤ (Q + 1) * (k : ℝ) ^ 3 := by nlinarith
  calc
    _ ≤ (δ⁻¹ + 1) * (Q * (k : ℝ) ^ 3 + 1) := hpair
    _ ≤ (2 * (4 : ℝ) ^ k) * ((Q + 1) * (k : ℝ) ^ 3) := by
      exact mul_le_mul hfirst hsecond (by positivity) (by positivity)
    _ = _ := by dsimp [Q, D]; ring

/-- A square-root dyadic modulus and a uniform sharp occupation estimate imply
an ordered close-pair bound at every positive dyadic scale and every shift. -/
theorem dyadic_close_pairs_of_occupation (b : ℝ → ℂ) (L A ε : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hε : 0 < ε)
    (hmod : ∀ k : ℕ, 1 ≤ k → ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |u - v| ≤ (1 / 4 : ℝ) ^ k →
      ‖b u - b v‖ ≤ L * (1 / 2 : ℝ) ^ k * Real.sqrt k)
    (hocc : ∀ z : ℂ, ∀ r : ℝ, 0 < r → r ≤ ε →
      volume {u : ℝ | u ∈ Icc 0 1 ∧ ‖b u - z‖ < r} ≤
        ENNReal.ofReal (A * r ^ 2 * (Real.log (1 / r)) ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ s : ℝ, ∀ S : Finset ℤ,
      (∀ i ∈ S, s + (1 / 4 : ℝ) ^ k * (i : ℝ) ∈ Icc (0 : ℝ) 1) →
      (sampledClosePairCount b S (fun i => s + (1 / 4 : ℝ) ^ k * (i : ℝ))
          ((1 / 2 : ℝ) ^ k) : ℝ) ≤ C * (4 : ℝ) ^ k * (k : ℝ) ^ 3 := by
  let Q := A * (L + 2) ^ 2 * (Real.log 2) ^ 2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  obtain ⟨N, hN⟩ := dyadic_close_pairs_eventually b L A ε hL hA hε hmod hocc
  let C : ℝ := 2 * (Q + 1 + ((4 : ℝ) ^ N + 1))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro k hk s S ht
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk3 : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ hkreal
  have hfour : (1 : ℝ) ≤ (4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  by_cases hkN : N ≤ k
  · have hfine := hN k hkN hk s S ht
    have hconst : 2 * (A * (L + 2) ^ 2 * (Real.log 2) ^ 2 + 1) ≤ C := by
      change 2 * (Q + 1) ≤ C
      dsimp [C]
      nlinarith [show 0 ≤ (4 : ℝ) ^ N by positivity]
    exact hfine.trans (by gcongr)
  · let δ : ℝ := (1 / 4 : ℝ) ^ k
    let t : ℤ → ℝ := fun i => s + δ * (i : ℝ)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hinv : δ⁻¹ = (4 : ℝ) ^ k := by
      dsimp [δ]
      rw [← inv_pow]
      norm_num
    have hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → δ ≤ |t i - t j| := by
      intro i _hi j _hj hij
      exact shifted_integer_grid_separated s δ hδ.le hij
    have hcard := separated_sample_count_le S t δ hδ ht hsep
    rw [hinv] at hcard
    have hpair : (sampledClosePairCount b S t ((1 / 2 : ℝ) ^ k) : ℝ) ≤
        (S.card : ℝ) ^ 2 := by
      exact_mod_cast sampledClosePairCount_le_card_sq b S t ((1 / 2 : ℝ) ^ k)
    have hpow : (4 : ℝ) ^ k ≤ (4 : ℝ) ^ N := by
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hfirst : (4 : ℝ) ^ k + 1 ≤ 2 * (4 : ℝ) ^ k := by linarith
    have hsecond : (4 : ℝ) ^ k + 1 ≤ (4 : ℝ) ^ N + 1 := by linarith
    have hsq : (S.card : ℝ) ^ 2 ≤ (2 * (4 : ℝ) ^ k) * ((4 : ℝ) ^ N + 1) := by
      calc
        (S.card : ℝ) ^ 2 ≤ ((4 : ℝ) ^ k + 1) ^ 2 := by nlinarith
        _ ≤ (2 * (4 : ℝ) ^ k) * ((4 : ℝ) ^ N + 1) := by
          nlinarith [mul_le_mul hfirst hsecond (by positivity : 0 ≤ (4 : ℝ) ^ k + 1)
            (by positivity : 0 ≤ 2 * (4 : ℝ) ^ k)]
    have hconst : 2 * ((4 : ℝ) ^ N + 1) ≤ C := by dsimp [C]; linarith
    calc
      _ ≤ (S.card : ℝ) ^ 2 := hpair
      _ ≤ (2 * (4 : ℝ) ^ k) * ((4 : ℝ) ^ N + 1) := hsq
      _ ≤ C * (4 : ℝ) ^ k * (k : ℝ) ^ 3 := by
        nlinarith [mul_nonneg (by positivity : 0 ≤ C * (4 : ℝ) ^ k) (sub_nonneg.mpr hk3),
          mul_nonneg (sub_nonneg.mpr hconst) (by positivity : 0 ≤ (4 : ℝ) ^ k)]

/-- Integer indices of the shifted dyadic grid lying in the unit interval. -/
noncomputable def shiftedDyadicIndices (s : ℝ) (k : ℕ) : Finset ℤ :=
  Finset.Icc ⌈(-s) / (1 / 4 : ℝ) ^ k⌉ ⌊(1 - s) / (1 / 4 : ℝ) ^ k⌋

/-- The index set contains precisely the shifted dyadic times in the unit interval. -/
theorem mem_shiftedDyadicIndices (s : ℝ) (k : ℕ) (i : ℤ) :
    i ∈ shiftedDyadicIndices s k ↔
      s + (1 / 4 : ℝ) ^ k * (i : ℝ) ∈ Icc (0 : ℝ) 1 := by
  have hδ : 0 < (1 / 4 : ℝ) ^ k := by positivity
  simp only [shiftedDyadicIndices, Finset.mem_Icc, Int.ceil_le, Int.le_floor, mem_Icc]
  rw [div_le_iff₀ hδ, le_div_iff₀ hδ]
  constructor <;> intro h <;> constructor <;> nlinarith [h.1, h.2]

/-- The full shifted dyadic grids satisfy the conditional occupation-to-pair bound. -/
theorem shifted_dyadic_close_pairs_of_occupation (b : ℝ → ℂ) (L A ε : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hε : 0 < ε)
    (hmod : ∀ k : ℕ, 1 ≤ k → ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |u - v| ≤ (1 / 4 : ℝ) ^ k →
      ‖b u - b v‖ ≤ L * (1 / 2 : ℝ) ^ k * Real.sqrt k)
    (hocc : ∀ z : ℂ, ∀ r : ℝ, 0 < r → r ≤ ε →
      volume {u : ℝ | u ∈ Icc 0 1 ∧ ‖b u - z‖ < r} ≤
        ENNReal.ofReal (A * r ^ 2 * (Real.log (1 / r)) ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, 1 ≤ k → ∀ s : ℝ,
      (sampledClosePairCount b (shiftedDyadicIndices s k)
        (fun i => s + (1 / 4 : ℝ) ^ k * (i : ℝ)) ((1 / 2 : ℝ) ^ k) : ℝ) ≤
          C * (4 : ℝ) ^ k * (k : ℝ) ^ 3 := by
  obtain ⟨C, hC, h⟩ := dyadic_close_pairs_of_occupation b L A ε hL hA hε hmod hocc
  refine ⟨C, hC, ?_⟩
  intro k hk s
  apply h k hk s (shiftedDyadicIndices s k)
  intro i hi
  exact (mem_shiftedDyadicIndices s k i).mp hi

/-- The sum defining the count is the cardinality of the ordered close-pair set. -/
theorem sampledClosePairCount_eq_card {ι : Type*} [DecidableEq ι]
    (b : ℝ → ℂ) (S : Finset ι) (t : ι → ℝ) (r : ℝ) :
    sampledClosePairCount b S t r =
      ((S.product S).filter fun p => ‖b (t p.2) - b (t p.1)‖ ≤ r).card := by
  classical
  simp only [sampledClosePairCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact (Finset.sum_product S S (fun p : ι × ι =>
    if ‖b (t p.2) - b (t p.1)‖ ≤ r then (1 : ℕ) else 0)).symm

/-- The shifted dyadic index parametrization has no repeated sample times. -/
theorem shifted_dyadic_time_injective (s : ℝ) (k : ℕ) :
    Function.Injective (fun i : ℤ => s + (1 / 4 : ℝ) ^ k * (i : ℝ)) := by
  intro i j hij
  have hδ : (1 / 4 : ℝ) ^ k ≠ 0 := by positivity
  have heq : (1 / 4 : ℝ) ^ k * (i : ℝ) = (1 / 4 : ℝ) ^ k * (j : ℝ) := by linarith
  have hcast : (i : ℝ) = j := mul_left_cancel₀ hδ heq
  exact_mod_cast hcast

end HarmonicBalls
