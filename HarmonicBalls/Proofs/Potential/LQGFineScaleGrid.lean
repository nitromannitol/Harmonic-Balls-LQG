import LatticeProb.LQG.GMCDilatedGrid

/-! # Summability for fine-scale grids

A geometric estimate for grids whose scale index dominates their spatial index.
-/

open Filter MeasureTheory Real

namespace HarmonicBalls

/-- A two-index geometric series remains summable when its second index is
restricted to lie above a sufficiently steep linear threshold. -/
theorem summable_fine_scale_grid {A t : ℝ} {m : ℕ} (hA : 0 ≤ A)
    (ht : 0 ≤ t) (ht1 : t < 1) (hdecay : A * t ^ m < 1) :
    Summable fun p : ℕ × ℕ =>
      if m * p.1 ≤ p.2 then A ^ p.1 * (t ^ 2) ^ p.2 else 0 := by
  have hr : 0 ≤ A * t ^ m := mul_nonneg hA (pow_nonneg ht _)
  have hsum : Summable fun p : ℕ × ℕ => (A * t ^ m) ^ p.1 * t ^ p.2 :=
    (summable_geometric_of_lt_one hr hdecay).mul_of_nonneg
      (summable_geometric_of_lt_one ht ht1)
      (fun _ => pow_nonneg hr _) (fun _ => pow_nonneg ht _)
  refine Summable.of_norm_bounded hsum fun ⟨j, n⟩ => ?_
  by_cases h : m * j ≤ n
  · simp only [h, ↓reduceIte, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg hA _) (pow_nonneg (sq_nonneg t) _))]
    have hpow : t ^ n ≤ t ^ (m * j) := pow_le_pow_of_le_one ht ht1.le h
    calc A ^ j * (t ^ 2) ^ n = A ^ j * (t ^ n * t ^ n) := by rw [pow_two, mul_pow]
      _ ≤ A ^ j * (t ^ (m * j) * t ^ n) := by gcongr
      _ = (A * t ^ m) ^ j * t ^ n := by rw [mul_pow, ← pow_mul]; ring
  · simp only [h, ↓reduceIte, norm_zero]
    exact mul_nonneg (pow_nonneg hr _) (pow_nonneg ht _)



/-- A sufficiently steep threshold yields summability for every nonnegative
spatial growth factor and every geometric decay factor below one. -/
theorem exists_summable_fine_scale_grid {A t : ℝ} (hA : 0 ≤ A)
    (ht : 0 ≤ t) (ht1 : t < 1) :
    ∃ m : ℕ, Summable fun p : ℕ × ℕ =>
      if m * p.1 ≤ p.2 then A ^ p.1 * (t ^ 2) ^ p.2 else 0 := by
  have hlim : Tendsto (fun m : ℕ => A * t ^ m) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ht ht1).const_mul A
  obtain ⟨m, hm⟩ := (eventually_atTop.1 (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)))
  exact ⟨m, summable_fine_scale_grid hA ht ht1 (hm m le_rfl)⟩

/-- A summable bound on fine-scale increment probabilities yields simultaneous
control over all sufficiently fine grid points. -/
theorem ae_eventually_fine_scale_grid_abs_lt {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} {X : ℕ → ℕ → ℕ → Ω → ℝ}
    {N : ℕ → ℕ → ℕ} {b δ : ℕ → ℕ → ℝ} {m : ℕ}
    (hδ : ∀ j n, 0 < δ j n)
    (hX : ∀ j n i, m * j ≤ n → i ≤ N j n → MeasureTheory.Integrable (X j n i) P)
    (hb : ∀ j n i, m * j ≤ n → i ≤ N j n →
      ∫ ω, |X j n i ω| ∂P ≤ b j n)
    (hsum : Summable fun p : ℕ × ℕ =>
      if m * p.1 ≤ p.2 then ((N p.1 p.2 : ℝ) + 1) * (b p.1 p.2 / δ p.1 p.2) else 0) :
    ∀ᵐ ω ∂P, ∀ᶠ j in atTop, ∀ n, m * j ≤ n → ∀ i ≤ N j n, |X j n i ω| < δ j n := by
  let Y : ℕ → ℕ → ℕ → Ω → ℝ := fun j n i ω => if m * j ≤ n then X j n i ω else 0
  let c : ℕ → ℕ → ℝ := fun j n => if m * j ≤ n then b j n else 0
  have hY : ∀ j n i, i ≤ N j n → MeasureTheory.Integrable (Y j n i) P := by
    intro j n i hi
    by_cases h : m * j ≤ n
    · simpa [Y, h] using hX j n i h hi
    · simp [Y, h]
  have hYb : ∀ j n i, i ≤ N j n → ∫ ω, |Y j n i ω| ∂P ≤ c j n := by
    intro j n i hi
    by_cases h : m * j ≤ n
    · simpa [Y, c, h] using hb j n i h hi
    · simp [Y, c, h]
  have hsum' : Summable fun p : ℕ × ℕ =>
      ((N p.1 p.2 : ℝ) + 1) * (c p.1 p.2 / δ p.1 p.2) := by
    convert hsum using 1
    funext p
    by_cases h : m * p.1 ≤ p.2 <;> simp [c, h]
  have he := LatticeProb.LQG.GMCScaleGrid.ae_eventually_forall_forall_abs_lt
    hδ hY hYb hsum'
  filter_upwards [he] with ω hω
  filter_upwards [hω] with j hj n hn i hi
  simpa [Y, hn] using hj n i hi


/-- Uniform scale increment bounds give almost-sure control over indexed
families of whole-plane fields when the index counts have geometric growth. -/
theorem ae_fine_scale_gff_increment {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    {R : ℝ} (hR : 0 < R) (hgR : ∀ z, g z ≠ 0 → ‖z‖ + 1 ≤ R) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ (A D t B : ℝ), 0 ≤ A → 0 ≤ D → 0 ≤ B →
      0 ≤ t → t < 1 → D * ((2 : ℝ)⁻¹ ^ c) ≤ t ^ 2 →
      ∃ m : ℕ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : ℕ → ℕ → ℕ → Ω → (ℂ → ℝ) → ℝ)
      (H : ℕ → ℕ → ℕ → Ω → ℝ → ℂ → ℝ)
      (_hG : ∀ j n i, LatticeProb.Gauss.IsWholePlaneGFF P (hC j n i) (H j n i))
      (N : ℕ → ℕ → ℕ) (s : ℕ → ℕ → ℕ → ℝ),
      (∀ j n, ((N j n : ℝ) + 1) ≤ B * (A ^ j * D ^ n)) →
      (∀ j n i, LatticeProb.LQG.dyadicScale n / 2 ≤ s j n i ∧
        s j n i ≤ LatticeProb.LQG.dyadicScale n) →
      ∀ᵐ ω ∂P, ∀ᶠ j in atTop, ∀ n, m * j ≤ n → ∀ i ≤ N j n,
        |∫ z, g z * (s j n i ^ (γ ^ 2 / 2) * exp (γ * (H j n i ω (s j n i) z - H j n i ω R 0)) -
          LatticeProb.LQG.dyadicScale n ^ (γ ^ 2 / 2) *
            exp (γ * (H j n i ω (LatticeProb.LQG.dyadicScale n) z - H j n i ω R 0)))| < 1 := by
  obtain ⟨K, c, hK, hc, hinc⟩ := LatticeProb.Gauss.exists_scaleIncrement_bound_uniform hγ hγ2 hgc hgs hR hgR
  refine ⟨K, c, hK, hc, ?_⟩
  intro A D t B hA hD hB ht ht1 hDt
  have hlim : Tendsto (fun m : ℕ => A * t ^ m) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ht ht1).const_mul A
  obtain ⟨m, hm⟩ := eventually_atTop.1 (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  have hsum := (summable_fine_scale_grid hA ht ht1 (hm m le_rfl)).mul_left (K * B)
  refine ⟨m, ?_⟩
  intro Ω _ P hC H hG N s hN hs
  let X : ℕ → ℕ → ℕ → Ω → ℝ := fun j n i ω =>
    ∫ z, g z * (s j n i ^ (γ ^ 2 / 2) * exp (γ * (H j n i ω (s j n i) z - H j n i ω R 0)) -
      LatticeProb.LQG.dyadicScale n ^ (γ ^ 2 / 2) *
        exp (γ * (H j n i ω (LatticeProb.LQG.dyadicScale n) z - H j n i ω R 0)))
  have hd : ∀ n, 0 < LatticeProb.LQG.dyadicScale n := fun n => by
    unfold LatticeProb.LQG.dyadicScale
    positivity
  have hd1 : ∀ n, LatticeProb.LQG.dyadicScale n ≤ 1 := fun n => by
    unfold LatticeProb.LQG.dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hpow : ∀ n, LatticeProb.LQG.dyadicScale n ^ c = (((2 : ℝ)⁻¹) ^ c) ^ n := fun n => by
    rw [LatticeProb.LQG.dyadicScale, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have hsum' : Summable fun p : ℕ × ℕ =>
      if m * p.1 ≤ p.2 then ((N p.1 p.2 : ℝ) + 1) *
        ((K * LatticeProb.LQG.dyadicScale p.2 ^ c) / 1) else 0 := by
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hsum
    · have hp := (hd p.2).le
      split_ifs <;> positivity
    · obtain ⟨j, n⟩ := p
      by_cases h : m * j ≤ n
      · simp only [h, ↓reduceIte, div_one]
        rw [hpow n]
        calc ((N j n : ℝ) + 1) * (K * ((2 : ℝ)⁻¹ ^ c) ^ n)
            ≤ (B * (A ^ j * D ^ n)) * (K * ((2 : ℝ)⁻¹ ^ c) ^ n) := by gcongr; exact hN j n
          _ = (K * B) * (A ^ j * (D * ((2 : ℝ)⁻¹ ^ c)) ^ n) := by rw [mul_pow]; ring
          _ ≤ (K * B) * (A ^ j * (t ^ 2) ^ n) := by gcongr
      · simp [h]
  apply ae_eventually_fine_scale_grid_abs_lt (X := X) (N := N)
    (b := fun _ n => K * LatticeProb.LQG.dyadicScale n ^ c) (δ := fun _ _ => 1)
    (fun _ _ => by norm_num) _ _ hsum'
  · intro j n i _ _
    have hsi : 0 < s j n i := lt_of_lt_of_le (half_pos (hd n)) (hs j n i).1
    exact (hG j n i).integrable_integral_increment_scales hsi (hd n) hR volume
      hgc.measurable (hgc.integrable_of_hasCompactSupport hgs)
      (fun z hz => by linarith [hgR z hz, (hs j n i).2, hd1 n])
      (fun z hz => by linarith [hgR z hz, hd1 n]) γ
  · intro j n i _ _
    exact hinc (hG j n i) _ _ (hd n) (hd1 n) (hs j n i).1 (hs j n i).2


/-- Circle averages in affine coordinates, recentered at the unit circle. -/
noncomputable def affineRecentredCircle (h : ℝ → ℂ → ℝ) (a : ℝ) (z : ℂ)
    (r : ℝ) (w : ℂ) : ℝ :=
  h (a * r) ((a : ℂ) * w + z) - h a z

/-- Fine-scale increment control applies simultaneously to affine rescalings
of one whole-plane field at arbitrary indexed centers. -/
theorem ae_fine_scale_affine_gff_increment {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    {R : ℝ} (hR : 0 < R) (hgR : ∀ z, g z ≠ 0 → ‖z‖ + 1 ≤ R) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ (A D t B : ℝ), 0 ≤ A → 0 ≤ D → 0 ≤ B →
      0 ≤ t → t < 1 → D * ((2 : ℝ)⁻¹ ^ c) ≤ t ^ 2 →
      ∃ m : ℕ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (_hG : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
      (N : ℕ → ℕ → ℕ) (s : ℕ → ℕ → ℕ → ℝ) (z : ℕ → ℕ → ℕ → ℂ),
      (∀ j n, ((N j n : ℝ) + 1) ≤ B * (A ^ j * D ^ n)) →
      (∀ j n i, LatticeProb.LQG.dyadicScale n / 2 ≤ s j n i ∧
        s j n i ≤ LatticeProb.LQG.dyadicScale n) →
      ∀ᵐ ω ∂P, ∀ᶠ j in atTop, ∀ n, m * j ≤ n → ∀ i ≤ N j n,
        |∫ w, g w * (s j n i ^ (γ ^ 2 / 2) * exp (γ *
          (affineRecentredCircle (hcirc ω) (LatticeProb.LQG.dyadicScale j) (z j n i) (s j n i) w -
            affineRecentredCircle (hcirc ω) (LatticeProb.LQG.dyadicScale j) (z j n i) R 0)) -
          LatticeProb.LQG.dyadicScale n ^ (γ ^ 2 / 2) * exp (γ *
          (affineRecentredCircle (hcirc ω) (LatticeProb.LQG.dyadicScale j) (z j n i)
            (LatticeProb.LQG.dyadicScale n) w -
            affineRecentredCircle (hcirc ω) (LatticeProb.LQG.dyadicScale j) (z j n i) R 0)))| < 1 := by
  obtain ⟨K, c, hK, hc, hgrid⟩ := ae_fine_scale_gff_increment hγ hγ2 hgc hgs hR hgR
  refine ⟨K, c, hK, hc, ?_⟩
  intro A D t B hA hD hB ht ht1 hDt
  obtain ⟨m, hm⟩ := hgrid A D t B hA hD hB ht ht1 hDt
  refine ⟨m, ?_⟩
  intro Ω _ P hC hcirc hG N s z hN hs
  let H : ℕ → ℕ → ℕ → Ω → ℝ → ℂ → ℝ := fun j n i ω =>
    affineRecentredCircle (hcirc ω) (LatticeProb.LQG.dyadicScale j) (z j n i)
  have hex : ∀ j n i, ∃ hC', LatticeProb.Gauss.IsWholePlaneGFF P hC' (H j n i) := by
    intro j n i
    have hj : 0 < LatticeProb.LQG.dyadicScale j := by
      unfold LatticeProb.LQG.dyadicScale
      positivity
    have h := LatticeProb.LQG.AffineDerived.wholePlaneGFFAffineInvariance_lp P hC hcirc hG
      (LatticeProb.LQG.dyadicScale j : ℂ) (Complex.ofReal_ne_zero.2 hj.ne') (z j n i)
    have heq : (fun ω r w => hcirc ω (‖(LatticeProb.LQG.dyadicScale j : ℂ)‖ * r)
        ((LatticeProb.LQG.dyadicScale j : ℂ) * w + z j n i) -
        hcirc ω ‖(LatticeProb.LQG.dyadicScale j : ℂ)‖ (z j n i)) = H j n i := by
      funext ω r w
      simp [H, affineRecentredCircle, Complex.norm_real, Real.norm_of_nonneg hj.le]
    rw [heq] at h
    exact ⟨_, h⟩
  choose hC' hH using hex
  exact hm P hC' H hH N s hN hs

end HarmonicBalls
