import LatticeProb.LQG.GMCDilatedGrid
import LatticeProb.LQG.LQGBallMassRatioUniform
import LatticeProb.Gauss.CircleAverageModulusUniform
import LatticeProb.LQG.GMCRatioLimit
import LatticeProb.LQG.GMCContinuumMaximal
import LatticeProb.LQG.LQGOnePieceScaling

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


/-- A bounded disk admits dyadic spatial grids with quadratic cardinality. -/
theorem exists_dyadic_ball_grids (R : ℝ) (hR : 0 < R) :
    ∃ S : ℕ → Finset ℂ, ∀ j,
      ((S j).card : ℝ) ≤ (4 * R + 1) ^ 2 * (4 : ℝ) ^ j ∧
      ∀ z ∈ Metric.ball (0 : ℂ) R, ∃ x ∈ S j,
        dist z x < LatticeProb.LQG.dyadicScale j := by
  have hd (j : ℕ) : 0 < LatticeProb.LQG.dyadicScale j := by
    unfold LatticeProb.LQG.dyadicScale
    positivity
  have hd1 (j : ℕ) : LatticeProb.LQG.dyadicScale j ≤ 1 := by
    unfold LatticeProb.LQG.dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  choose S hcard hcover using fun j =>
    LatticeProb.LQG.LQGBallMassRatioUniform.exists_ball_grid hR (hd j)
  refine ⟨S, fun j => ⟨?_, hcover j⟩⟩
  have hratio : 4 * R / LatticeProb.LQG.dyadicScale j + 1 ≤
      (4 * R + 1) / LatticeProb.LQG.dyadicScale j := by
    rw [add_div]
    have h : (1 : ℝ) ≤ 1 / LatticeProb.LQG.dyadicScale j :=
      (le_div_iff₀ (hd j)).2 (by linarith [hd1 j])
    linarith
  calc
    ((S j).card : ℝ) ≤ (4 * R / LatticeProb.LQG.dyadicScale j + 1) ^ 2 := hcard j
    _ ≤ ((4 * R + 1) / LatticeProb.LQG.dyadicScale j) ^ 2 :=
      pow_le_pow_left₀ (by have := hd j; positivity) hratio 2
    _ = (4 * R + 1) ^ 2 * (4 : ℝ) ^ j := by
      rw [div_pow, LatticeProb.LQG.dyadicScale, ← pow_mul]
      simp only [inv_pow]
      field_simp
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, Nat.mul_comm j 2]


/-- The number of standard radial grid points has geometric growth. -/
theorem radial_grid_count_le {a : ℝ} (ha : 0 ≤ a) (j n : ℕ) :
    ((LatticeProb.LQG.GMCScaleGrid.gridCount a (n + j) : ℝ) + 1) ≤
      2 * ((2 : ℝ)⁻¹ ^ (-(a / 2))) ^ j * ((2 : ℝ)⁻¹ ^ (-(a / 2))) ^ n := by
  let d := LatticeProb.LQG.dyadicScale (n + j)
  have hd : 0 < d := by dsimp [d, LatticeProb.LQG.dyadicScale]; positivity
  have hd1 : d ≤ 1 := by
    dsimp [d, LatticeProb.LQG.dyadicScale]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hone : 1 ≤ d ^ (-(a / 2)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (by linarith)
  have hfloor : (LatticeProb.LQG.GMCScaleGrid.gridCount a (n + j) : ℝ) ≤ d ^ (-(a / 2)) :=
    Nat.floor_le (Real.rpow_pos_of_pos hd _).le
  have hp : d ^ (-(a / 2)) = ((2 : ℝ)⁻¹ ^ (-(a / 2))) ^ (n + j) := by
    dsimp [d, LatticeProb.LQG.dyadicScale]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
  rw [pow_add] at hp
  calc
    _ ≤ 2 * d ^ (-(a / 2)) := by linarith
    _ = _ := by rw [hp]; ring


/-- The product of spatial and radial grid counts has geometric growth. -/
theorem spatial_radial_grid_count_le {a R : ℝ} (ha : 0 ≤ a) (hR : 0 < R)
    {S : ℕ → Finset ℂ}
    (hS : ∀ j, ((S j).card : ℝ) ≤ (4 * R + 1) ^ 2 * (4 : ℝ) ^ j) (j n : ℕ) :
    (((S j).card * (LatticeProb.LQG.GMCScaleGrid.gridCount a (n + j) + 1) : ℕ) : ℝ) + 1 ≤
      (2 * ((4 * R + 1) ^ 2 + 1)) *
        ((4 : ℝ) * ((2 : ℝ)⁻¹ ^ (-(a / 2)))) ^ j *
          ((2 : ℝ)⁻¹ ^ (-(a / 2))) ^ n := by
  let q : ℝ := (2 : ℝ)⁻¹ ^ (-(a / 2))
  have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have h4 : (1 : ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
  have hs : ((S j).card : ℝ) + 1 ≤ ((4 * R + 1) ^ 2 + 1) * (4 : ℝ) ^ j := by
    nlinarith [hS j]
  have hn := radial_grid_count_le ha j n
  change ((LatticeProb.LQG.GMCScaleGrid.gridCount a (n + j) : ℝ) + 1) ≤
    2 * q ^ j * q ^ n at hn
  have hp := mul_le_mul hs hn (by positivity : 0 ≤
    ((LatticeProb.LQG.GMCScaleGrid.gridCount a (n + j) : ℝ) + 1)) (by positivity :
      0 ≤ ((4 * R + 1) ^ 2 + 1) * (4 : ℝ) ^ j)
  have haux : (((S j).card : ℝ) *
      ((LatticeProb.LQG.GMCScaleGrid.gridCount a (n + j) : ℝ) + 1) + 1) ≤
      (((S j).card : ℝ) + 1) *
        ((LatticeProb.LQG.GMCScaleGrid.gridCount a (n + j) : ℝ) + 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (LatticeProb.LQG.GMCScaleGrid.gridCount a (n + j))]
  calc
    _ ≤ (((S j).card : ℝ) + 1) *
        ((LatticeProb.LQG.GMCScaleGrid.gridCount a (n + j) : ℝ) + 1) := by
          push_cast
          exact haux
    _ ≤ (((4 * R + 1) ^ 2 + 1) * (4 : ℝ) ^ j) * (2 * q ^ j * q ^ n) := hp
    _ = _ := by rw [mul_pow]; ring


/-- A finite family of centers and radial indices can be enumerated together. -/
theorem exists_spatial_radial_enumeration (S : ℕ → Finset ℂ) (Q : ℕ → ℕ → ℕ) :
    ∃ z : ℕ → ℕ → ℕ → ℂ, ∃ k : ℕ → ℕ → ℕ → ℕ,
      (∀ j n i, k j n i ≤ Q j n) ∧
      ∀ (j n : ℕ) (x : ℂ), x ∈ S j → ∀ l ≤ Q j n,
        ∃ i ≤ (S j).card * (Q j n + 1), z j n i = x ∧ k j n i = l := by
  classical
  let E : ℕ → ℕ → Finset (ℂ × ℕ) := fun j n => S j ×ˢ Finset.range (Q j n + 1)
  let v : ℕ → ℕ → ℕ → ℂ × ℕ := fun j n i =>
    if h : i < (E j n).card then ((E j n).equivFin.symm ⟨i, h⟩).val else (0, 0)
  refine ⟨fun j n i => (v j n i).1, fun j n i => (v j n i).2, ?_, ?_⟩
  · intro j n i
    by_cases hi : i < (E j n).card
    · have hm := ((E j n).equivFin.symm ⟨i, hi⟩).property
      have hm2 : (((E j n).equivFin.symm ⟨i, hi⟩).val).2 < Q j n + 1 := by
        simpa [E] using (Finset.mem_product.mp hm).2
      simpa [v, hi] using Nat.lt_succ_iff.mp hm2
    · simp [v, hi]
  · intro j n x hx l hl
    have hm : (x, l) ∈ E j n := by simp [E, hx, Nat.lt_succ_iff.mpr hl]
    let i : Fin (E j n).card := (E j n).equivFin ⟨(x, l), hm⟩
    have hi : i.val < (E j n).card := i.isLt
    have hval : v j n i.val = (x, l) := by
      simp [v, hi, i]
    refine ⟨i.val, ?_, ?_, ?_⟩
    · have hc : (E j n).card = (S j).card * (Q j n + 1) := by
        simp [E]
      omega
    · exact congrArg Prod.fst hval
    · exact congrArg Prod.snd hval


open LatticeProb.LQG LatticeProb.LQG.GMCScaleGrid LatticeProb.LQG.GMCRatioLimit

/-- The dyadic spatial grids can be chosen with uniformly bounded centers. -/
theorem exists_bounded_dyadic_ball_grids (R : ℝ) (hR : 0 < R) :
    ∃ S : ℕ → Finset ℂ, ∀ j,
      ((S j).card : ℝ) ≤ (4 * R + 1) ^ 2 * (4 : ℝ) ^ j ∧
      (∀ x ∈ S j, ‖x‖ ≤ R + 1) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) R, ∃ x ∈ S j, dist z x < dyadicScale j := by
  classical
  obtain ⟨S, hS⟩ := exists_dyadic_ball_grids R hR
  refine ⟨fun j => (S j).filter (fun x => ‖x‖ ≤ R + 1), fun j => ⟨?_, ?_, ?_⟩⟩
  · have hc : (((S j).filter (fun x => ‖x‖ ≤ R + 1)).card : ℝ) ≤ (S j).card := by
      exact_mod_cast Finset.card_filter_le (S j) (fun x => ‖x‖ ≤ R + 1)
    exact hc.trans (hS j).1
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro z hz
    obtain ⟨x, hx, hdist⟩ := (hS j).2 z hz
    have hd1 : dyadicScale j ≤ 1 := by
      unfold dyadicScale
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hzR : ‖z‖ < R := by simpa [Metric.mem_ball, dist_zero_right] using hz
    have htri := dist_triangle x z (0 : ℂ)
    rw [dist_zero_right, dist_comm x z, dist_zero_right] at htri
    have hbound : ‖x‖ ≤ R + 1 := by linarith
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hbound⟩, hdist⟩

/-- Fine-scale increments are controlled on concrete spatial and radial grids. -/
theorem ae_fine_scale_affine_gff_increment_on_ball_grid
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g)
    {T : ℝ} (hT : 0 < T) (hgT : ∀ z, g z ≠ 0 → ‖z‖ + 1 ≤ T) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∀ (a t R : ℝ), 0 ≤ a → 0 < R →
      0 ≤ t → t < 1 →
      ((2 : ℝ)⁻¹ ^ (-(a / 2))) * ((2 : ℝ)⁻¹ ^ c) ≤ t ^ 2 →
      ∃ m : ℕ, ∃ S : ℕ → Finset ℂ,
        (∀ j, ((S j).card : ℝ) ≤ (4 * R + 1) ^ 2 * (4 : ℝ) ^ j) ∧
        (∀ j x, x ∈ S j → ‖x‖ ≤ R + 1) ∧
        (∀ j z, z ∈ Metric.ball (0 : ℂ) R →
          ∃ x ∈ S j, dist z x < dyadicScale j) ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
          (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
          LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc →
          ∀ᵐ ω ∂P, ∀ᶠ j in atTop, ∀ n, m * j ≤ n → ∀ x ∈ S j,
            ∀ l ≤ gridCount a (n + j),
              |∫ w, g w *
                (gridScale (fun k => gridCount a (k + j)) n l ^ (γ ^ 2 / 2) * exp (γ *
                  (affineRecentredCircle (hcirc ω) (dyadicScale j) x
                    (gridScale (fun k => gridCount a (k + j)) n l) w -
                   affineRecentredCircle (hcirc ω) (dyadicScale j) x T 0)) -
                 dyadicScale n ^ (γ ^ 2 / 2) * exp (γ *
                  (affineRecentredCircle (hcirc ω) (dyadicScale j) x (dyadicScale n) w -
                   affineRecentredCircle (hcirc ω) (dyadicScale j) x T 0)))| < 1 := by
  obtain ⟨K, c, hK, hc, hgrid⟩ := ae_fine_scale_affine_gff_increment hγ hγ2 hgc hgs hT hgT
  refine ⟨K, c, hK, hc, ?_⟩
  intro a t R ha hR ht ht1 hdecay
  let q : ℝ := (2 : ℝ)⁻¹ ^ (-(a / 2))
  have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨m, hm⟩ := hgrid (4 * q) q t (2 * ((4 * R + 1) ^ 2 + 1))
    (by positivity) hq.le (by positivity) ht ht1 hdecay
  obtain ⟨S, hS⟩ := exists_bounded_dyadic_ball_grids R hR
  refine ⟨m, S, fun j => (hS j).1, fun j x hx => (hS j).2.1 x hx,
    fun j z hz => (hS j).2.2 z hz, ?_⟩
  intro Ω _ P hC hcirc hG
  let Q : ℕ → ℕ → ℕ := fun j n => gridCount a (n + j)
  obtain ⟨z, k, hk, hcover⟩ := exists_spatial_radial_enumeration S Q
  let s : ℕ → ℕ → ℕ → ℝ := fun j n i =>
    gridScale (fun r => gridCount a (r + j)) n (k j n i)
  have hs : ∀ j n i, dyadicScale n / 2 ≤ s j n i ∧ s j n i ≤ dyadicScale n := by
    intro j n i
    exact gridScale_mem_Icc _ (hk j n i)
  have hN : ∀ j n, (((S j).card * (Q j n + 1) : ℕ) : ℝ) + 1 ≤
      (2 * ((4 * R + 1) ^ 2 + 1)) * ((4 * q) ^ j * q ^ n) := by
    intro j n
    simpa only [Q, q, mul_assoc] using
      spatial_radial_grid_count_le ha hR (fun j => (hS j).1) j n
  have he := hm P hC hcirc hG (fun j n => (S j).card * (Q j n + 1)) s z hN hs
  filter_upwards [he] with ω hω
  filter_upwards [hω] with j hj n hn x hx l hl
  obtain ⟨i, hi, hzi, hki⟩ := hcover j n x hx l hl
  have hi0 := hj n hn i hi
  simpa [s, hzi, hki] using hi0



/-- The radial grid can be chosen slowly enough for any positive decay rate. -/
theorem exists_fine_scale_grid_rate {c : ℝ} (hc : 0 < c) :
    ∃ a t : ℝ, 0 < a ∧ 0 ≤ t ∧ t < 1 ∧
      ((2 : ℝ)⁻¹ ^ (-(a / 2))) * ((2 : ℝ)⁻¹ ^ c) ≤ t ^ 2 := by
  refine ⟨c, (2 : ℝ)⁻¹ ^ (c / 4), hc, (Real.rpow_pos_of_pos (by norm_num) _).le,
    Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith), ?_⟩
  apply le_of_eq
  rw [← Real.rpow_add (by norm_num), ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

/-- A common radial modulus holds for all affine fields centered in a fixed
bounded disk, uniformly over dyadic bands and points of the unit cutoff disk. -/
theorem ae_affine_circle_radial_modulus
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {a : ℝ} (ha : 0 < a) (R : ℝ) :
    ∀ᵐ ω ∂P, ∀ᶠ j in atTop, ∀ n : ℕ, ∀ x : ℂ, ‖x‖ ≤ R + 1 →
      ∀ w : ℂ, ‖w‖ ≤ 2 → ∀ s t : ℝ,
        dyadicScale (n + j) / 2 ≤ dyadicScale j * s →
        dyadicScale j * s ≤ dyadicScale (n + j) →
        dyadicScale (n + j) / 2 ≤ dyadicScale j * t →
        dyadicScale j * t ≤ dyadicScale (n + j) →
        |dyadicScale j * s - dyadicScale j * t| <
          dyadicScale (n + j) * dyadicScale (n + j) ^ a →
        |affineRecentredCircle (hcirc ω) (dyadicScale j) x s w -
          affineRecentredCircle (hcirc ω) (dyadicScale j) x t w| ≤ 1 := by
  obtain ⟨β, hβ, hmod⟩ := hh.ae_eventually_abs_circle_sub_le ha (R + 3)
  filter_upwards [hmod] with ω hω
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hω
  refine eventually_atTop.mpr ⟨J, fun j hj n x hx w hw s t h1 h2 h3 h4 h5 => ?_⟩
  have hd0 : 0 ≤ dyadicScale j := (show 0 < dyadicScale j from pow_pos (by norm_num) j).le
  have hd1 : dyadicScale j ≤ 1 := by
    unfold dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hnorm : ‖(dyadicScale j : ℂ) * w + x‖ ≤ R + 3 := by
    have hm : ‖(dyadicScale j : ℂ) * w‖ ≤ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hd0]
      nlinarith [norm_nonneg w]
    linarith [norm_add_le ((dyadicScale j : ℂ) * w) x]
  have h := hJ (n + j) (by omega) _ hnorm _ _ h1 h2 h3 h4 h5
  have hpow : dyadicScale (n + j) ^ β ≤ 1 :=
    Real.rpow_le_one (show 0 < dyadicScale (n + j) from pow_pos (by norm_num) _).le
      (by unfold dyadicScale; exact pow_le_one₀ (by norm_num) (by norm_num)) hβ.le
  apply le_trans ?_ hpow
  simpa only [affineRecentredCircle, sub_sub_sub_cancel_right] using h

/-- A radial grid point in the same dyadic band lies within the mesh required
by the circle-average modulus after affine rescaling. -/
theorem exists_fine_scale_grid_near {a : ℝ} (ha : 0 < a) {j n : ℕ}
    (hj : 1 ≤ j) {t : ℝ} (ht1 : dyadicScale n / 2 ≤ t)
    (ht2 : t ≤ dyadicScale n) :
    ∃ i ≤ gridCount a (n + j),
      dyadicScale (n + j) / 2 ≤ dyadicScale j * t ∧
      dyadicScale j * t ≤ dyadicScale (n + j) ∧
      dyadicScale (n + j) / 2 ≤
        dyadicScale j * gridScale (fun k => gridCount a (k + j)) n i ∧
      dyadicScale j * gridScale (fun k => gridCount a (k + j)) n i ≤
        dyadicScale (n + j) ∧
      |dyadicScale j * t -
        dyadicScale j * gridScale (fun k => gridCount a (k + j)) n i| <
          dyadicScale (n + j) * dyadicScale (n + j) ^ (a / 4) := by
  have hdj : 0 < dyadicScale j := pow_pos (by norm_num) j
  obtain ⟨hN, hmesh⟩ := one_le_gridCount_and_mesh_le ha.le (n + j)
  obtain ⟨i, hi, hti⟩ := exists_gridScale_near
    (fun k => gridCount a (k + j)) hN ht1 ht2
  obtain ⟨hs1, hs2⟩ := gridScale_mem_Icc (fun k => gridCount a (k + j)) hi
  have hk : dyadicScale (n + j) = dyadicScale j * dyadicScale n := by
    rw [add_comm]; exact dyadicScale_add j n
  have hk0 : 0 < dyadicScale (n + j) := pow_pos (by norm_num) _
  have hk1 : dyadicScale (n + j) < 1 := by
    unfold dyadicScale
    exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  refine ⟨i, hi, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hk, mul_div_assoc]; exact mul_le_mul_of_nonneg_left ht1 hdj.le
  · rw [hk]; exact mul_le_mul_of_nonneg_left ht2 hdj.le
  · rw [hk, mul_div_assoc]; exact mul_le_mul_of_nonneg_left hs1 hdj.le
  · rw [hk]; exact mul_le_mul_of_nonneg_left hs2 hdj.le
  · rw [← mul_sub, abs_mul, abs_of_pos hdj]
    calc
      dyadicScale j * |t - gridScale (fun k => gridCount a (k + j)) n i| ≤
          dyadicScale j * (dyadicScale n / (2 * gridCount a (n + j))) :=
        mul_le_mul_of_nonneg_left hti hdj.le
      _ = dyadicScale (n + j) / (2 * gridCount a (n + j)) := by rw [hk]; ring
      _ ≤ dyadicScale (n + j) * dyadicScale (n + j) ^ (a / 2) := hmesh
      _ < dyadicScale (n + j) * dyadicScale (n + j) ^ (a / 4) :=
        mul_lt_mul_of_pos_left (Real.rpow_lt_rpow_of_exponent_gt hk0 hk1 (by linarith)) hk0

/-- On one field event, a nearby radial grid point controls all affine
circle averages on the cutoff disk, uniformly over bounded centers. -/
theorem ae_fine_scale_grid_circle_comparison
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {a : ℝ} (ha : 0 < a) (R : ℝ) :
    ∀ᵐ ω ∂P, ∀ᶠ j in atTop, ∀ n : ℕ, ∀ t : ℝ,
      dyadicScale n / 2 ≤ t → t ≤ dyadicScale n →
      ∃ i ≤ gridCount a (n + j), ∀ x : ℂ, ‖x‖ ≤ R + 1 →
        ∀ w : ℂ, ‖w‖ ≤ 2 →
          |affineRecentredCircle (hcirc ω) (dyadicScale j) x t w -
            affineRecentredCircle (hcirc ω) (dyadicScale j) x
              (gridScale (fun k => gridCount a (k + j)) n i) w| ≤ 1 := by
  filter_upwards [ae_affine_circle_radial_modulus hh (a := a / 4) (div_pos ha (by norm_num)) R] with ω hω
  filter_upwards [hω, eventually_ge_atTop 1] with j hj hj1 n t ht1 ht2
  obtain ⟨i, hi, h1, h2, h3, h4, h5⟩ := exists_fine_scale_grid_near ha hj1 ht1 ht2
  exact ⟨i, hi, fun x hx w hw => hj n x hx w hw _ _ h1 h2 h3 h4 h5⟩

open ProbabilityTheory Function Topology Metric Set
open scoped ENNReal NNReal
open LatticeProb LatticeProb.Gauss LatticeProb.LQG LatticeProb.LQG.GMCScaleSandwich
  LatticeProb.LQG.GMCContinuumMaximal

/-- A grid comparison in one dyadic band controls the ball mass at every
nearby scale by the mass at that band's upper endpoint. The proof adapts
LatticeProb.LQG.GMCContinuumMaximal.lqgApprox_ball_le_of_grid. -/
theorem lqgApprox_ball_le_of_band_grid {γ E t s : ℝ} {n : ℕ}
    {H : ℝ → ℂ → ℝ} (hγ : 0 < γ)
    (hcont : ∀ r, 0 < r → Continuous (H r))
    (hn1 : dyadicScale n / 2 ≤ t) (hn2 : t ≤ dyadicScale n)
    (hs1 : dyadicScale n / 2 ≤ s) (hs2 : s ≤ dyadicScale n)
    (hη : ∀ z, Gauss.ballCutoff z ≠ 0 → |H t z - H s z| ≤ 1)
    (hgi : |∫ z, Gauss.ballCutoff z *
      (s ^ (γ ^ 2 / 2) * rexp (γ * (H s z - H 4 0)) -
       dyadicScale n ^ (γ ^ 2 / 2) * rexp (γ * (H (dyadicScale n) z - H 4 0)))| < E) :
    lqgApprox γ H t (ball 0 1) ≤
      ENNReal.ofReal (rexp (γ ^ 2 / 2 * Real.log 2 + γ)) *
        (lqgApprox γ H (dyadicScale n) (ball 0 2) +
          ENNReal.ofReal (rexp (γ * H 4 0) * E)) := by
  have hdn : 0 < dyadicScale n := pow_pos (by norm_num) n
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) hn1
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs1
  have hint : ∀ r, 0 < r →
      Integrable (fun z => Gauss.ballCutoff z * (r ^ (γ ^ 2 / 2) * rexp (γ * (H r z - H 4 0)))) :=
    fun r hr => (Gauss.ballCutoff_continuous.mul (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul ((hcont r hr).sub continuous_const))))).integrable_of_hasCompactSupport
      Gauss.ballCutoff_hasCompactSupport.mul_right
  have hHc := hcont
  have hE : 0 ≤ E := (abs_nonneg _).trans hgi.le
  have hlog : |Real.log t - Real.log s| ≤ Real.log 2 := by
    have h1 : Real.log t ≤ Real.log (dyadicScale n) := Real.log_le_log ht0 hn2
    have h2 : Real.log s ≤ Real.log (dyadicScale n) := Real.log_le_log hs0 hs2
    have h3 : Real.log (dyadicScale n / 2) ≤ Real.log t := Real.log_le_log (by positivity) hn1
    have h4 : Real.log (dyadicScale n / 2) ≤ Real.log s := Real.log_le_log (by positivity) hs1
    rw [Real.log_div hdn.ne' two_ne_zero] at h3 h4
    rw [abs_le]; constructor <;> linarith
  have hcmp := abs_integral_recentred_sub_le (μ := volume) (γ := γ) (η := 1) (H₀ := H 4 0) ht0 hs0 hη
    (hint t ht0) (hint s hs0)
  have habs : ∫ z, |Gauss.ballCutoff z| * (s ^ (γ ^ 2 / 2) * rexp (γ * (H s z - H 4 0))) =
      ∫ z, Gauss.ballCutoff z * (s ^ (γ ^ 2 / 2) * rexp (γ * (H s z - H 4 0))) := by
    congr 1; funext z; rw [abs_of_nonneg (Gauss.ballCutoff_nonneg z)]
  rw [habs] at hcmp
  have hsplit : (∫ z, Gauss.ballCutoff z * (s ^ (γ ^ 2 / 2) * rexp (γ * (H s z - H 4 0)))) -
      ∫ z, Gauss.ballCutoff z * (dyadicScale n ^ (γ ^ 2 / 2) * rexp (γ * (H (dyadicScale n) z - H 4 0))) =
      ∫ z, Gauss.ballCutoff z * (s ^ (γ ^ 2 / 2) * rexp (γ * (H s z - H 4 0)) -
        dyadicScale n ^ (γ ^ 2 / 2) * rexp (γ * (H (dyadicScale n) z - H 4 0))) := by
    rw [← integral_sub (hint s hs0) (hint _ hdn)]
    congr 1; funext z; ring
  rw [← hsplit] at hgi
  set It := ∫ z, Gauss.ballCutoff z * (t ^ (γ ^ 2 / 2) * rexp (γ * (H t z - H 4 0))) with hIt
  set Is := ∫ z, Gauss.ballCutoff z * (s ^ (γ ^ 2 / 2) * rexp (γ * (H s z - H 4 0))) with hIs
  set Id := ∫ z, Gauss.ballCutoff z * (dyadicScale n ^ (γ ^ 2 / 2) *
    rexp (γ * (H (dyadicScale n) z - H 4 0))) with hId
  have hIs0 : 0 ≤ Is := integral_nonneg fun z => mul_nonneg (Gauss.ballCutoff_nonneg z) (by positivity)
  have hId0 : 0 ≤ Id := integral_nonneg fun z => mul_nonneg (Gauss.ballCutoff_nonneg z) (by positivity)
  have hexp : rexp (γ ^ 2 / 2 * |Real.log t - Real.log s| + |γ| * 1) ≤
      rexp (γ ^ 2 / 2 * Real.log 2 + γ) := by
    rw [abs_of_pos hγ, mul_one]
    have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ γ ^ 2 / 2)
    exact Real.exp_le_exp.mpr (by linarith)
  have hc0 := Real.exp_pos (γ ^ 2 / 2 * Real.log 2 + γ)
  have hIt_le : It ≤ rexp (γ ^ 2 / 2 * Real.log 2 + γ) * Is := by
    have h1 := (abs_le.mp hcmp).2
    have h2 := mul_le_mul_of_nonneg_right hexp hIs0
    linarith
  have hIs_le : Is ≤ Id + E := by linarith [(abs_lt.mp hgi).2]
  have hball := Gauss.lqgApprox_ball_le (γ := γ) (h := H) 4 ht0 (hHc t ht0)
  have hd2 := ofReal_exp_mul_integral_ballCutoff_le (γ := γ) (H := H) 4 hdn (hHc _ hdn)
  refine hball.trans ?_
  have he0 := Real.exp_pos (γ * H 4 0)
  have hreal : rexp (γ * H 4 0) * It ≤
      rexp (γ ^ 2 / 2 * Real.log 2 + γ) * (rexp (γ * H 4 0) * Id + rexp (γ * H 4 0) * E) := by
    calc rexp (γ * H 4 0) * It ≤ rexp (γ * H 4 0) * (rexp (γ ^ 2 / 2 * Real.log 2 + γ) * (Id + E)) :=
          mul_le_mul_of_nonneg_left (hIt_le.trans (mul_le_mul_of_nonneg_left hIs_le hc0.le)) he0.le
      _ = rexp (γ ^ 2 / 2 * Real.log 2 + γ) * (rexp (γ * H 4 0) * Id + rexp (γ * H 4 0) * E) := by ring
  refine (ENNReal.ofReal_le_ofReal hreal).trans ?_
  rw [ENNReal.ofReal_mul hc0.le, ENNReal.ofReal_add (mul_nonneg he0.le hId0) (mul_nonneg he0.le hE)]
  gcongr


/-- At sufficiently fine scales, the mass in each grid cell is controlled by
the mass at the upper endpoint of the same radial band and a recentred error.
The estimate is simultaneous over all cells and all radii in those bands. -/
theorem ae_fine_scale_affine_ball_le_band
    {γ R : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hR : 0 < R) :
    ∃ m : ℕ, ∃ S : ℕ → Finset ℂ,
      (∀ j x, x ∈ S j → ‖x‖ ≤ R + 1) ∧
      (∀ j z, z ∈ Metric.ball (0 : ℂ) R →
        ∃ x ∈ S j, dist z x < dyadicScale j) ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc →
        ∀ᵐ ω ∂P, ∀ᶠ j in atTop, ∀ n, m * j ≤ n → ∀ x ∈ S j,
          ∀ t, dyadicScale n / 2 ≤ t → t ≤ dyadicScale n →
            lqgApprox γ (affineRecentredCircle (hcirc ω) (dyadicScale j) x) t (ball 0 1) ≤
              ENNReal.ofReal (rexp (γ ^ 2 / 2 * Real.log 2 + γ)) *
                (lqgApprox γ (affineRecentredCircle (hcirc ω) (dyadicScale j) x)
                    (dyadicScale n) (ball 0 2) +
                  ENNReal.ofReal (rexp (γ *
                    affineRecentredCircle (hcirc ω) (dyadicScale j) x 4 0))) := by
  have hg : ∀ z, Gauss.ballCutoff z ≠ 0 → ‖z‖ + 1 ≤ (4 : ℝ) := by
    intro z hz
    have hz2 : ‖z‖ < 2 := by
      by_contra h
      exact hz (Gauss.ballCutoff_eq_zero (not_lt.mp h))
    linarith
  obtain ⟨K, c, hK, hc, hinc⟩ :=
    ae_fine_scale_affine_gff_increment_on_ball_grid hγ hγ2
      Gauss.ballCutoff_continuous Gauss.ballCutoff_hasCompactSupport (by norm_num : (0 : ℝ) < 4) hg
  obtain ⟨a, q, ha, hq, hq1, hdec⟩ := exists_fine_scale_grid_rate hc
  obtain ⟨m, S, hcard, hbound, hcover, hgrid⟩ := hinc a q R ha.le hR hq hq1 hdec
  refine ⟨m, S, hbound, hcover, ?_⟩
  intro Ω _ P hC hcirc hh
  filter_upwards [hgrid P hC hcirc hh, ae_fine_scale_grid_circle_comparison hh ha R,
    hh.ae_continuousOn_circle] with ω hgridω hmodω hcontω
  filter_upwards [hgridω, hmodω] with j hj hmj n hn x hx t ht1 ht2
  obtain ⟨i, hi, hmod⟩ := hmj n t ht1 ht2
  have hs := gridScale_mem_Icc (fun k => gridCount a (k + j)) hi
  have hη : ∀ z, Gauss.ballCutoff z ≠ 0 →
      |affineRecentredCircle (hcirc ω) (dyadicScale j) x t z -
        affineRecentredCircle (hcirc ω) (dyadicScale j) x
          (gridScale (fun k => gridCount a (k + j)) n i) z| ≤ 1 := by
    intro z hz
    have hz2 : ‖z‖ ≤ 2 := by
      by_contra h
      exact hz (Gauss.ballCutoff_eq_zero (not_le.mp h).le)
    exact hmod x (hbound j x hx) z hz2
  have hcont : ∀ r, 0 < r →
      Continuous (affineRecentredCircle (hcirc ω) (dyadicScale j) x r) := by
    intro r hr
    have hd : 0 < dyadicScale j := pow_pos (by norm_num) j
    have hslice := LatticeProb.LQG.GMCRatioLimit.continuous_slice hcontω (mul_pos hd hr)
    exact (hslice.comp ((continuous_const.mul continuous_id).add continuous_const)).sub continuous_const
  have h := lqgApprox_ball_le_of_band_grid hγ hcont ht1 ht2 hs.1 hs.2 hη (hj n hn x hx i hi)
  simpa only [mul_one] using h


/-- The affine band comparison, expressed for the original field and balls
at the spatial grid scale. -/
theorem ae_fine_scale_ball_le_band
    {γ R : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hR : 0 < R) :
    ∃ m : ℕ, ∃ S : ℕ → Finset ℂ,
      (∀ j x, x ∈ S j → ‖x‖ ≤ R + 1) ∧
      (∀ j z, z ∈ Metric.ball (0 : ℂ) R →
        ∃ x ∈ S j, dist z x < dyadicScale j) ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc →
        ∀ᵐ ω ∂P, ∀ᶠ j in atTop, ∀ n, m * j ≤ n → ∀ x ∈ S j,
          ∀ t, dyadicScale n / 2 ≤ t → t ≤ dyadicScale n →
            lqgApprox γ (hcirc ω) (dyadicScale j * t) (ball x (dyadicScale j)) ≤
              ENNReal.ofReal (rexp (γ ^ 2 / 2 * Real.log 2 + γ)) *
                (lqgApprox γ (hcirc ω) (dyadicScale j * dyadicScale n)
                    (ball x (dyadicScale j * 2)) +
                  LQGDyadicScaling.dyadicFactor γ j (hcirc ω (dyadicScale j) x) *
                    ENNReal.ofReal (rexp (γ *
                      affineRecentredCircle (hcirc ω) (dyadicScale j) x 4 0))) := by
  obtain ⟨m, S, hb, hc, h⟩ := ae_fine_scale_affine_ball_le_band hγ hγ2 hR
  refine ⟨m, S, hb, hc, ?_⟩
  intro Ω _ P hC hcirc hh
  filter_upwards [h P hC hcirc hh] with ω hω
  filter_upwards [hω] with j hj n hn x hx t ht1 ht2
  have ht : 0 ≤ t := le_trans (div_nonneg (show 0 ≤ dyadicScale n from (pow_pos (by norm_num) n).le) (by norm_num)) ht1
  have hd : 0 ≤ dyadicScale n := (show 0 < dyadicScale n from pow_pos (by norm_num) n).le
  have hscale := lqgApprox_ball_dyadic hγ.ne' (hcirc ω) j x ht 1
  have hscale' := lqgApprox_ball_dyadic hγ.ne' (hcirc ω) j x hd 2
  simp only [mul_one] at hscale
  change lqgApprox γ (hcirc ω) (dyadicScale j * t) (ball x (dyadicScale j)) =
    LQGDyadicScaling.dyadicFactor γ j (hcirc ω (dyadicScale j) x) *
      lqgApprox γ (affineRecentredCircle (hcirc ω) (dyadicScale j) x) t (ball 0 1) at hscale
  change lqgApprox γ (hcirc ω) (dyadicScale j * dyadicScale n) (ball x (dyadicScale j * 2)) =
    LQGDyadicScaling.dyadicFactor γ j (hcirc ω (dyadicScale j) x) *
      lqgApprox γ (affineRecentredCircle (hcirc ω) (dyadicScale j) x) (dyadicScale n) (ball 0 2) at hscale'
  rw [hscale]
  calc
    _ ≤ LQGDyadicScaling.dyadicFactor γ j (hcirc ω (dyadicScale j) x) *
        (ENNReal.ofReal (rexp (γ ^ 2 / 2 * Real.log 2 + γ)) *
          (lqgApprox γ (affineRecentredCircle (hcirc ω) (dyadicScale j) x)
            (dyadicScale n) (ball 0 2) +
           ENNReal.ofReal (rexp (γ * affineRecentredCircle (hcirc ω) (dyadicScale j) x 4 0)))) :=
      mul_le_mul_right (hj n hn x hx t ht1 ht2) _
    _ = ENNReal.ofReal (rexp (γ ^ 2 / 2 * Real.log 2 + γ)) *
        (lqgApprox γ (hcirc ω) (dyadicScale j * dyadicScale n) (ball x (dyadicScale j * 2)) +
          LQGDyadicScaling.dyadicFactor γ j (hcirc ω (dyadicScale j) x) *
            ENNReal.ofReal (rexp (γ * affineRecentredCircle (hcirc ω) (dyadicScale j) x 4 0))) := by
      rw [hscale']
      simp only [mul_add]
      ac_rfl

end HarmonicBalls
