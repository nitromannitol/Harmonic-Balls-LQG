import HarmonicBalls.Proofs.Potential.LQGClockAnnularGridOccupationIncrement
import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveUniformL1
import LatticeProb.LQG.GMCRatioLimit
import LatticeProb.LQG.LQGBallMassGrid2

/-! # Radial regularity of inserted circle averages

The insertion correction has a uniform radial modulus down to the origin.
-/

open MeasureTheory Filter LatticeProb.LQG MarkovProcess Set
open LatticeProb.LQG.GMCScaleGrid LatticeProb.LQG.GMCRatioLimit
open scoped Topology NNReal ENNReal

namespace HarmonicBalls

/-- The logarithmic insertion correction is Lipschitz in the radius above a
positive lower bound, uniformly in the spatial argument. -/
theorem abs_log_max_sub_log_max_le {a s t : ℝ} (ha : 0 < a)
    (hs : a ≤ s) (ht : a ≤ t) (u : ℝ) :
    |Real.log (max s u) - Real.log (max t u)| ≤ |s - t| / a := by
  let S := max s u
  let T := max t u
  have hS : a ≤ S := hs.trans (le_max_left _ _)
  have hT : a ≤ T := ht.trans (le_max_left _ _)
  have hS0 : 0 < S := ha.trans_le hS
  have hT0 : 0 < T := ha.trans_le hT
  have hmax : |S - T| ≤ |s - t| := abs_max_sub_max_le_abs s t u
  have hlog (x y : ℝ) (hx : a ≤ x) (hy : a ≤ y) (hxy : x ≤ y) :
      Real.log y - Real.log x ≤ (y - x) / a := by
    have hx0 : 0 < x := ha.trans_le hx
    have hy0 : 0 < y := ha.trans_le hy
    have h := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [Real.log_div hy0.ne' hx0.ne'] at h
    have heq : y / x - 1 = (y - x) / x := by field_simp
    rw [heq] at h
    exact h.trans (div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) ha hx)
  rcases le_total S T with hST | hTS
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hS0 hST))]
    have hm : T - S ≤ |s - t| := by
      have := hmax
      rw [abs_of_nonpos (sub_nonpos.mpr hST)] at this
      linarith
    calc
      -(Real.log S - Real.log T) = Real.log T - Real.log S := by ring
      _ ≤ (T - S) / a := hlog S T hS hT hST
      _ ≤ |s - t| / a := div_le_div_of_nonneg_right hm ha.le
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hT0 hTS))]
    have hm : S - T ≤ |s - t| := by
      simpa [abs_of_nonneg (sub_nonneg.mpr hTS)] using hmax
    exact (hlog T S hT hS hTS).trans (div_le_div_of_nonneg_right hm ha.le)

/-- The inserted circle average has a radial modulus uniformly on the closed
half-disc, including the origin. -/
theorem ae_eventually_inserted_halfDisc_circle_radial_modulus
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (α : ℝ)
    {a : ℝ} (ha : 0 < a) :
    ∃ β : ℝ, 0 < β ∧ ∀ᵐ ω ∂P, ∀ᶠ k in atTop,
      ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → ∀ s t : ℝ,
        dyadicScale k / 2 ≤ s → s ≤ dyadicScale k →
        dyadicScale k / 2 ≤ t → t ≤ dyadicScale k →
        |s - t| < dyadicScale k * dyadicScale k ^ a →
        |LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) s z -
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) t z| ≤
          dyadicScale k ^ β + 2 * |α| * dyadicScale k ^ a := by
  obtain ⟨β, hβ, hmod⟩ := hh.ae_eventually_abs_circle_sub_le ha (1 / 2)
  refine ⟨β, hβ, ?_⟩
  filter_upwards [hmod, ae_recentered_inserted_circle_average hh α] with ω hmod hrec
  filter_upwards [hmod] with k hk z hz s t hs1 hs2 ht1 ht2 hst
  have hd : 0 < dyadicScale k := dyadicScale_pos k
  have hs : 0 < s := (half_pos hd).trans_le hs1
  have ht : 0 < t := (half_pos hd).trans_le ht1
  have hlog : |Real.log (max s ‖z‖) - Real.log (max t ‖z‖)| ≤
      2 * dyadicScale k ^ a := by
    calc
      _ ≤ |s - t| / (dyadicScale k / 2) :=
        abs_log_max_sub_log_max_le (half_pos hd) hs1 ht1 ‖z‖
      _ ≤ 2 * dyadicScale k ^ a := by
        rw [div_le_iff₀ (half_pos hd)]
        nlinarith [hst.le]
  have hf := hk z hz s t hs1 hs2 ht1 ht2 hst
  rw [← hrec s z hs, ← hrec t z ht]
  have heq : hcirc ω s z - hcirc ω 1 0 - α * Real.log (max s ‖z‖) -
      (hcirc ω t z - hcirc ω 1 0 - α * Real.log (max t ‖z‖)) =
      (hcirc ω s z - hcirc ω t z) -
        α * (Real.log (max s ‖z‖) - Real.log (max t ‖z‖)) := by ring
  rw [heq]
  calc
    _ ≤ |hcirc ω s z - hcirc ω t z| +
        |α| * |Real.log (max s ‖z‖) - Real.log (max t ‖z‖)| := by
      simpa only [abs_mul] using abs_sub (hcirc ω s z - hcirc ω t z)
        (α * (Real.log (max s ‖z‖) - Real.log (max t ‖z‖)))
    _ ≤ dyadicScale k ^ β + 2 * |α| * dyadicScale k ^ a := by
      calc
        _ ≤ dyadicScale k ^ β + |α| * (2 * dyadicScale k ^ a) :=
          add_le_add hf (mul_le_mul_of_nonneg_left hlog (abs_nonneg α))
        _ = _ := by ring

/-- Normalized inserted densities at nearby radii are relatively close
uniformly on the closed half-disc. -/
theorem ae_eventually_halfDisc_density_radial_difference_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (α γ : ℝ)
    {a : ℝ} (ha : 0 < a) :
    ∃ β : ℝ, 0 < β ∧ ∀ᵐ ω ∂P, ∀ᶠ k in atTop,
      ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → ∀ s t : ℝ,
        dyadicScale k / 2 ≤ s → s ≤ dyadicScale k →
        dyadicScale k / 2 ≤ t → t ≤ dyadicScale k →
        |s - t| < dyadicScale k * dyadicScale k ^ a →
        let B := |γ| * (dyadicScale k ^ β + 2 * |α| * dyadicScale k ^ a) +
          γ ^ 2 * dyadicScale k ^ a
        |s ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) s z) -
          t ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) t z)| ≤
          B * Real.exp B * (t ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) t z)) := by
  obtain ⟨β, hβ, hmod⟩ := ae_eventually_inserted_halfDisc_circle_radial_modulus hh α ha
  refine ⟨β, hβ, ?_⟩
  filter_upwards [hmod] with ω hω
  filter_upwards [hω] with k hk z hz s t hs1 hs2 ht1 ht2 hst
  have hd : 0 < dyadicScale k := dyadicScale_pos k
  have hs : 0 < s := (half_pos hd).trans_le hs1
  have ht : 0 < t := (half_pos hd).trans_le ht1
  have hlog : |Real.log s - Real.log t| ≤ 2 * dyadicScale k ^ a := by
    have h := abs_log_max_sub_log_max_le (half_pos hd) hs1 ht1 0
    rw [max_eq_left hs.le, max_eq_left ht.le] at h
    calc
      _ ≤ |s - t| / (dyadicScale k / 2) := h
      _ ≤ 2 * dyadicScale k ^ a := by
        rw [div_le_iff₀ (half_pos hd)]
        nlinarith [hst.le]
  have hf := hk z hz s t hs1 hs2 ht1 ht2 hst
  let B : ℝ := |γ| * (dyadicScale k ^ β + 2 * |α| * dyadicScale k ^ a) +
    γ ^ 2 * dyadicScale k ^ a
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply abs_normalized_exp_sub_le hs ht hB
  calc
    _ ≤ |Real.log s - Real.log t| * |γ ^ 2 / 2| +
        |γ| * |LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) s z -
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) t z| := by
      have htriangle := abs_add_le
        ((Real.log s - Real.log t) * (γ ^ 2 / 2))
        (γ * (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) s z -
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) t z))
      rw [abs_mul, abs_mul] at htriangle
      exact htriangle
    _ ≤ B := by
      have hγ : 0 ≤ γ ^ 2 / 2 := by positivity
      rw [abs_of_nonneg hγ]
      dsimp [B]
      nlinarith [mul_le_mul_of_nonneg_right hlog hγ,
        mul_le_mul_of_nonneg_left hf (abs_nonneg γ)]

/-- Nearby smoothing radii give relatively close half-disc occupation clocks,
uniformly over paths and nonnegative finite times. -/
theorem ae_eventually_halfDisc_clock_radial_difference_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (α γ : ℝ)
    {a : ℝ} (ha : 0 < a) :
    ∃ β : ℝ, 0 < β ∧ ∀ᵐ ω ∂P, ∀ᶠ k in atTop,
      ∀ (b : ContinuousPath ℂ) (T : ℝ≥0) (s t : ℝ),
        dyadicScale k / 2 ≤ s → s ≤ dyadicScale k →
        dyadicScale k / 2 ≤ t → t ≤ dyadicScale k →
        |s - t| < dyadicScale k * dyadicScale k ^ a →
        let B := |γ| * (dyadicScale k ^ β + 2 * |α| * dyadicScale k ^ a) +
          γ ^ 2 * dyadicScale k ^ a
        let A : ℝ → ℝ := fun v => ∫ u in (0 : ℝ)..(T : ℝ),
          {z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z =>
            v ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) v z)) (b u.toNNReal)
        |A s - A t| ≤ B * Real.exp B * A t := by
  obtain ⟨β, hβ, hmod⟩ := ae_eventually_halfDisc_density_radial_difference_le hh α γ ha
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  refine ⟨β, hβ, ?_⟩
  filter_upwards [hmod, hHae, ae_recentered_inserted_circle_average hh α] with ω hω hH hrec
  have hcont : ∀ r, 0 < r → Continuous (fun z : ℂ => r ^ (γ ^ 2 / 2) *
      Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)) := by
    intro r hr
    have hc : Continuous (hcirc ω r) := by
      rw [← funext (hH r)]
      exact hHc ω r hr
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) =
        fun z => hcirc ω r z - hcirc ω 1 0 - α * Real.log (max r ‖z‖) := by
      funext z
      exact (hrec r z hr).symm
    have hci : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) := by
      rw [heq]
      exact (hc.sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hr).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hci))
  filter_upwards [hω] with k hk b T s t hs1 hs2 ht1 ht2 hst
  have hs : 0 < s := (half_pos (dyadicScale_pos k)).trans_le hs1
  have ht : 0 < t := (half_pos (dyadicScale_pos k)).trans_le ht1
  have hset : {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2} =
      {z : ℂ | ‖z‖ ≤ 1 / 2} := by
    ext z
    simp only [Set.mem_ofPred_eq, norm_nonneg, true_and]
  have h := abs_annular_occupation_sub_le
    (fun z => s ^ (γ ^ 2 / 2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) s z))
    (fun z => t ^ (γ ^ 2 / 2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) t z))
    (hcont s hs) (hcont t ht) 0
    ((|γ| * (dyadicScale k ^ β + 2 * |α| * dyadicScale k ^ a) +
      γ ^ 2 * dyadicScale k ^ a) * Real.exp
        (|γ| * (dyadicScale k ^ β + 2 * |α| * dyadicScale k ^ a) +
          γ ^ 2 * dyadicScale k ^ a))
    (fun z _ hz => hk z hz s t hs1 hs2 ht1 ht2 hst) b T.coe_nonneg
  simpa only [hset] using h

/-- Every smoothing radius in a sufficiently small dyadic shell has a grid
radius with a relatively close half-disc clock for every path and horizon. -/
theorem ae_eventually_halfDisc_clock_grid_comparison
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (α γ : ℝ)
    {c : ℝ} (hc : 0 < c) :
    ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
      ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ s : ℝ,
        dyadicScale k / 2 ≤ s → s ≤ dyadicScale k →
        ∃ i ≤ gridCount c k, ∀ (b : ContinuousPath ℂ) (T : ℝ≥0),
          let r := gridScale (gridCount c) k i
          let A : ℝ → ℝ := fun v => ∫ u in (0 : ℝ)..(T : ℝ),
            {z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z =>
              v ^ (γ ^ 2 / 2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) v z)) (b u.toNNReal)
          |A s - A r| ≤ η k * A r := by
  obtain ⟨β, hβ, hmod⟩ :=
    ae_eventually_halfDisc_clock_radial_difference_le hh α γ (show 0 < c / 4 by positivity)
  let B : ℕ → ℝ := fun k =>
    |γ| * (dyadicScale k ^ β + 2 * |α| * dyadicScale k ^ (c / 4)) +
      γ ^ 2 * dyadicScale k ^ (c / 4)
  have hpow (p : ℝ) (hp : 0 < p) : Tendsto (fun k => dyadicScale k ^ p) atTop (𝓝 0) := by
    have h0 : Tendsto dyadicScale atTop (𝓝 (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [Real.zero_rpow hp.ne'] using h0.rpow_const (Or.inr hp.le)
  have hB : Tendsto B atTop (𝓝 0) := by
    dsimp [B]
    simpa using (((hpow β hβ).add ((hpow (c / 4) (by positivity)).const_mul (2 * |α|))).const_mul |γ|).add
      ((hpow (c / 4) (by positivity)).const_mul (γ ^ 2))
  refine ⟨fun k => B k * Real.exp (B k), ?_, ?_⟩
  · simpa using hB.mul ((Real.continuous_exp.tendsto 0).comp hB)
  · filter_upwards [hmod] with ω hω
    filter_upwards [hω, eventually_ge_atTop 1] with k hk hk1 s hs1 hs2
    have he : 0 < dyadicScale k := dyadicScale_pos k
    have helt : dyadicScale k < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    obtain ⟨hN, hmesh⟩ := one_le_gridCount_and_mesh_le hc.le k
    obtain ⟨i, hi, hnear⟩ := exists_gridScale_near (gridCount c) hN hs1 hs2
    obtain ⟨hr1, hr2⟩ := gridScale_mem_Icc (gridCount c) hi
    have hclose : |s - gridScale (gridCount c) k i| < dyadicScale k * dyadicScale k ^ (c / 4) :=
      (hnear.trans hmesh).trans_lt (mul_lt_mul_of_pos_left
        (Real.rpow_lt_rpow_of_exponent_gt he helt (by linarith)) he)
    refine ⟨i, hi, ?_⟩
    intro b T
    exact hk b T s _ hs1 hs2 hr1 hr2 hclose

/-- The nonpositive insertion increment separates into a weighted zero-insertion
increment and a correction supported inside the larger smoothing ball. -/
theorem nonpositive_insertion_radius_density_increment
    (h : ℝ → ℂ → ℝ) (γ α ε s : ℝ) (z : ℂ)
    (hγ : 0 ≤ γ) (hα : α ≤ 0) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) (hs : 0 < s) (hsε : s ≤ ε)
    (hz : ‖z‖ ≤ 1 / 2) :
    let q := -γ * α
    let a := (max s ‖z‖) ^ q
    let b := (max ε ‖z‖) ^ q
    let X := fun r : ℝ => r ^ (γ ^ 2 / 2) * Real.exp
      (γ * LatticeProb.Gauss.fieldCircleAverage 0 h r z)
    let Y := fun r : ℝ => r ^ (γ ^ 2 / 2) * Real.exp
      (γ * LatticeProb.Gauss.fieldCircleAverage α h r z)
    0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧
      0 ≤ b - a ∧ b - a ≤ ε ^ q ∧
      (ε ≤ ‖z‖ → b - a = 0) ∧
      Y s - Y ε = a * (X s - X ε) - (b - a) * X ε ∧
      0 ≤ (b - a) * X ε ∧ (b - a) * X ε ≤ ε ^ q * X ε := by
  dsimp only
  have hq : 0 ≤ -γ * α := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hγ) hα
  have he2 : 0 < s := hs
  have hm1 : 0 < max s ‖z‖ := lt_max_of_lt_left he2
  have hm2 : 0 < max ε ‖z‖ := lt_max_of_lt_left hε
  have hmax : max s ‖z‖ ≤ max ε ‖z‖ := max_le_max_right _ hsε
  have hmaxone : max ε ‖z‖ ≤ 1 := by apply max_le <;> linarith
  have ha : 0 ≤ (max s ‖z‖) ^ (-γ * α) := Real.rpow_nonneg hm1.le _
  have hab : (max s ‖z‖) ^ (-γ * α) ≤ (max ε ‖z‖) ^ (-γ * α) :=
    Real.rpow_le_rpow hm1.le hmax hq
  have hb : (max ε ‖z‖) ^ (-γ * α) ≤ 1 := Real.rpow_le_one hm2.le hmaxone hq
  have herr : (max ε ‖z‖) ^ (-γ * α) - (max s ‖z‖) ^ (-γ * α) ≤
      ε ^ (-γ * α) := by
    by_cases hzε : ε ≤ ‖z‖
    · rw [max_eq_right hzε, max_eq_right (by linarith : s ≤ ‖z‖), sub_self]
      exact Real.rpow_nonneg hε.le _
    · rw [max_eq_left (le_of_not_ge hzε)]
      linarith
  have hzero (hzε : ε ≤ ‖z‖) :
      (max ε ‖z‖) ^ (-γ * α) - (max s ‖z‖) ^ (-γ * α) = 0 := by
    rw [max_eq_right hzε, max_eq_right (by linarith : s ≤ ‖z‖), sub_self]
  have hfactor (r : ℝ) (hr : 0 < r) :
      r ^ (γ ^ 2 / 2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α h r z) =
      (max r ‖z‖) ^ (-γ * α) *
        (r ^ (γ ^ 2 / 2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 h r z)) := by
    have hlog : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z r =
        Real.log (max r ‖z‖) := by
      simpa using (LatticeProb.Gauss.circleAverage_log_norm_sub_eq z 0 hr)
    have heq : γ * LatticeProb.Gauss.fieldCircleAverage α h r z =
        (-γ * α) * Real.log (max r ‖z‖) +
          γ * LatticeProb.Gauss.fieldCircleAverage 0 h r z := by
      dsimp [LatticeProb.Gauss.fieldCircleAverage]
      rw [hlog]
      ring_nf
    rw [heq, Real.exp_add, Real.rpow_def_of_pos (lt_max_of_lt_left hr)]
    ring_nf
  have hX : 0 ≤ ε ^ (γ ^ 2 / 2) * Real.exp
      (γ * LatticeProb.Gauss.fieldCircleAverage 0 h ε z) :=
    mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le
  refine ⟨ha, hab, hb, sub_nonneg.mpr hab, herr, hzero, ?_, ?_, ?_⟩
  · rw [hfactor s he2, hfactor ε hε]
    ring_nf
  · exact mul_nonneg (sub_nonneg.mpr hab) hX
  · exact mul_le_mul_of_nonneg_right herr hX

/-- The insertion correction has an annealed power bound uniformly over
Brownian starts and all smaller positive smoothing radii. -/
theorem exists_uniform_annealed_nonpositive_radius_insertion_correction_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (γ α : ℝ) (hγ : 0 < γ) (hα : α ≤ 0) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C < ∞ ∧ ∀ (x : ℂ) {ε δ r : ℝ},
      0 < ε → ε ≤ 1 / 2 → δ ≤ 1 / 2 → 0 < r → r ≤ ε →
      (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) 1,
        ENNReal.ofReal ({z : ℂ | ‖z‖ < δ}.indicator (fun z =>
          ((max ε ‖z‖) ^ (-γ * α) - (max r ‖z‖) ^ (-γ * α)) *
          (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) ε z))) (q.2 s.toNNReal)))
        ∂(P.prod (planarBrownianMotion x))) ≤
      ENNReal.ofReal (ε ^ (-γ * α)) * ((ENNReal.ofReal ε) ^ (1 / 2 : ℝ) * C) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_lintegral_prod_brownian_inner_zero_le hh γ
  refine ⟨C + 1, by positivity, ENNReal.add_lt_top.mpr ⟨hC, by simp⟩, ?_⟩
  intro x ε δ r hε hεhalf hδ hr hrε
  calc
    _ ≤ ENNReal.ofReal (ε ^ (-γ * α)) *
        (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) 1,
          ENNReal.ofReal ({z : ℂ | ‖z‖ < ε}.indicator (fun z =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) ε z)) (q.2 s.toNNReal)))
          ∂(P.prod (planarBrownianMotion x))) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono
      intro q
      dsimp only
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono
      intro s
      let z := q.2 s.toNNReal
      change ENNReal.ofReal ({z : ℂ | ‖z‖ < δ}.indicator _ z) ≤
        ENNReal.ofReal (ε ^ (-γ * α)) * ENNReal.ofReal ({z : ℂ | ‖z‖ < ε}.indicator _ z)
      by_cases hzδ : ‖z‖ < δ
      · have hzhalf : ‖z‖ ≤ 1 / 2 := le_trans (le_of_lt hzδ) hδ
        have hstep := nonpositive_insertion_radius_density_increment
          (hcirc q.1) γ α ε r z hγ.le hα hε hεhalf hr hrε hzhalf
        dsimp only at hstep
        by_cases hzε : ‖z‖ < ε
        · rw [Set.indicator_of_mem (show z ∈ {w : ℂ | ‖w‖ < δ} from hzδ), Set.indicator_of_mem (show z ∈ {w : ℂ | ‖w‖ < ε} from hzε),
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hε.le _)]
          exact ENNReal.ofReal_le_ofReal hstep.2.2.2.2.2.2.2.2
        · have hzero := hstep.2.2.2.2.2.1 (le_of_not_gt hzε)
          rw [Set.indicator_of_mem (show z ∈ {w : ℂ | ‖w‖ < δ} from hzδ), Set.indicator_of_notMem (show z ∉ {w : ℂ | ‖w‖ < ε} from hzε), hzero, zero_mul,
            ENNReal.ofReal_zero, mul_zero]
      · rw [Set.indicator_of_notMem (show z ∉ {w : ℂ | ‖w‖ < δ} from hzδ), ENNReal.ofReal_zero]
        exact zero_le
    _ ≤ _ := by
      gcongr
      exact (hbound x hε hεhalf hε hεhalf).trans (by
        gcongr
        exact le_add_right le_rfl)

/-- Same-shell field increments with bounded weights admit one energy bound
for every Brownian start, weight, radius and occupation submeasure. -/
theorem exists_uniform_exponents_brownian_weighted_radius_increment_le_riesz_energy
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ θ d : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ x : ℂ, ∀ᵐ b ∂(planarBrownianMotion x),
        ∀ (g : ℂ → ℝ), Measurable g → ∀ M : ℝ, 0 ≤ M →
        (∀ z, |g z| ≤ M) → (∀ z, g z ≠ 0 → ‖z‖ ≤ 1 / 2) →
        ∀ μ : Measure ℂ, μ ≤ Measure.map (fun t => b t) ν →
        ∀ ε r : ℝ, 0 < ε → ε ≤ 1/2 → 0 < r → r ≤ ε → ε/2 ≤ r →
        (∫ ω, |∫ z, g z * (r^(γ^2/2) * Real.exp (γ*(hcirc ω r z-hcirc ω 1 0)) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0))) ∂μ| ∂P) ≤
        ((Real.exp (γ^2*Real.log 2)-1)*(M^2 * unitOccupationRieszEnergy d b * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨θ, d, hγθ, hθ, hd0, hd2, hp, _⟩ := exists_clock_truncation_exponents hγ0 hγ2
  refine ⟨θ, d, hγθ, hθ, hd0, hd2, hp, ?_⟩
  dsimp only
  intro x
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  filter_upwards [planarBrownianMotion_ae_unit_weighted_occupation_le_riesz_energy x hd0 hd2] with b hb
  intro g hg M hM hgM hgs μ hμ ε r hε hεhalf hr hrε hεr
  let ρ : Measure ℂ := Measure.map (fun t => b t) ν
  let : IsProbabilityMeasure ρ := inferInstance
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le ρ hμ
  have hgρ : Integrable g ρ := by
    refine (integrable_const M).mono' hg.aestronglyMeasurable ?_
    filter_upwards with z
    simpa [Real.norm_eq_abs] using hgM z
  have hgi : Integrable g μ := hgρ.mono_measure hμ
  have hA : (∫ z, |g z| ∂μ) ≤ M := by
    calc
      _ ≤ ∫ z, |g z| ∂ρ := integral_mono_measure hμ (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) hgρ.abs
      _ ≤ ∫ _ : ℂ, M ∂ρ := integral_mono hgρ.abs (integrable_const M) (fun z => hgM z)
      _ = M := by simp
  have hpair0 := hb g hg M hM hgM (2*ε) (by positivity)
  have hpair : (∫ p : ℂ × ℂ, if ‖p.1-p.2‖ < 2*ε then |g p.1| * |g p.2| else 0
      ∂(μ.prod μ)) ≤ M^2*(unitOccupationRieszEnergy d b*(2*ε)^d) := by
    apply (integral_mono_measure (Measure.prod_mono hμ hμ) ?_ hpair0.1).trans hpair0.2.2
    filter_upwards with p
    split_ifs <;> positivity
  have hI : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤
      (M^2*unitOccupationRieszEnergy d b*2^d)*Real.exp (Real.log ε*d) := by
    have hI' : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤ M^2*(unitOccupationRieszEnergy d b*(2*ε)^d) := by
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using hpair
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le,
      Real.rpow_def_of_pos hε] at hI'
    convert hI' using 1; ring
  exact field_radius_increment_le_rate hh hr hrε hεr μ hg hgi (fun z hz => by linarith [hgs z hz])
    hγθ.le hθ.le hA hI



/-- The zero-insertion annular time-cell second moment has a constant
independent of the smoothing radius and the Brownian starting point. -/
theorem exists_uniform_brownian_zero_insertion_annular_cell_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ : γ ≠ 0) (hγ2 : γ ^ 2 < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (x : ℂ) {ε : ℝ}, 0 < ε →
      ∀ (u h : ℝ), 0 ≤ u → 0 < h →
        let ν := Measure.map Real.toNNReal (volume.restrict (Icc u (u + h)))
        (∫⁻ b, ∫⁻ ω, (∫⁻ t, ENNReal.ofReal
          ({z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z)) (b t)) ∂ν) ^ 2 ∂P
          ∂(planarBrownianMotion x)) ≤ C * (ENNReal.ofReal h) ^ (2 - γ ^ 2 / 2) := by
  obtain ⟨D, hD, henergy⟩ :=
    exists_planarBrownianMotion_interval_pair_enorm_rpow_neg 0 (sq_pos_of_ne_zero hγ) hγ2
  let A : ℝ≥0∞ := ENNReal.ofReal (2 ^ (γ ^ 2))
  refine ⟨A * D, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD, ?_⟩
  intro x ε hε u h hu hhpos
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc u (u + h)))
  have hbound (b : ContinuousPath ℂ) :
      (∫⁻ ω, (∫⁻ t, ENNReal.ofReal
        ({z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z)) (b t)) ∂ν) ^ 2 ∂P) ≤
      A * ∫⁻ p : ℝ≥0 × ℝ≥0,
        (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-(γ ^ 2)) ∂(ν.prod ν) := by
    simpa [A] using
      (lintegral_annular_inserted_path_sq_le_riesz hh ν b b.continuous.measurable hε
        (le_refl ε) hγ 0)
  have hm : Measurable (fun b : ContinuousPath ℂ => ∫⁻ p : ℝ≥0 × ℝ≥0,
      (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-(γ ^ 2)) ∂(ν.prod ν)) := by
    have hk : Measurable (fun q : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0) =>
        (ENNReal.ofReal ‖q.1 q.2.1 - q.1 q.2.2‖) ^ (-(γ ^ 2))) := by fun_prop
    exact hk.lintegral_prod_right'
  calc
    _ ≤ ∫⁻ b, A * (∫⁻ p : ℝ≥0 × ℝ≥0,
        (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-(γ ^ 2)) ∂(ν.prod ν))
          ∂(planarBrownianMotion x) := lintegral_mono hbound
    _ = A * (∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0,
        (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-(γ ^ 2)) ∂(ν.prod ν)
          ∂(planarBrownianMotion x)) := lintegral_const_mul A hm
    _ ≤ (A * D) * (ENNReal.ofReal h) ^ (2 - γ ^ 2 / 2) := by
      have heq := henergy u h hu hhpos
      dsimp only at heq
      rw [lintegral_planarBrownianMotion_interval_pair_enorm_rpow_neg 0 u h _ hu hhpos] at heq
      rw [lintegral_planarBrownianMotion_interval_pair_enorm_rpow_neg x u h _ hu hhpos, heq]
      exact le_of_eq (by ac_rfl)


/-- The zero-insertion annular cell moment bound on the field-path product. -/
theorem exists_uniform_prod_brownian_zero_insertion_annular_cell_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ : γ ≠ 0) (hγ2 : γ ^ 2 < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (x : ℂ) {ε : ℝ}, 0 < ε →
      ∀ (u h : ℝ), 0 ≤ u → 0 < h →
      (∫⁻ p : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc u (u + h), ENNReal.ofReal
        ({z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc p.1) ε z)) (p.2 s.toNNReal))) ^ 2
          ∂(P.prod (planarBrownianMotion x))) ≤
        C * (ENNReal.ofReal h) ^ (2 - γ ^ 2 / 2) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_brownian_zero_insertion_annular_cell_sq_le hh hγ hγ2
  refine ⟨C, hC, ?_⟩
  intro x ε hε u h hu hhpos
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc u (u + h)))
  let A : Set ℂ := {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}
  let F : Ω × ContinuousPath ℂ → ℝ≥0∞ := fun p =>
    ∫⁻ s in Ioc u (u + h), ENNReal.ofReal
      (A.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage 0 (hcirc p.1) ε z)) (p.2 s.toNNReal))
  have hF : AEMeasurable (fun p => (F p) ^ 2) (P.prod (planarBrownianMotion x)) :=
    (aemeasurable_annular_inserted_clock_cell hh (planarBrownianMotion x) hε γ 0 ε u (u+h)).pow_const 2
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hmeas : ∀ᵐ ω ∂P, Measurable (fun z => ENNReal.ofReal
      (A.indicator (fun w => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε w)) z)) := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh 0] with ω hω hrec
    have hm : Measurable (fun z : ℂ => ENNReal.ofReal
        (A.indicator (fun w => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          (H ω ε w - H ω 1 0 - 0 * Real.log (max ε ‖w‖)))) z)) := by
      apply ENNReal.measurable_ofReal.comp
      exact (measurable_const.mul (measurable_const.mul
        ((((hHm ε hε).comp (measurable_id.prodMk measurable_const)).sub measurable_const).sub
          (measurable_const.mul ((measurable_const.max measurable_norm).log)))).exp).indicator hA
    convert hm using 1
    ext z
    simp only [Set.indicator_apply]
    split_ifs
    · rw [hω, hω, hrec ε z hε]
    · rfl
  have heq (b : ContinuousPath ℂ) : ∀ᵐ ω ∂P,
      F (ω,b) = ∫⁻ t, ENNReal.ofReal (A.indicator (fun z =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z)) (b t)) ∂ν := by
    filter_upwards [hmeas] with ω hω
    dsimp [F, ν]
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
    symm
    exact lintegral_map (hω.comp b.continuous.measurable) continuous_real_toNNReal.measurable
  have hswap : (∫⁻ p, (F p)^2 ∂(P.prod (planarBrownianMotion x))) =
      ∫⁻ b, ∫⁻ ω, (F (ω,b))^2 ∂P ∂(planarBrownianMotion x) :=
    lintegral_prod_symm _ hF
  change (∫⁻ p, (F p)^2 ∂(P.prod (planarBrownianMotion x))) ≤ _
  rw [hswap]
  refine (le_of_eq ?_).trans (hbound x hε u h hu hhpos)
  apply lintegral_congr
  intro b
  apply lintegral_congr_ae
  filter_upwards [heq b] with ω hω
  rw [hω]


/-- The expected maximum zero-insertion annular mesh cell decays uniformly
in the smoothing radius and Brownian starting point. -/
theorem exists_uniform_prod_zero_insertion_annular_mesh_max_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ : γ ≠ 0) (hγ2 : γ ^ 2 < 2) :
    ∃ (C : ℝ≥0∞) (β : ℝ), C < ∞ ∧ 0 < β ∧
      ∀ (x : ℂ) {ε : ℝ}, 0 < ε → ∀ (m : ℕ), 0 < m →
      (∫⁻ p : Ω × ContinuousPath ℂ, (⨆ j : Fin m,
        ∫⁻ s in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m),
          ENNReal.ofReal ({z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc p.1) ε z)) (p.2 s.toNNReal)))
          ∂(P.prod (planarBrownianMotion x))) ≤ C * (m : ℝ≥0∞) ^ (-β) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_prod_brownian_zero_insertion_annular_cell_sq_le hh hγ hγ2
  let β : ℝ := (1 - γ ^ 2 / 2) / 2
  have hβ : 0 < β := by dsimp [β]; linarith
  refine ⟨C ^ (1 / 2 : ℝ), β, ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC.ne, hβ, ?_⟩
  intro x ε hε m hm
  let X : Fin m → Ω × ContinuousPath ℂ → ℝ≥0∞ := fun j p =>
    ∫⁻ s in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m),
      ENNReal.ofReal ({z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage 0 (hcirc p.1) ε z)) (p.2 s.toNNReal))
  have hX (j : Fin m) : AEMeasurable (X j) (P.prod (planarBrownianMotion x)) :=
    aemeasurable_annular_inserted_clock_cell hh (planarBrownianMotion x) hε γ 0 ε
      ((j : ℝ) / m) (((j : ℝ) + 1) / m)
  have hcell (j : Fin m) :
      (∫⁻ p, (X j p) ^ (2 : ℝ) ∂(P.prod (planarBrownianMotion x))) ≤
        C * (m : ℝ≥0∞) ^ (-(1 + 2 * β)) := by
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hj0 : (0 : ℝ) ≤ j := by positivity
    have hend : ((j : ℝ) / m) + 1 / (m : ℝ) = ((j : ℝ) + 1) / m := by ring
    have hrpow : (ENNReal.ofReal (1 / (m : ℝ))) ^ (2 - γ ^ 2 / 2) =
        (m : ℝ≥0∞) ^ (-(1 + 2 * β)) := by
      rw [one_div, ENNReal.ofReal_inv_of_pos hm0, ENNReal.ofReal_natCast,
        ENNReal.inv_rpow, ← ENNReal.rpow_neg]
      congr 1
      dsimp [β]
      ring
    have hmain := hbound x hε ((j : ℝ) / m) (1 / (m : ℝ))
      (div_nonneg hj0 hm0.le) (one_div_pos.mpr hm0)
    rw [hend, hrpow] at hmain
    simpa only [X, ENNReal.rpow_ofNat] using hmain
  exact lintegral_iSup_le_mesh_rpow_of_aemeasurable (P.prod (planarBrownianMotion x)) hm X hX
    (by norm_num : (1 : ℝ) ≤ 2) C hcell


/-- A nonpositive insertion reduces the normalized density in the half-disc. -/
theorem nonpositive_halfDisc_density_le_zero_insertion
    (h : ℝ → ℂ → ℝ) {γ α ε : ℝ} (z : ℂ)
    (hγ : 0 ≤ γ) (hα : α ≤ 0) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hz : ‖z‖ ≤ 1 / 2) :
    ε ^ (γ ^ 2 / 2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α h ε z) ≤
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 h ε z) := by
  have hq : 0 ≤ -γ * α := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hγ) hα
  have hm : 0 < max ε ‖z‖ := lt_max_of_lt_left hε
  have hmone : max ε ‖z‖ ≤ 1 := by apply max_le <;> linarith
  have hweight : (max ε ‖z‖) ^ (-γ * α) ≤ 1 := Real.rpow_le_one hm.le hmone hq
  have hlog : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z ε =
      Real.log (max ε ‖z‖) := by
    simpa using (LatticeProb.Gauss.circleAverage_log_norm_sub_eq z 0 hε)
  have heq : γ * LatticeProb.Gauss.fieldCircleAverage α h ε z =
      (-γ * α) * Real.log (max ε ‖z‖) +
        γ * LatticeProb.Gauss.fieldCircleAverage 0 h ε z := by
    dsimp [LatticeProb.Gauss.fieldCircleAverage]
    rw [hlog]
    ring_nf
  have hfactor : ε ^ (γ ^ 2 / 2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α h ε z) =
      (max ε ‖z‖) ^ (-γ * α) * (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage 0 h ε z)) := by
    rw [heq, Real.exp_add, Real.rpow_def_of_pos hm]
    ring_nf
  rw [hfactor]
  exact mul_le_of_le_one_left (mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le) hweight


/-- Nonpositive-insertion annular mesh cells have the same uniform maximum
bound as zero-insertion cells. -/
theorem exists_uniform_prod_nonpositive_annular_mesh_max_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2) :
    ∃ (C : ℝ≥0∞) (β : ℝ), C < ∞ ∧ 0 < β ∧
      ∀ (x : ℂ) (α : ℝ), α ≤ 0 → ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 2 →
      ∀ (m : ℕ), 0 < m →
      (∫⁻ p : Ω × ContinuousPath ℂ, (⨆ j : Fin m,
        ∫⁻ s in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m),
          ENNReal.ofReal ({z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) (p.2 s.toNNReal)))
          ∂(P.prod (planarBrownianMotion x))) ≤ C * (m : ℝ≥0∞) ^ (-β) := by
  obtain ⟨C, β, hC, hβ, hmesh⟩ :=
    exists_uniform_prod_zero_insertion_annular_mesh_max_le hh hγ.ne' hγ2
  refine ⟨C, β, hC, hβ, ?_⟩
  intro x α hα ε hε hεhalf m hm
  refine (lintegral_mono ?_).trans (hmesh x hε m hm)
  intro p
  apply iSup_le
  intro j
  calc
    _ ≤ ∫⁻ s in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m),
        ENNReal.ofReal ({z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc p.1) ε z)) (p.2 s.toNNReal)) := by
      apply lintegral_mono
      intro s
      apply ENNReal.ofReal_le_ofReal
      by_cases hz : p.2 s.toNNReal ∈ {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
        exact nonpositive_halfDisc_density_le_zero_insertion (hcirc p.1) _ hγ.le hα hε hεhalf hz.2
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
    _ ≤ _ := by
      dsimp only
      exact le_iSup (fun i : Fin m => ∫⁻ s in Ioc ((i : ℝ) / m) (((i : ℝ) + 1) / m),
        ENNReal.ofReal ({z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc p.1) ε z)) (p.2 s.toNNReal))) j


/-- The expected maximum inner-ball mesh cell is bounded by the entire
zero-insertion inner occupation, uniformly over the mesh. -/
theorem exists_uniform_prod_nonpositive_inner_mesh_max_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ : 0 ≤ γ) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (x : ℂ) (α : ℝ), α ≤ 0 →
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 2 → ∀ (m : ℕ), 0 < m →
      (∫⁻ p : Ω × ContinuousPath ℂ, (⨆ j : Fin m,
        ∫⁻ s in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m),
          ENNReal.ofReal ({z : ℂ | ‖z‖ < ε}.indicator (fun z =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) (p.2 s.toNNReal)))
          ∂(P.prod (planarBrownianMotion x))) ≤ (ENNReal.ofReal ε) ^ (1 / 2 : ℝ) * C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_lintegral_prod_brownian_inner_zero_le hh γ
  refine ⟨C, hC, ?_⟩
  intro x α hα ε hε hεhalf m hm
  refine (lintegral_mono ?_).trans (hbound x hε hεhalf hε hεhalf)
  intro p
  apply iSup_le
  intro j
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hjm : (j : ℝ) + 1 ≤ m := by exact_mod_cast j.isLt
  calc
    _ ≤ ∫⁻ s in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m),
        ENNReal.ofReal ({z : ℂ | ‖z‖ < ε}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc p.1) ε z)) (p.2 s.toNNReal)) := by
      apply lintegral_mono
      intro s
      apply ENNReal.ofReal_le_ofReal
      by_cases hz : p.2 s.toNNReal ∈ {z : ℂ | ‖z‖ < ε}
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
        exact nonpositive_halfDisc_density_le_zero_insertion (hcirc p.1) _ hγ hα hε hεhalf
          (le_trans (le_of_lt hz) hεhalf)
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
    _ ≤ _ := by
      dsimp only
      apply lintegral_mono_set
      exact Ioc_subset_Ioc (by positivity) ((div_le_one hm0).2 hjm)


/-- The full half-disc mesh maximum has a uniform bound obtained by splitting
the annulus from the inner ball. -/
theorem exists_uniform_prod_nonpositive_halfDisc_mesh_max_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2) :
    ∃ (C D : ℝ≥0∞) (β : ℝ), C < ∞ ∧ D < ∞ ∧ 0 < β ∧
      ∀ (x : ℂ) (α : ℝ), α ≤ 0 → ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 2 →
      ∀ (m : ℕ), 0 < m →
      (∫⁻ p : Ω × ContinuousPath ℂ, (⨆ j : Fin m,
        ∫⁻ s in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m),
          ENNReal.ofReal ({z : ℂ | ‖z‖ ≤ 1 / 2}.indicator (fun z =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) (p.2 s.toNNReal)))
          ∂(P.prod (planarBrownianMotion x))) ≤
        C * (m : ℝ≥0∞) ^ (-β) + (ENNReal.ofReal ε) ^ (1 / 2 : ℝ) * D := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨C, β, hC, hβ, houter⟩ := exists_uniform_prod_nonpositive_annular_mesh_max_le hh hγ hγ2
  obtain ⟨D, hD, hinner⟩ := exists_uniform_prod_nonpositive_inner_mesh_max_le hh hγ.le
  refine ⟨C, D, β, hC, hD, hβ, ?_⟩
  intro x α hα ε hε hεhalf m hm
  let A : Set ℂ := {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}
  let B : Set ℂ := {z : ℂ | ‖z‖ < ε}
  let E : Set ℂ := {z : ℂ | ‖z‖ ≤ 1 / 2}
  let f : Ω × ContinuousPath ℂ → ℂ → ℝ := fun p z =>
    ε ^ (γ ^ 2 / 2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)
  let O : Fin m → Ω × ContinuousPath ℂ → ℝ≥0∞ := fun j p =>
    ∫⁻ s in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m),
      ENNReal.ofReal (A.indicator (f p) (p.2 s.toNNReal))
  let I : Fin m → Ω × ContinuousPath ℂ → ℝ≥0∞ := fun j p =>
    ∫⁻ s in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m),
      ENNReal.ofReal (B.indicator (f p) (p.2 s.toNNReal))
  have hO : AEMeasurable (fun p => ⨆ j, O j p) (P.prod (planarBrownianMotion x)) := by
    apply AEMeasurable.iSup
    intro j
    exact aemeasurable_annular_inserted_clock_cell hh (planarBrownianMotion x) hε γ α ε
      ((j : ℝ) / m) (((j : ℝ) + 1) / m)
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hB : MeasurableSet B := measurableSet_lt measurable_norm measurable_const
  have hf : ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), Measurable
      (fun s : ℝ => ENNReal.ofReal (B.indicator (f p) (p.2 s.toNNReal))) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P)
      (ν := planarBrownianMotion x)).ae hHae,
      (Measure.quasiMeasurePreserving_fst (μ := P)
        (ν := planarBrownianMotion x)).ae (ae_recentered_inserted_circle_average hh α)] with p hp hrec
    have hmz : Measurable (fun z : ℂ => ENNReal.ofReal
        (B.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          (H p.1 ε z - H p.1 1 0 - α * Real.log (max ε ‖z‖)))) z)) := by
      apply ENNReal.measurable_ofReal.comp
      exact (measurable_const.mul (measurable_const.mul
        ((((hHm ε hε).comp (measurable_id.prodMk measurable_const)).sub measurable_const).sub
          (measurable_const.mul ((measurable_const.max measurable_norm).log)))).exp).indicator hB
    have heq : (fun z : ℂ => ENNReal.ofReal (B.indicator (f p) z)) =
        (fun z : ℂ => ENNReal.ofReal (B.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          (H p.1 ε z - H p.1 1 0 - α * Real.log (max ε ‖z‖)))) z)) := by
      ext z
      dsimp [f]
      simp only [Set.indicator_apply]
      split_ifs
      · rw [hp, hp, hrec ε z hε]
      · rfl
    rw [← heq] at hmz
    exact hmz.comp (p.2.continuous.measurable.comp continuous_real_toNNReal.measurable)
  have hpoint : ∀ᵐ p ∂(P.prod (planarBrownianMotion x)),
      (⨆ j : Fin m, ∫⁻ s in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m),
        ENNReal.ofReal (E.indicator (f p) (p.2 s.toNNReal))) ≤
        (⨆ j, O j p) + (⨆ j, I j p) := by
    filter_upwards [hf] with p hp
    apply iSup_le
    intro j
    calc
      _ = I j p + O j p := by
        dsimp [I, O]
        rw [← lintegral_add_left hp]
        apply lintegral_congr
        intro s
        let z := p.2 s.toNNReal
        have hpos : 0 ≤ f p z := mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le
        by_cases hzB : z ∈ B
        · have hzE : z ∈ E := le_trans (le_of_lt hzB) hεhalf
          have hzA : z ∉ A := by exact fun hz => not_le_of_gt hzB hz.1
          rw [Set.indicator_of_mem hzE, Set.indicator_of_mem hzB, Set.indicator_of_notMem hzA]
          simp
        · by_cases hzE : z ∈ E
          · have hzA : z ∈ A := ⟨le_of_not_gt hzB, hzE⟩
            rw [Set.indicator_of_mem hzE, Set.indicator_of_notMem hzB, Set.indicator_of_mem hzA]
            simp
          · have hzA : z ∉ A := fun hz => hzE hz.2
            rw [Set.indicator_of_notMem hzE, Set.indicator_of_notMem hzB, Set.indicator_of_notMem hzA]
            simp
      _ ≤ _ := add_le_add (le_iSup (fun j => I j p) j) (le_iSup (fun j => O j p) j) |>.trans_eq (add_comm _ _)
  calc
    _ ≤ ∫⁻ p, ((⨆ j, O j p) + (⨆ j, I j p)) ∂(P.prod (planarBrownianMotion x)) :=
      lintegral_mono_ae hpoint
    _ = (∫⁻ p, ⨆ j, O j p ∂(P.prod (planarBrownianMotion x))) +
        (∫⁻ p, ⨆ j, I j p ∂(P.prod (planarBrownianMotion x))) := lintegral_add_left' hO _
    _ ≤ _ := add_le_add (houter x α hα hε hεhalf m hm) (hinner x α hα hε hεhalf m hm)


/-- The uniform time difference of two half-disc clocks is controlled by
its time-grid values and the full-disc mesh bound. -/
theorem exists_uniform_prod_nonpositive_halfDisc_clock_iSup_le_grid
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2) :
    ∃ (C D : ℝ≥0∞) (β : ℝ), C < ∞ ∧ D < ∞ ∧ 0 < β ∧
      ∀ (x : ℂ) (α : ℝ), α ≤ 0 → ∀ {r ε : ℝ}, 0 < r → 0 < ε → ε ≤ 1 / 2 →
      ∀ (m : ℕ), 0 < m →
      let F : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
        stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) 0
          (fun _ => t.toNNReal) p.2
      (∫⁻ p, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |F r p t - F ε p t|
        ∂(P.prod (planarBrownianMotion x))) ≤
        (∑ j ∈ Finset.range (m + 1), ∫⁻ p, ENNReal.ofReal
          |F r p (j / (m : ℝ)) - F ε p (j / (m : ℝ))|
          ∂(P.prod (planarBrownianMotion x))) +
          (C * (m : ℝ≥0∞) ^ (-β) + (ENNReal.ofReal ε) ^ (1 / 2 : ℝ) * D) := by
  obtain ⟨C, D, β, hC, hD, hβ, hmesh⟩ :=
    exists_uniform_prod_nonpositive_halfDisc_mesh_max_le hh hγ hγ2
  refine ⟨C, D, β, hC, hD, hβ, ?_⟩
  intro x α hα r ε hr hε hεhalf m hm
  have hbase := lintegral_prod_stoppedAnnularClock_radius_iSup_le_grid_and_mesh
    hh x γ α 0 hr hε m hm
  simp only [norm_nonneg, true_and] at hbase
  exact hbase.trans (add_le_add le_rfl (hmesh x α hα hε hεhalf m hm))


/-- The nonpositive insertion weight in a same-shell field increment is
bounded by one uniformly over all occupation submeasures. -/
theorem exists_uniform_nonpositive_weighted_radius_increment_le_riesz_energy
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ θ d : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ x : ℂ, ∀ᵐ b ∂(planarBrownianMotion x),
        ∀ α : ℝ, α ≤ 0 → ∀ μ : Measure ℂ, μ ≤ Measure.map (fun t => b t) ν →
        ∀ ε r : ℝ, 0 < ε → ε ≤ 1/2 → 0 < r → r ≤ ε → ε/2 ≤ r →
        (∫ ω, |∫ z, {z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z =>
          (max r ‖z‖) ^ (-γ*α) *
            (r^(γ^2/2) * Real.exp (γ*(hcirc ω r z-hcirc ω 1 0)) -
              ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0)))) z ∂μ| ∂P) ≤
        ((Real.exp (γ^2*Real.log 2)-1)*(unitOccupationRieszEnergy d b * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨θ, d, hγθ, hθ, hd0, hd2, hp, hbound⟩ :=
    exists_uniform_exponents_brownian_weighted_radius_increment_le_riesz_energy hh hγ0 hγ2
  refine ⟨θ, d, hγθ, hθ, hd0, hd2, hp, ?_⟩
  dsimp only at hbound ⊢
  intro x
  filter_upwards [hbound x] with b hb
  intro α hα μ hμ ε r hε hεhalf hr hrε hεr
  let A : Set ℂ := {z : ℂ | ‖z‖ ≤ 1/2}
  let g : ℂ → ℝ := A.indicator (fun z => (max r ‖z‖) ^ (-γ*α))
  have hA : MeasurableSet A := measurableSet_le measurable_norm measurable_const
  have hg : Measurable g := by
    apply Measurable.indicator _ hA
    exact ((continuous_const.max continuous_norm).rpow_const
      (fun _ => Or.inl (ne_of_gt (lt_max_of_lt_left hr)))).measurable
  have hq : 0 ≤ -γ * α := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hγ0.le) hα
  have hg1 (z : ℂ) : |g z| ≤ 1 := by
    by_cases hz : z ∈ A
    · rw [show g z = _ from Set.indicator_of_mem hz _]
      rw [abs_of_nonneg (Real.rpow_nonneg (le_of_lt (lt_max_of_lt_left hr)) _)]
      exact Real.rpow_le_one (le_of_lt (lt_max_of_lt_left hr))
        (by
          have hzhalf : ‖z‖ ≤ (1 : ℝ)/2 := hz
          apply max_le <;> linarith) hq
    · rw [show g z = 0 from Set.indicator_of_notMem hz _, abs_zero]
      norm_num
  have hgs (z : ℂ) (hz : g z ≠ 0) : ‖z‖ ≤ 1/2 := by
    by_contra hn
    have hnA : z ∉ A := hn
    exact hz (show g z = 0 from Set.indicator_of_notMem hnA _)
  have hhbound := hb g hg 1 (by norm_num) hg1 hgs μ hμ ε r hε hεhalf hr hrε hεr
  convert hhbound using 1
  · congr 1
    funext ω
    congr 1
    apply integral_congr_ae
    filter_upwards with z
    by_cases hz : z ∈ A
    · rw [show A.indicator _ z = _ from Set.indicator_of_mem hz _,
        show g z = _ from Set.indicator_of_mem hz _]
    · rw [show A.indicator _ z = _ from Set.indicator_of_notMem hz _,
        show g z = _ from Set.indicator_of_notMem hz _, zero_mul]
  · simp


/-- The nonnegative insertion correction is controlled uniformly in time
by its entire unit-interval occupation. -/
theorem exists_uniform_annealed_nonpositive_radius_correction_iSup_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (γ α : ℝ) (hγ : 0 < γ) (hα : α ≤ 0) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C < ∞ ∧ ∀ (x : ℂ) {ε r : ℝ},
      0 < ε → ε ≤ 1 / 2 → 0 < r → r ≤ ε →
      (∫⁻ q : Ω × ContinuousPath ℂ, (⨆ t : Icc (0 : ℝ) 1,
        ∫⁻ s in Ioc (0 : ℝ) t.1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < 1 / 2}.indicator (fun z =>
            ((max ε ‖z‖) ^ (-γ * α) - (max r ‖z‖) ^ (-γ * α)) *
            (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) ε z))) (q.2 s.toNNReal)))
        ∂(P.prod (planarBrownianMotion x))) ≤
      ENNReal.ofReal (ε ^ (-γ * α)) * ((ENNReal.ofReal ε) ^ (1 / 2 : ℝ) * C) := by
  obtain ⟨C, hC0, hC, hbound⟩ :=
    exists_uniform_annealed_nonpositive_radius_insertion_correction_le hh γ α hγ hα
  refine ⟨C, hC0, hC, ?_⟩
  intro x ε r hε hεhalf hr hrε
  refine (lintegral_mono ?_).trans (hbound x hε hεhalf (le_refl (1/2 : ℝ)) hr hrε)
  intro q
  apply iSup_le
  intro t
  exact lintegral_mono_set (Ioc_subset_Ioc le_rfl t.2.2)


/-- A bounded weighted same-shell increment is integrable over the field
for every submeasure of a unit Brownian occupation measure. -/
theorem integrable_brownian_weighted_radius_increment_field
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε r : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hr : 0 < r) (hrε : r ≤ ε)
    (γ : ℝ) (b : ContinuousPath ℂ) (g : ℂ → ℝ) (hg : Measurable g)
    (hgm : ∀ z, |g z| ≤ 1) (hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ 1/2)
    (μ : Measure ℂ) (hμ : μ ≤ Measure.map (fun t => b t)
      (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) :
    Integrable (fun ω => ∫ z, g z *
      (r^(γ^2/2) * Real.exp (γ*(hcirc ω r z-hcirc ω 1 0)) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0))) ∂μ) P := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le (Measure.map (fun t => b t) ν) hμ
  have hgi : Integrable g μ := by
    apply (integrable_const (1 : ℝ)).mono' hg.aestronglyMeasurable
    filter_upwards with z
    simpa only [Real.norm_eq_abs] using hgm z
  have hgr : ∀ z, g z ≠ 0 → ‖z‖ + r ≤ 1 := by
    intro z hz
    linarith [hgs z hz]
  have hgε : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ 1 := by
    intro z hz
    linarith [hgs z hz]
  exact hh.integrable_integral_increment_scales hr hε zero_lt_one μ hg hgi hgr hgε γ


/-- A stopped, weighted radius increment has a jointly measurable
path-field representative. -/
theorem exists_measurable_brownian_weighted_radius_increment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (γ : ℝ)
    (g : ℂ → ℝ) (hg : Measurable g) (T : ℝ≥0) :
    ∃ F : ContinuousPath ℂ × Ω → ℝ, Measurable F ∧
      ∀ᵐ ω ∂P, ∀ b, F (b, ω) = ∫ z, g z *
        (r^(γ^2/2) * Real.exp (γ*(hcirc ω r z-hcirc ω 1 0)) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0)))
        ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
          (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic T))) := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let G : Ω × ℂ → ℝ := fun q => g q.2 *
    (r^(γ^2/2) * Real.exp (γ*(H q.1 r q.2-H q.1 1 0)) -
      ε^(γ^2/2) * Real.exp (γ*(H q.1 ε q.2-H q.1 1 0)))
  have hG : Measurable G := by
    have h1 : Measurable (fun q : Ω × ℂ => H q.1 r q.2) :=
      (hHm r hr).comp measurable_swap
    have h2 : Measurable (fun q : Ω × ℂ => H q.1 ε q.2) :=
      (hHm ε hε).comp measurable_swap
    have h3 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
      (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
    exact (hg.comp measurable_snd).mul
      ((measurable_const.mul (measurable_const.mul (h1.sub h3)).exp).sub
        (measurable_const.mul (measurable_const.mul (h2.sub h3)).exp))
  let ν : Measure ℝ≥0 := (Measure.map Real.toNNReal
    (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic T)
  let F : ContinuousPath ℂ × Ω → ℝ := fun q =>
    ∫ z, G (q.2,z) ∂(Measure.map (fun t => q.1 t) ν)
  have hF : Measurable F := by
    have heval0 : Measurable (fun q : ContinuousPath ℂ × ℝ≥0 => q.1 q.2) := by fun_prop
    have heval : Measurable (fun q : (ContinuousPath ℂ × Ω) × ℝ≥0 => q.1.1 q.2) :=
      heval0.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have h := hG.comp ((measurable_snd.comp measurable_fst).prodMk heval)
    have hm := h.stronglyMeasurable.integral_prod_right' (ν := ν)
    convert hm.measurable using 1
    funext q
    exact integral_map q.1.continuous.measurable.aemeasurable
      (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  refine ⟨F, hF, ?_⟩
  filter_upwards [hHae] with ω hω b
  simp only [F, G, hω, ν]


/-- A summable annealed bound controls every bounded weighted same-shell
increment stopped at a deterministic unit-time horizon. -/
theorem exists_uniform_summable_annealed_weighted_radius_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ A : ℕ → ℝ, Summable A ∧ (∀ n, 0 ≤ A n) ∧
      (∃ c u v : ℝ, 0 ≤ c ∧ 0 < u ∧ 0 < v ∧ ∀ n,
        A n = c * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * u) +
          2 * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * v)) ∧
      ∀ (n : ℕ) (x : ℂ) (g : ℂ → ℝ), Measurable g →
        (∀ z, |g z| ≤ 1) → (∀ z, g z ≠ 0 → ‖z‖ ≤ 1/2) →
        ∀ r : ℝ, 0 < r → r ≤ (2 : ℝ)⁻¹ ^ (n+1) →
        (2 : ℝ)⁻¹ ^ (n+1) / 2 ≤ r → ∀ T : ℝ≥0,
        ∃ F : ContinuousPath ℂ × Ω → ℝ, Measurable F ∧
          (∀ᵐ ω ∂P, ∀ b, F (b, ω) = ∫ z, g z *
            (r^(γ^2/2) * Real.exp (γ*(hcirc ω r z-hcirc ω 1 0)) -
              ((2 : ℝ)⁻¹ ^ (n+1))^(γ^2/2) * Real.exp (γ*
                (hcirc ω ((2 : ℝ)⁻¹ ^ (n+1)) z-hcirc ω 1 0)))
            ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
              (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic T)))) ∧
          Integrable F ((planarBrownianMotion x).prod P) ∧
          (∫ q, |F q| ∂((planarBrownianMotion x).prod P)) ≤ A n := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨θ, d, hγθ, hθ, hd0, hd2, hp, hbound⟩ :=
    exists_uniform_exponents_brownian_weighted_radius_increment_le_riesz_energy hh hγ0 hγ2
  let u : ℝ := (d-γ^2+(2*γ-θ)^2/2)/2
  let v : ℝ := (θ-γ)^2/2
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  let R : ℕ → ContinuousPath ℂ → ℝ := fun n b =>
    ((Real.exp (γ^2*Real.log 2)-1)*(unitOccupationRieszEnergy d b * 2^d)+1)/2 *
      Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * u) +
      2 * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * v)
  obtain ⟨A, hAs, hA⟩ := exists_uniform_summable_inner_energy_bound
    (γ := γ) hd0 hd2 hu hv
  have hR0 (n : ℕ) (b : ContinuousPath ℂ) : 0 ≤ R n b := by
    dsimp [R]
    have he : 0 ≤ Real.exp (γ^2*Real.log 2)-1 :=
      sub_nonneg.mpr (Real.one_le_exp (by positivity))
    have hE : 0 ≤ unitOccupationRieszEnergy d b := ENNReal.toReal_nonneg
    positivity
  refine ⟨A, hAs, ?_, ?_, ?_⟩
  · intro n
    rw [← (hA 0 n).2]
    exact integral_nonneg (hR0 n)
  · let B : ContinuousPath ℂ → ℝ := fun b =>
      ((Real.exp (γ^2*Real.log 2)-1)*(unitOccupationRieszEnergy d b * 2^d)+1)/2
    have hB : Integrable B (planarBrownianMotion 0) := by
      have hE := integrable_unitOccupationRieszEnergy 0 hd0 hd2
      dsimp [B]
      fun_prop
    have hB0 (b : ContinuousPath ℂ) : 0 ≤ B b := by
      dsimp [B]
      have he : 0 ≤ Real.exp (γ^2*Real.log 2)-1 :=
        sub_nonneg.mpr (Real.one_le_exp (by positivity))
      have hE : 0 ≤ unitOccupationRieszEnergy d b := ENNReal.toReal_nonneg
      positivity
    refine ⟨∫ b, B b ∂(planarBrownianMotion 0), u, v,
      integral_nonneg hB0, hu, hv, ?_⟩
    intro n
    rw [← (hA 0 n).2]
    change (∫ b, B b * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * u) +
      2 * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * v)
      ∂(planarBrownianMotion 0)) = _
    rw [integral_add (hB.mul_const _) (integrable_const _), integral_mul_const]
    simp
  intro n x g hg hgm hgs r hr hrε hεr T
  let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεhalf : ε ≤ 1/2 := by
    dsimp [ε]
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  obtain ⟨F, hFm, hFspatial⟩ :=
    exists_measurable_brownian_weighted_radius_increment hh hε hr γ g hg T
  have hfield (b : ContinuousPath ℂ) : Integrable (fun ω => F (b,ω)) P := by
    let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    let μ : Measure ℂ := Measure.map (fun t => b t) (ν.restrict (Iic T))
    have hμ : μ ≤ Measure.map (fun t => b t) ν :=
      Measure.map_mono Measure.restrict_le_self b.continuous.measurable
    apply (integrable_brownian_weighted_radius_increment_field hh hε hεhalf hr hrε γ b g hg hgm hgs μ hμ).congr
    filter_upwards [hFspatial] with ω hω
    exact (hω b).symm
  have hRi : Integrable (R n) (planarBrownianMotion x) := (hA x n).1
  have hbound' : ∀ᵐ b ∂(planarBrownianMotion x), (∫ ω, ‖F (b,ω)‖ ∂P) ≤ R n b := by
    filter_upwards [hbound x] with b hb
    have heq : (∫ ω, ‖F (b,ω)‖ ∂P) = ∫ ω, |∫ z, g z *
        (r^(γ^2/2) * Real.exp (γ*(hcirc ω r z-hcirc ω 1 0)) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0)))
        ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
          (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic T)))| ∂P := by
      apply integral_congr_ae
      filter_upwards [hFspatial] with ω hω
      rw [hω b, Real.norm_eq_abs]
    rw [heq]
    let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    let μ : Measure ℂ := Measure.map (fun t => b t) (ν.restrict (Iic T))
    have hμ : μ ≤ Measure.map (fun t => b t) ν :=
      Measure.map_mono Measure.restrict_le_self b.continuous.measurable
    have h := hb g hg 1 zero_le_one hgm hgs μ hμ ε r hε hεhalf hr hrε hεr
    simpa only [one_pow, one_mul, mul_one, R, u, v, ε, μ, ν] using h
  have hsec : Integrable (fun b => ∫ ω, ‖F (b,ω)‖ ∂P) (planarBrownianMotion x) := by
    apply hRi.mono' (hFm.stronglyMeasurable.norm.integral_prod_right').aestronglyMeasurable
    filter_upwards [hbound'] with b hb
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hb
  have hFi : Integrable F ((planarBrownianMotion x).prod P) :=
    (integrable_prod_iff hFm.aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall hfield, hsec⟩
  refine ⟨F, hFm, hFspatial, hFi, ?_⟩
  calc
    _ = ∫ b, ∫ ω, ‖F (b,ω)‖ ∂P ∂(planarBrownianMotion x) := by
      simpa only [Real.norm_eq_abs] using integral_prod (fun q => |F q|) hFi.abs
    _ ≤ ∫ b, R n b ∂(planarBrownianMotion x) := integral_mono_ae hsec hRi hbound'
    _ = A n := (hA x n).2


/-- The nonpositive insertion weight on the half-disc is measurable,
bounded by one, and supported in the half-disc. -/
theorem nonpositive_halfDisc_insertion_weight_properties
    {γ α r : ℝ} (hγ : 0 ≤ γ) (hα : α ≤ 0) (hr : 0 < r) (hrhalf : r ≤ 1/2) :
    let g : ℂ → ℝ := {z : ℂ | ‖z‖ ≤ 1/2}.indicator
      (fun z => (max r ‖z‖) ^ (-γ*α))
    Measurable g ∧ (∀ z, |g z| ≤ 1) ∧ (∀ z, g z ≠ 0 → ‖z‖ ≤ 1/2) := by
  let A : Set ℂ := {z : ℂ | ‖z‖ ≤ 1/2}
  let g : ℂ → ℝ := A.indicator (fun z => (max r ‖z‖) ^ (-γ*α))
  have hA : MeasurableSet A := measurableSet_le measurable_norm measurable_const
  have hg : Measurable g := by
    apply Measurable.indicator _ hA
    exact ((continuous_const.max continuous_norm).rpow_const
      (fun _ => Or.inl (ne_of_gt (lt_max_of_lt_left hr)))).measurable
  have hq : 0 ≤ -γ * α := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hγ) hα
  change Measurable g ∧ (∀ z, |g z| ≤ 1) ∧ (∀ z, g z ≠ 0 → ‖z‖ ≤ 1/2)
  refine ⟨hg, ?_, ?_⟩
  · intro z
    by_cases hz : z ∈ A
    · rw [show g z = _ from Set.indicator_of_mem hz _]
      rw [abs_of_nonneg (Real.rpow_nonneg (le_of_lt (lt_max_of_lt_left hr)) _)]
      exact Real.rpow_le_one (le_of_lt (lt_max_of_lt_left hr))
        (by
          have hzhalf : ‖z‖ ≤ (1 : ℝ)/2 := hz
          apply max_le <;> linarith) hq
    · rw [show g z = 0 from Set.indicator_of_notMem hz _, abs_zero]
      norm_num
  · intro z hz
    by_contra hn
    have hnA : z ∉ A := hn
    exact hz (show g z = 0 from Set.indicator_of_notMem hnA _)


/-- The half-disc density increment splits into a weighted field increment
and a correction supported in the smoothing ball. -/
theorem nonpositive_halfDisc_radius_density_increment_split
    (h : ℝ → ℂ → ℝ) {γ α ε r : ℝ} (z : ℂ)
    (hγ : 0 ≤ γ) (hα : α ≤ 0) (hε : 0 < ε) (hεhalf : ε ≤ 1/2)
    (hr : 0 < r) (hrε : r ≤ ε) :
    {z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z =>
      r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α h r z) -
        ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α h ε z)) z =
    {z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z =>
      (max r ‖z‖)^(-γ*α) *
        (r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 h r z) -
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 h ε z))) z -
    {z : ℂ | ‖z‖ < ε}.indicator (fun z =>
      ((max ε ‖z‖)^(-γ*α) - (max r ‖z‖)^(-γ*α)) *
        (ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 h ε z))) z := by
  by_cases hz : ‖z‖ ≤ 1/2
  · have hs := nonpositive_insertion_radius_density_increment h γ α ε r z
      hγ hα hε hεhalf hr hrε hz
    dsimp only at hs
    rw [Set.indicator_of_mem (show z ∈ {w : ℂ | ‖w‖ ≤ 1/2} from hz),
      Set.indicator_of_mem (show z ∈ {w : ℂ | ‖w‖ ≤ 1/2} from hz)]
    by_cases hzε : ‖z‖ < ε
    · rw [Set.indicator_of_mem (show z ∈ {w : ℂ | ‖w‖ < ε} from hzε)]
      exact hs.2.2.2.2.2.2.1
    · rw [Set.indicator_of_notMem (show z ∉ {w : ℂ | ‖w‖ < ε} from hzε), sub_zero]
      have hzero := hs.2.2.2.2.2.1 (le_of_not_gt hzε)
      rw [hzero, zero_mul, sub_zero] at hs
      exact hs.2.2.2.2.2.2.1
  · have hzε : ¬ ‖z‖ < ε := by linarith
    rw [Set.indicator_of_notMem (show z ∉ {w : ℂ | ‖w‖ ≤ 1/2} from hz),
      Set.indicator_of_notMem (show z ∉ {w : ℂ | ‖w‖ ≤ 1/2} from hz),
      Set.indicator_of_notMem (show z ∉ {w : ℂ | ‖w‖ < ε} from hzε), sub_zero]


/-- A continuous density restricted to a measurable subset of the half-disc
is integrable against any finite spatial measure. -/
theorem integrable_indicator_continuous_of_halfDisc
    (μ : Measure ℂ) [IsFiniteMeasure μ] (S : Set ℂ) (hS : MeasurableSet S)
    (hSdisc : ∀ z ∈ S, ‖z‖ ≤ 1/2) (f : ℂ → ℝ) (hf : Continuous f) :
    Integrable (S.indicator f) μ := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (1/2 : ℝ)).bddAbove_image hf.norm.continuousOn
  apply (integrable_const (max K 0)).mono' (hf.measurable.indicator hS).aestronglyMeasurable
  filter_upwards with z
  by_cases hz : z ∈ S
  · have hzball : z ∈ Metric.closedBall (0 : ℂ) (1/2 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hSdisc z hz
    rw [Set.indicator_of_mem hz]
    exact (hK ⟨z, hzball, rfl⟩).trans (le_max_left K 0)
  · rw [Set.indicator_of_notMem hz, norm_zero]
    exact le_max_right K 0


private theorem continuous_fieldCircleAverage_of_continuous
    (h : ℝ → ℂ → ℝ) (α : ℝ) {r : ℝ} (hr : 0 < r) (hc : Continuous (h r)) :
    Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α h r z) := by
  have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α h r z) =
      (fun z => h r z - α * Real.log (max r ‖z‖)) := by
    funext z
    have hlog : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z r =
        Real.log (max r ‖z‖) := by
      simpa using (LatticeProb.Gauss.circleAverage_log_norm_sub_eq z 0 hr)
    dsimp [LatticeProb.Gauss.fieldCircleAverage]
    rw [hlog]
  rw [heq]
  exact hc.sub (continuous_const.mul
    ((continuous_const.max continuous_norm).log (fun _ => ne_of_gt (lt_max_of_lt_left hr))))

/-- Integrating the density split against a finite measure preserves the
weighted field term and the inner-ball correction. -/
theorem integral_nonpositive_halfDisc_radius_increment_split
    (μ : Measure ℂ) [IsFiniteMeasure μ] (h : ℝ → ℂ → ℝ) {γ α ε r : ℝ}
    (hγ : 0 ≤ γ) (hα : α ≤ 0) (hε : 0 < ε) (hεhalf : ε ≤ 1/2)
    (hr : 0 < r) (hrε : r ≤ ε) (hcr : Continuous (h r)) (hcε : Continuous (h ε)) :
    (∫ z, {z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z =>
      r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α h r z)) z ∂μ) -
    (∫ z, {z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z =>
      ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α h ε z)) z ∂μ) =
    (∫ z, {z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z =>
      (max r ‖z‖)^(-γ*α) *
        (r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 h r z) -
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 h ε z))) z ∂μ) -
    (∫ z, {z : ℂ | ‖z‖ < ε}.indicator (fun z =>
      ((max ε ‖z‖)^(-γ*α) - (max r ‖z‖)^(-γ*α)) *
        (ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 h ε z))) z ∂μ) := by
  let D : Set ℂ := {z : ℂ | ‖z‖ ≤ 1/2}
  let B : Set ℂ := {z : ℂ | ‖z‖ < ε}
  let Y : ℝ → ℂ → ℝ := fun s z => s^(γ^2/2) * Real.exp
    (γ * LatticeProb.Gauss.fieldCircleAverage α h s z)
  let X : ℝ → ℂ → ℝ := fun s z => s^(γ^2/2) * Real.exp
    (γ * LatticeProb.Gauss.fieldCircleAverage 0 h s z)
  let w : ℝ → ℂ → ℝ := fun s z => (max s ‖z‖)^(-γ*α)
  let U : ℂ → ℝ := fun z => w r z * (X r z - X ε z)
  let V : ℂ → ℝ := fun z => (w ε z - w r z) * X ε z
  have hD : MeasurableSet D := measurableSet_le measurable_norm measurable_const
  have hB : MeasurableSet B := measurableSet_lt measurable_norm measurable_const
  have hY (s : ℝ) (hs : 0 < s) (hc : Continuous (h s)) : Continuous (Y s) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (continuous_fieldCircleAverage_of_continuous h α hs hc)))
  have hX (s : ℝ) (hs : 0 < s) (hc : Continuous (h s)) : Continuous (X s) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (continuous_fieldCircleAverage_of_continuous h 0 hs hc)))
  have hw (s : ℝ) (hs : 0 < s) : Continuous (w s) :=
    (continuous_const.max continuous_norm).rpow_const
      (fun _ => Or.inl (ne_of_gt (lt_max_of_lt_left hs)))
  have hU : Continuous U := (hw r hr).mul ((hX r hr hcr).sub (hX ε hε hcε))
  have hV : Continuous V := ((hw ε hε).sub (hw r hr)).mul (hX ε hε hcε)
  have hDsub : ∀ z ∈ D, ‖z‖ ≤ 1/2 := fun _ hz => hz
  have hBsub : ∀ z ∈ B, ‖z‖ ≤ 1/2 := fun _ hz => le_trans (le_of_lt hz) hεhalf
  have hYr := integrable_indicator_continuous_of_halfDisc μ D hD hDsub (Y r) (hY r hr hcr)
  have hYε := integrable_indicator_continuous_of_halfDisc μ D hD hDsub (Y ε) (hY ε hε hcε)
  have hUi := integrable_indicator_continuous_of_halfDisc μ D hD hDsub U hU
  have hVi := integrable_indicator_continuous_of_halfDisc μ B hB hBsub V hV
  change (∫ z, D.indicator (Y r) z ∂μ) - (∫ z, D.indicator (Y ε) z ∂μ) =
    (∫ z, D.indicator U z ∂μ) - (∫ z, B.indicator V z ∂μ)
  rw [← integral_sub hYr hYε, ← integral_sub hUi hVi]
  apply integral_congr_ae
  filter_upwards with z
  have hs := nonpositive_halfDisc_radius_density_increment_split h z hγ hα hε hεhalf hr hrε
  change D.indicator (fun z => Y r z - Y ε z) z = D.indicator U z - B.indicator V z at hs
  simpa only [Set.indicator_sub, Pi.sub_apply] using hs


/-- On one field event, every stopped half-disc clock increment splits
into its weighted field increment and its inner-ball correction. -/
theorem ae_stopped_halfDisc_radius_increment_split
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {γ α : ℝ} (hγ : 0 ≤ γ) (hα : α ≤ 0) :
    ∀ᵐ ω ∂P, ∀ (b : ContinuousPath ℂ) (T : ℝ≥0) (ε r : ℝ),
      0 < ε → ε ≤ 1/2 → 0 < r → r ≤ ε →
      let μ := Measure.map (fun t => b t) ((Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic T))
      stoppedAnnularClock (fun z => r^(γ^2/2) * Real.exp
        (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)) 0 (fun _ => T) b -
      stoppedAnnularClock (fun z => ε^(γ^2/2) * Real.exp
        (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) 0 (fun _ => T) b =
      (∫ z, {z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z =>
        (max r ‖z‖)^(-γ*α) *
          (r^(γ^2/2) * Real.exp (γ*(hcirc ω r z-hcirc ω 1 0)) -
            ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0)))) z ∂μ) -
      (∫ z, {z : ℂ | ‖z‖ < ε}.indicator (fun z =>
        ((max ε ‖z‖)^(-γ*α) - (max r ‖z‖)^(-γ*α)) *
          (ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z))) z ∂μ) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [hHae, hh.ae_circleAverage_one_zero] with ω hω hzero
  intro b T ε r hε hεhalf hr hrε
  have hcont (s : ℝ) (hs : 0 < s) : Continuous (hcirc ω s) := by
    rw [← funext (hω s)]
    exact hHc ω s hs
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let μ : Measure ℂ := Measure.map (fun t => b t) (ν.restrict (Iic T))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  have hμ : μ ≤ Measure.map (fun t => b t) ν :=
    Measure.map_mono Measure.restrict_le_self b.continuous.measurable
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le (Measure.map (fun t => b t) ν) hμ
  have hsplit := integral_nonpositive_halfDisc_radius_increment_split μ (hcirc ω)
    hγ hα hε hεhalf hr hrε (hcont r hr) (hcont ε hε)
  have hzero' (s : ℝ) (z : ℂ) : LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) s z =
      hcirc ω s z - hcirc ω 1 0 := by
    simp [LatticeProb.Gauss.fieldCircleAverage, hzero]
  simp only [hzero'] at hsplit
  change (∫ z, {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator _ z ∂μ) -
    (∫ z, {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator _ z ∂μ) = _
  simpa only [norm_nonneg, true_and, hzero'] using hsplit


/-- The stopped spatial insertion correction is nonnegative and bounded by
the nonnegative occupation of the entire unit interval. -/
theorem ae_stopped_nonpositive_radius_correction_le_unit_occupation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {γ α : ℝ} (hγ : 0 ≤ γ) (hα : α ≤ 0) :
    ∀ᵐ ω ∂P, ∀ (b : ContinuousPath ℂ) (T : ℝ≥0) (ε r : ℝ),
      0 < ε → ε ≤ 1/2 → 0 < r → r ≤ ε →
      let f : ℂ → ℝ := fun z =>
        ((max ε ‖z‖)^(-γ*α) - (max r ‖z‖)^(-γ*α)) *
          (ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z))
      let μ := Measure.map (fun t => b t) ((Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic T))
      0 ≤ (∫ z, {z : ℂ | ‖z‖ < ε}.indicator f z ∂μ) ∧
      ENNReal.ofReal (∫ z, {z : ℂ | ‖z‖ < ε}.indicator f z ∂μ) ≤
        ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < ε}.indicator f (b s.toNNReal)) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [hHae] with ω hω
  intro b T ε r hε hεhalf hr hrε
  let f : ℂ → ℝ := fun z =>
    ((max ε ‖z‖)^(-γ*α) - (max r ‖z‖)^(-γ*α)) *
      (ε^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z))
  have hc : Continuous (hcirc ω ε) := by
    rw [← funext (hω ε)]
    exact hHc ω ε hε
  have hw (s : ℝ) (hs : 0 < s) : Continuous (fun z : ℂ => (max s ‖z‖)^(-γ*α)) :=
    (continuous_const.max continuous_norm).rpow_const
      (fun _ => Or.inl (ne_of_gt (lt_max_of_lt_left hs)))
  have hf : Continuous f := by
    dsimp [f]
    exact ((hw ε hε).sub (hw r hr)).mul (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul
        (continuous_fieldCircleAverage_of_continuous (hcirc ω) 0 hε hc))))
  have hq : 0 ≤ -γ * α := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hγ) hα
  have hf0 (z : ℂ) : 0 ≤ f z := by
    dsimp [f]
    apply mul_nonneg _ (mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le)
    apply sub_nonneg.mpr
    exact Real.rpow_le_rpow (le_of_lt (lt_max_of_lt_left hr)) (max_le_max_right _ hrε) hq
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let μ : Measure ℂ := Measure.map (fun t => b t) (ν.restrict (Iic T))
  let ρ : Measure ℂ := Measure.map (fun t => b t) ν
  have hμ : μ ≤ ρ := Measure.map_mono Measure.restrict_le_self b.continuous.measurable
  have hfull := inner_indicator_integrable_and_lintegral_eq b f hf hf0 hεhalf
  have hnonneg (z : ℂ) : 0 ≤ {z : ℂ | ‖z‖ < ε}.indicator f z := by
    by_cases hz : ‖z‖ < ε
    · simpa [hz] using hf0 z
    · simp [hz]
  refine ⟨integral_nonneg hnonneg, ?_⟩
  rw [hfull.2]
  apply ENNReal.ofReal_le_ofReal
  exact integral_mono_measure hμ (Filter.Eventually.of_forall hnonneg) hfull.1


/-- Same-shell nonpositive half-disc clock differences satisfy an annealed
geometric field bound plus a small-ball correction, uniformly in the start
and deterministic stopping horizon. -/
theorem exists_uniform_annealed_nonpositive_halfDisc_radius_increment_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2) :
    ∃ A : ℕ → ℝ, Summable A ∧ (∀ n, 0 ≤ A n) ∧
      (∃ c u v : ℝ, 0 ≤ c ∧ 0 < u ∧ 0 < v ∧ ∀ n,
        A n = c * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * u) +
          2 * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * v)) ∧
      ∀ α : ℝ, α ≤ 0 → ∃ C : ℝ≥0∞, 0 < C ∧ C < ∞ ∧
      ∀ (n : ℕ) (x : ℂ) (r : ℝ), 0 < r → r ≤ (2 : ℝ)⁻¹ ^ (n+1) →
        (2 : ℝ)⁻¹ ^ (n+1) / 2 ≤ r → ∀ T : ℝ≥0,
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        (∫⁻ p : Ω × ContinuousPath ℂ, ENNReal.ofReal |stoppedAnnularClock
          (fun z => r^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z)) 0 (fun _ => T) p.2 -
          stoppedAnnularClock (fun z => ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) 0 (fun _ => T) p.2|
          ∂(P.prod (planarBrownianMotion x))) ≤
        ENNReal.ofReal (A n) + ENNReal.ofReal (ε ^ (-γ*α)) *
          ((ENNReal.ofReal ε) ^ (1/2 : ℝ) * C) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hγlt2 : γ < 2 := by nlinarith [sq_nonneg (γ - 2)]
  obtain ⟨A, hAs, hA0, hAgeom, hweighted⟩ :=
    exists_uniform_summable_annealed_weighted_radius_increments hh hγ hγlt2
  refine ⟨A, hAs, hA0, hAgeom, ?_⟩
  intro α hα
  obtain ⟨C, hC0, hC, hcor⟩ :=
    exists_uniform_annealed_nonpositive_radius_insertion_correction_le hh γ α hγ hα
  refine ⟨C, hC0, hC, ?_⟩
  intro n x r hr hrε hεr T
  let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεhalf : ε ≤ 1/2 := by
    dsimp [ε]
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  let g : ℂ → ℝ := {z : ℂ | ‖z‖ ≤ 1/2}.indicator
    (fun z => (max r ‖z‖)^(-γ*α))
  have hg := nonpositive_halfDisc_insertion_weight_properties hγ.le hα hr (le_trans hrε hεhalf)
  obtain ⟨F, hFm, hFspatial, hFi, hFbound⟩ :=
    hweighted n x g hg.1 hg.2.1 hg.2.2 r hr hrε hεr T
  have hFmeas : Measurable (fun p : Ω × ContinuousPath ℂ =>
      ENNReal.ofReal |F (p.2,p.1)|) := ENNReal.measurable_ofReal.comp ((hFm.comp measurable_swap).abs)
  have hFbound' : (∫⁻ p : Ω × ContinuousPath ℂ, ENNReal.ofReal |F (p.2,p.1)|
      ∂(P.prod (planarBrownianMotion x))) ≤ ENNReal.ofReal (A n) := by
    rw [lintegral_prod_symm _ hFmeas.aemeasurable]
    have hswap : (∫⁻ b, ∫⁻ ω, ENNReal.ofReal |F (b,ω)| ∂P ∂(planarBrownianMotion x)) =
        ∫⁻ q : ContinuousPath ℂ × Ω, ENNReal.ofReal |F q|
          ∂((planarBrownianMotion x).prod P) := by
      symm
      exact lintegral_prod _ ((ENNReal.measurable_ofReal.comp hFm.abs).aemeasurable)
    rw [hswap, ← ofReal_integral_eq_lintegral_ofReal hFi.abs
      (Filter.Eventually.of_forall (fun q => abs_nonneg (F q)))]
    exact ENNReal.ofReal_le_ofReal hFbound
  have hpoint : ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ENNReal.ofReal |stoppedAnnularClock
      (fun z => r^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z)) 0 (fun _ => T) p.2 -
      stoppedAnnularClock (fun z => ε^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) 0 (fun _ => T) p.2| ≤
      ENNReal.ofReal |F (p.2,p.1)| + ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < ε}.indicator (fun z =>
          ((max ε ‖z‖)^(-γ*α) - (max r ‖z‖)^(-γ*α)) *
            (ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc p.1) ε z))) (p.2 s.toNNReal)) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P)
      (ν := planarBrownianMotion x)).ae (ae_stopped_halfDisc_radius_increment_split hh hγ.le hα),
      (Measure.quasiMeasurePreserving_fst (μ := P)
        (ν := planarBrownianMotion x)).ae (ae_stopped_nonpositive_radius_correction_le_unit_occupation hh hγ.le hα),
      (Measure.quasiMeasurePreserving_fst (μ := P)
        (ν := planarBrownianMotion x)).ae hFspatial] with p hs hc hf
    let μ : Measure ℂ := Measure.map (fun t => p.2 t) ((Measure.map Real.toNNReal
      (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic T))
    let V : ℂ → ℝ := fun z =>
      ((max ε ‖z‖)^(-γ*α) - (max r ‖z‖)^(-γ*α)) *
        (ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc p.1) ε z))
    let K : ℝ := ∫ z, {z : ℂ | ‖z‖ < ε}.indicator V z ∂μ
    have hK : 0 ≤ K ∧ ENNReal.ofReal K ≤ ∫⁻ s in Ioc (0 : ℝ) 1,
        ENNReal.ofReal ({z : ℂ | ‖z‖ < ε}.indicator V (p.2 s.toNNReal)) :=
      hc p.2 T ε r hε hεhalf hr hrε
    have hF : F (p.2,p.1) = ∫ z, {z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z =>
        (max r ‖z‖)^(-γ*α) *
          (r^(γ^2/2) * Real.exp (γ*(hcirc p.1 r z-hcirc p.1 1 0)) -
            ε^(γ^2/2) * Real.exp (γ*(hcirc p.1 ε z-hcirc p.1 1 0)))) z ∂μ := by
      rw [hf p.2]
      apply integral_congr_ae
      filter_upwards with z
      simp only [g, Set.indicator_apply]
      split_ifs <;> simp [ε]
    have hsplit := hs p.2 T ε r hε hεhalf hr hrε
    change _ = _ - K at hsplit
    rw [← hF] at hsplit
    rw [hsplit]
    calc
      ENNReal.ofReal |F (p.2,p.1) - K| ≤ ENNReal.ofReal (|F (p.2,p.1)| + K) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          _ ≤ |F (p.2,p.1)| + |K| := by simpa using (abs_sub_le (F (p.2,p.1)) 0 K)
          _ = _ := by rw [abs_of_nonneg hK.1]
      _ = ENNReal.ofReal |F (p.2,p.1)| + ENNReal.ofReal K :=
        ENNReal.ofReal_add (abs_nonneg _) hK.1
      _ ≤ _ := add_le_add le_rfl hK.2
  calc
    _ ≤ ∫⁻ p : Ω × ContinuousPath ℂ, (ENNReal.ofReal |F (p.2,p.1)| +
      ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal ({z : ℂ | ‖z‖ < ε}.indicator (fun z =>
        ((max ε ‖z‖)^(-γ*α) - (max r ‖z‖)^(-γ*α)) *
          (ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc p.1) ε z))) (p.2 s.toNNReal)))
      ∂(P.prod (planarBrownianMotion x)) := lintegral_mono_ae hpoint
    _ = (∫⁻ p : Ω × ContinuousPath ℂ, ENNReal.ofReal |F (p.2,p.1)|
      ∂(P.prod (planarBrownianMotion x))) +
      (∫⁻ p : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < ε}.indicator (fun z =>
          ((max ε ‖z‖)^(-γ*α) - (max r ‖z‖)^(-γ*α)) *
            (ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc p.1) ε z))) (p.2 s.toNNReal)))
        ∂(P.prod (planarBrownianMotion x))) := lintegral_add_left hFmeas _
    _ ≤ _ := add_le_add hFbound' (hcor x hε hεhalf hεhalf hr hrε)


/-- A same-shell half-disc clock supremum has a time-mesh bound with
explicit geometric field and small-ball terms. -/
theorem exists_uniform_annealed_nonpositive_halfDisc_radius_iSup_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2) :
    ∃ (A : ℕ → ℝ) (C D : ℝ≥0∞) (β : ℝ), Summable A ∧ (∀ n, 0 ≤ A n) ∧
      (∃ c u v : ℝ, 0 ≤ c ∧ 0 < u ∧ 0 < v ∧ ∀ n,
        A n = c * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * u) +
          2 * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * v)) ∧
      C < ∞ ∧ D < ∞ ∧ 0 < β ∧
      ∀ α : ℝ, α ≤ 0 → ∃ E : ℝ≥0∞, 0 < E ∧ E < ∞ ∧
      ∀ (n : ℕ) (x : ℂ) (r : ℝ), 0 < r → r ≤ (2 : ℝ)⁻¹ ^ (n+1) →
        (2 : ℝ)⁻¹ ^ (n+1) / 2 ≤ r → ∀ (m : ℕ), 0 < m →
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        let F : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
          stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) 0
            (fun _ => t.toNNReal) p.2
        (∫⁻ p, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |F r p t - F ε p t|
          ∂(P.prod (planarBrownianMotion x))) ≤
        (m + 1 : ℝ≥0∞) * (ENNReal.ofReal (A n) + ENNReal.ofReal (ε ^ (-γ*α)) *
          ((ENNReal.ofReal ε) ^ (1/2 : ℝ) * E)) +
          (C * (m : ℝ≥0∞) ^ (-β) + (ENNReal.ofReal ε) ^ (1/2 : ℝ) * D) := by
  obtain ⟨A, hAs, hA0, hAgeom, hfixed⟩ :=
    exists_uniform_annealed_nonpositive_halfDisc_radius_increment_le hh hγ hγ2
  obtain ⟨C, D, β, hC, hD, hβ, hmesh⟩ :=
    exists_uniform_prod_nonpositive_halfDisc_clock_iSup_le_grid hh hγ hγ2
  refine ⟨A, C, D, β, hAs, hA0, hAgeom, hC, hD, hβ, ?_⟩
  intro α hα
  obtain ⟨E, hE0, hE, hbound⟩ := hfixed α hα
  refine ⟨E, hE0, hE, ?_⟩
  intro n x r hr hrε hεr m hm
  let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεhalf : ε ≤ 1/2 := by
    dsimp [ε]
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  let F : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
    stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) 0 (fun _ => t.toNNReal) p.2
  let B : ℝ≥0∞ := ENNReal.ofReal (A n) + ENNReal.ofReal (ε ^ (-γ*α)) *
    ((ENNReal.ofReal ε) ^ (1/2 : ℝ) * E)
  have hgrid (j : ℕ) :
      (∫⁻ p, ENNReal.ofReal |F r p (j / (m : ℝ)) - F ε p (j / (m : ℝ))|
        ∂(P.prod (planarBrownianMotion x))) ≤ B := by
    exact hbound n x r hr hrε hεr ((j / (m : ℝ)).toNNReal)
  have hsum : (∑ j ∈ Finset.range (m+1), ∫⁻ p, ENNReal.ofReal
        |F r p (j / (m : ℝ)) - F ε p (j / (m : ℝ))|
        ∂(P.prod (planarBrownianMotion x))) ≤ (m + 1 : ℝ≥0∞) * B := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (m+1), B := Finset.sum_le_sum (fun j _ => hgrid j)
      _ = _ := by simp [nsmul_eq_mul]
  have h := hmesh x α hα hr hε hεhalf m hm
  exact h.trans (add_le_add hsum le_rfl)


/-- Positive time and radius grid exponents can be chosen below the field,
small-ball, and mesh decay rates. -/
theorem exists_nonpositive_halfDisc_grid_exponents {u v β : ℝ}
    (hu : 0 < u) (hv : 0 < v) (hβ : 0 < β) :
    ∃ p b c : ℝ, 0 < p ∧ p ≤ u ∧ p ≤ v ∧ p ≤ 1/2 ∧
      0 < b ∧ 0 < c ∧ c ≤ p - b/2 ∧ c ≤ b*β/2 := by
  let p : ℝ := min u (min v (1/2))
  let b : ℝ := p
  let c : ℝ := min (p/4) (p*β/4)
  have hp : 0 < p := by dsimp [p]; positivity
  have hpu : p ≤ u := min_le_left _ _
  have hpv : p ≤ v := (min_le_right _ _).trans (min_le_left _ _)
  have hp2 : p ≤ 1/2 := (min_le_right _ _).trans (min_le_right _ _)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨p, b, c, hp, hpu, hpv, hp2, by simpa [b] using hp, hc, ?_, ?_⟩
  · have h := min_le_left (p/4) (p*β/4)
    dsimp [b, c] at *
    linarith
  · have h := min_le_right (p/4) (p*β/4)
    have hpb : 0 < p*β := mul_pos hp hβ
    dsimp [b, c] at *
    linarith


/-- The combined time and radius grid rate is summable after shifting the
dyadic index. -/
theorem summable_nonpositive_halfDisc_grid_mesh {p β b c A D : ℝ}
    (hβ : 0 < β) (hb : 0 < b) (hc : 0 < c)
    (hcp : c ≤ p - b / 2) (hcβ : c ≤ b * β / 2)
    (hA : 0 ≤ A) (hD : 0 ≤ D) :
    Summable (fun n : ℕ => ((gridCount c (n+1) : ℝ) + 1) *
      ((((gridCount b (n+1) : ℝ) + 1) + 1) *
        (A * LatticeProb.LQG.dyadicScale (n+1) ^ p) +
          D * (((gridCount b (n+1) : ℝ) + 1) ^ (-β)))) := by
  have hs := summable_annular_grid_mesh (p := p) (q := p) (β := β)
    (b := b) (c := c) (A := A) (B := 0) (D := D)
    hβ hb hc hcp hcp hcβ hA le_rfl hD
  have hs' := (summable_nat_add_iff 1).2 hs
  simpa only [zero_mul, add_zero] using hs'


/-- A common positive power absorbs the field, correction, and inner mesh
rates in the uniform-time estimate. -/
theorem nonpositive_halfDisc_mesh_rate_le
    {e q p u v c β : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hq : 0 ≤ q)
    (hpu : p ≤ u) (hpv : p ≤ v) (hp2 : p ≤ 1/2) (hc : 0 ≤ c)
    (C D E : ℝ≥0∞) (m : ℕ) :
    (m + 1 : ℝ≥0∞) * (ENNReal.ofReal (c*e^u + 2*e^v) +
      ENNReal.ofReal (e^q) * ((ENNReal.ofReal e) ^ (1/2 : ℝ) * E)) +
      (C * (m : ℝ≥0∞)^(-β) + (ENNReal.ofReal e) ^ (1/2 : ℝ) * D) ≤
    (m + 1 : ℝ≥0∞) *
      ((ENNReal.ofReal c + 2 + E + D) * ENNReal.ofReal (e^p)) +
      C * (m : ℝ≥0∞)^(-β) := by
  let W : ℝ≥0∞ := ENNReal.ofReal (e^p)
  have hu : e^u ≤ e^p := Real.rpow_le_rpow_of_exponent_ge he he1 hpu
  have hv : e^v ≤ e^p := Real.rpow_le_rpow_of_exponent_ge he he1 hpv
  have h2 : e^(1/2 : ℝ) ≤ e^p := Real.rpow_le_rpow_of_exponent_ge he he1 hp2
  have hq1 : e^q ≤ 1 := Real.rpow_le_one he.le he1 hq
  have hscale : (ENNReal.ofReal e) ^ (1/2 : ℝ) ≤ W := by
    rw [ENNReal.ofReal_rpow_of_pos he]
    exact ENNReal.ofReal_le_ofReal h2
  have hweight : ENNReal.ofReal (e^q) ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal hq1
  have hfield : ENNReal.ofReal (c*e^u + 2*e^v) ≤ (ENNReal.ofReal c + 2)*W := by
    have hreal : c*e^u + 2*e^v ≤ (c+2)*e^p := by
      nlinarith [mul_nonneg hc (sub_nonneg.mpr hu)]
    calc
      _ ≤ ENNReal.ofReal ((c+2)*e^p) := ENNReal.ofReal_le_ofReal hreal
      _ = _ := by rw [ENNReal.ofReal_mul (by linarith : 0 ≤ c+2),
        ENNReal.ofReal_add hc (by norm_num)]; norm_num [W]
  have hcor : ENNReal.ofReal (e^q) * ((ENNReal.ofReal e) ^ (1/2 : ℝ) * E) ≤ E*W := by
    calc
      _ ≤ 1 * (W*E) := by gcongr
      _ = _ := by ac_rfl
  have hinner : (ENNReal.ofReal e) ^ (1/2 : ℝ) * D ≤
      (m + 1 : ℝ≥0∞) * (D*W) := by
    calc
      _ ≤ W*D := by gcongr
      _ = D*W := mul_comm _ _
      _ ≤ (m + 1 : ℝ≥0∞) * (D*W) := by
        calc
          _ = 1 * (D*W) := by simp
          _ ≤ _ := by gcongr; simp
  calc
    _ ≤ (m + 1 : ℝ≥0∞) * ((ENNReal.ofReal c + 2)*W + E*W) +
        (C * (m : ℝ≥0∞)^(-β) + (m + 1 : ℝ≥0∞) * (D*W)) := by gcongr
    _ = _ := by ring


/-- Finite mesh coefficients convert the nonnegative extended-real rate
to its real-valued expression. -/
theorem nonpositive_halfDisc_grid_rate_to_ofReal
    (N m : ℕ) (hm : 0 < m) (K C : ℝ≥0∞) (hK : K < ∞) (hC : C < ∞)
    (e p β : ℝ) (he : 0 < e) :
    (N : ℝ≥0∞) * ((m + 1 : ℝ≥0∞) * (K * ENNReal.ofReal (e^p)) +
      C * (m : ℝ≥0∞)^(-β)) =
    ENNReal.ofReal ((N : ℝ) * (((m : ℝ) + 1) * (K.toReal * e^p) +
      C.toReal * ((m : ℝ)^(-β)))) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hepow : 0 ≤ e^p := (Real.rpow_pos_of_pos he _).le
  have hmpow : 0 ≤ (m : ℝ)^(-β) := (Real.rpow_pos_of_pos hm0 _).le
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ N),
    ENNReal.ofReal_natCast, ENNReal.ofReal_add (by positivity)
      (mul_nonneg ENNReal.toReal_nonneg hmpow),
    ENNReal.ofReal_mul (by positivity : 0 ≤ (m : ℝ) + 1),
    ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hK.ne, ENNReal.ofReal_toReal hC.ne,
    ← ENNReal.ofReal_rpow_of_pos hm0, ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_add (by positivity : 0 ≤ (m : ℝ)) (by positivity : (0 : ℝ) ≤ 1),
    ENNReal.ofReal_natCast, ENNReal.ofReal_one]


/-- Unit-time same-shell nonpositive clock increments have summable
expectations over a geometric radius grid. -/
theorem exists_tsum_nonpositive_halfDisc_radius_grid_clock_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2) (α : ℝ) (hα : α ≤ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℂ,
      let F : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
        stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) 0
            (fun _ => t.toNNReal) p.2
      (∑' n : ℕ, ∑ i ∈ Finset.range (gridCount c (n+1) + 1),
        ∫⁻ p, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal
          |F (gridScale (gridCount c) (n+1) i) p t -
            F (LatticeProb.LQG.dyadicScale (n+1)) p t|
          ∂(P.prod (planarBrownianMotion x))) < ⊤ := by
  obtain ⟨A, C, D, β, hAs, hA0, hAgeom, hC, hD, hβ, hbound⟩ :=
    exists_uniform_annealed_nonpositive_halfDisc_radius_iSup_le hh hγ hγ2
  obtain ⟨a, u, v, ha, hu, hv, hAexpr⟩ := hAgeom
  obtain ⟨p, b, c, hp, hpu, hpv, hp2, hb, hc, hcp, hcβ⟩ :=
    exists_nonpositive_halfDisc_grid_exponents hu hv hβ
  obtain ⟨E, hE0, hE, hclock⟩ := hbound α hα
  let K : ℝ≥0∞ := ENNReal.ofReal a + 2 + E + D
  have hK : K < ∞ := by
    dsimp [K]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
      ⟨ENNReal.ofReal_lt_top, by norm_num⟩, hE⟩, hD⟩
  have hseries := summable_nonpositive_halfDisc_grid_mesh (p := p) (β := β)
    (b := b) (c := c) (A := K.toReal) (D := C.toReal)
    hβ hb hc hcp hcβ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hq : 0 ≤ -γ*α := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hγ.le) hα
  refine ⟨c, hc, ?_⟩
  intro x
  dsimp only
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum (g := fun n : ℕ =>
    ENNReal.ofReal (((gridCount c (n+1) : ℝ) + 1) *
      ((((gridCount b (n+1) : ℝ) + 1) + 1) *
        (K.toReal * LatticeProb.LQG.dyadicScale (n+1) ^ p) +
          C.toReal * (((gridCount b (n+1) : ℝ) + 1) ^ (-β))))) (fun n => ?_)) ?_
  · let k : ℕ := n+1
    let e : ℝ := LatticeProb.LQG.dyadicScale k
    let m : ℕ := gridCount b k + 1
    let N : ℕ := gridCount c k + 1
    have he : 0 < e := by dsimp [e, LatticeProb.LQG.dyadicScale]; positivity
    have he1 : e ≤ 1 := by
      dsimp [e, LatticeProb.LQG.dyadicScale]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have hm : 0 < m := by dsimp [m]; omega
    have hrate (i : ℕ) (hi : i ∈ Finset.range N) := by
      have hi' : i ≤ gridCount c k := by
        dsimp [N] at hi
        exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hgrid := gridScale_mem_Icc (gridCount c) hi'
      have hr : 0 < gridScale (gridCount c) k i := (half_pos he).trans_le hgrid.1
      have h := hclock n x (gridScale (gridCount c) k i) hr hgrid.2 hgrid.1 m hm
      have hpowu : Real.exp (Real.log e * u) = e^u := (Real.rpow_def_of_pos he u).symm
      have hpowv : Real.exp (Real.log e * v) = e^v := (Real.rpow_def_of_pos he v).symm
      rw [hAexpr n] at h
      change _ ≤ (m + 1 : ℝ≥0∞) * (ENNReal.ofReal
        (a * Real.exp (Real.log e * u) + 2 * Real.exp (Real.log e * v)) +
        ENNReal.ofReal (e^(-γ*α)) * ((ENNReal.ofReal e)^(1/2 : ℝ)*E)) +
        (C * (m : ℝ≥0∞)^(-β) + (ENNReal.ofReal e)^(1/2 : ℝ)*D) at h
      rw [hpowu, hpowv] at h
      exact h.trans (nonpositive_halfDisc_mesh_rate_le he he1 hq hpu hpv hp2 ha C D E m)
    calc
      _ ≤ ∑ _i ∈ Finset.range N,
          ((m + 1 : ℝ≥0∞) * (K * ENNReal.ofReal (e^p)) +
            C * (m : ℝ≥0∞)^(-β)) := Finset.sum_le_sum (fun i hi => hrate i hi)
      _ = (N : ℝ≥0∞) * ((m + 1 : ℝ≥0∞) * (K * ENNReal.ofReal (e^p)) +
            C * (m : ℝ≥0∞)^(-β)) := by simp [nsmul_eq_mul, mul_add]
      _ = ENNReal.ofReal ((N : ℝ) * (((m : ℝ) + 1) * (K.toReal * e^p) +
          C.toReal * ((m : ℝ)^(-β)))) :=
        nonpositive_halfDisc_grid_rate_to_ofReal N m hm K C hK hC e p β he
      _ = _ := by dsimp [N, m, e, k]; push_cast; rfl
  · exact hseries.tsum_ofReal_lt_top


/-- At every Brownian start, the unit-time radius-grid errors are summable
on a product-full event. -/
theorem exists_ae_tsum_nonpositive_halfDisc_radius_grid_clock_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2) (α : ℝ) (hα : α ≤ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℂ,
      ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      let F : ℝ → ℝ → ℝ := fun v t =>
        stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) 0
            (fun _ => t.toNNReal) p.2
      (∑' n : ℕ, ∑ i ∈ Finset.range (gridCount c (n+1) + 1),
        ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal
          |F (gridScale (gridCount c) (n+1) i) t -
            F (LatticeProb.LQG.dyadicScale (n+1)) t|) < ⊤ := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_tsum_nonpositive_halfDisc_radius_grid_clock_lt_top hh hγ hγ2 α hα
  refine ⟨c, hc, ?_⟩
  intro x
  let F : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
    stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) 0
        (fun _ => t.toNNReal) p.2
  let S : ℕ → ℕ → (Ω × ContinuousPath ℂ) → ℝ≥0∞ := fun n i p =>
    ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal
      |F (gridScale (gridCount c) (n+1) i) p t -
        F (LatticeProb.LQG.dyadicScale (n+1)) p t|
  have hS (n i : ℕ) (hi : i ∈ Finset.range (gridCount c (n+1) + 1)) :
      AEMeasurable (S n i) (P.prod (planarBrownianMotion x)) := by
    have hi' : i ≤ gridCount c (n+1) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have he : 0 < LatticeProb.LQG.dyadicScale (n+1) := by
      dsimp [LatticeProb.LQG.dyadicScale]; positivity
    have hr : 0 < gridScale (gridCount c) (n+1) i :=
      (half_pos he).trans_le (gridScale_mem_Icc (gridCount c) hi').1
    simpa only [S, F, ContinuousPath.shift_zero] using
      (aemeasurable_shift_annular_radius_iSup hh x 0 γ α 0 hr he)
  have hm (n : ℕ) : AEMeasurable (fun p => ∑ i ∈ Finset.range (gridCount c (n+1) + 1), S n i p)
      (P.prod (planarBrownianMotion x)) :=
    Finset.aemeasurable_fun_sum _ fun i hi => hS n i hi
  have hint : (∫⁻ p, ∑' n, ∑ i ∈ Finset.range (gridCount c (n+1) + 1), S n i p
      ∂(P.prod (planarBrownianMotion x))) < ⊤ := by
    rw [lintegral_tsum hm]
    simp_rw [lintegral_finsetSum' _ (fun i hi => hS _ i hi)]
    exact hbound x
  exact ae_lt_top' (AEMeasurable.tsum hm) hint.ne


private def nonpositiveUnitRationalTime (q : ℚ) : Icc (0 : ℝ) 1 :=
  ⟨min 1 (max (q : ℝ) 0), ⟨le_min (by norm_num) (le_max_right _ _), min_le_left _ _⟩⟩

private theorem nonpositive_unit_iSup_eq_rational (f : ℝ → ℝ≥0∞) (hf : Continuous f) :
    (⨆ t : Icc (0 : ℝ) 1, f t) = ⨆ q : ℚ, f (nonpositiveUnitRationalTime q) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    have hc : Continuous (fun x : ℝ => f (min 1 (max x 0))) :=
      hf.comp (continuous_const.min (continuous_id.max continuous_const))
    have hclosed : IsClosed {x : ℝ | f (min 1 (max x 0)) ≤ ⨆ q : ℚ, f (nonpositiveUnitRationalTime q)} :=
      isClosed_le hc continuous_const
    have hall : ∀ x : ℝ, f (min 1 (max x 0)) ≤ ⨆ q : ℚ, f (nonpositiveUnitRationalTime q) := by
      intro x
      refine Rat.denseRange_cast.induction_on x hclosed ?_
      intro q
      exact le_iSup (fun q : ℚ => f (nonpositiveUnitRationalTime q)) q
    simpa only [max_eq_left t.property.1, min_eq_right t.property.2] using hall t
  · apply iSup_le
    intro q
    exact le_iSup (fun t : Icc (0 : ℝ) 1 => f t) (nonpositiveUnitRationalTime q)

/-- Radius-grid errors remain summable on every integer-shifted unit block. -/
theorem exists_ae_tsum_nonpositive_halfDisc_shifted_radius_grid_clock_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2) (α : ℝ) (hα : α ≤ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℂ,
      ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)), ∀ j : ℕ,
      let F : ℝ → ℝ → ℝ := fun v t =>
        stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) 0
            (fun _ => t.toNNReal) (ContinuousPath.shift j p.2)
      (∑' n : ℕ, ∑ i ∈ Finset.range (gridCount c (n+1) + 1),
        ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal
          |F (gridScale (gridCount c) (n+1) i) t -
            F (LatticeProb.LQG.dyadicScale (n+1)) t|) < ⊤ := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨c, hc, hbase⟩ :=
    exists_ae_tsum_nonpositive_halfDisc_radius_grid_clock_lt_top hh hγ hγ2 α hα
  let ε : ℕ → ℝ := fun n => LatticeProb.LQG.dyadicScale (n+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε, LatticeProb.LQG.dyadicScale]; positivity
  let r : ℕ → ℕ → ℝ := fun n i =>
    if i ≤ gridCount c (n+1) then gridScale (gridCount c) (n+1) i else ε n
  have hr (n i : ℕ) : 0 < r n i := by
    dsimp [r]
    split_ifs with hi
    · exact (half_pos (hε n)).trans_le (gridScale_mem_Icc (gridCount c) hi).1
    · exact hε n
  let τ : ℚ → ContinuousPath ℂ → ℝ≥0 := fun q _ =>
    ((nonpositiveUnitRationalTime q : Icc (0 : ℝ) 1) : ℝ).toNNReal
  have hexists (n i : ℕ) (q : ℚ) : ∃ F : ContinuousPath ℂ × Ω → ℝ, Measurable F ∧
      ∀ᵐ ω ∂P, ∀ b, F (b,ω) =
        annularRadiusIncrementSample hcirc γ α 0 (ε n) (r n i) (τ q) b ω :=
    exists_measurable_annularRadiusIncrementSample hh (hε n) (hr n i) γ α 0 (τ q) measurable_const
  choose G hGm hGae using hexists
  have hGall : ∀ᵐ ω ∂P, ∀ n i q b, G n i q (b,ω) =
      annularRadiusIncrementSample hcirc γ α 0 (ε n) (r n i) (τ q) b ω := by
    exact ae_all_iff.mpr fun n => ae_all_iff.mpr fun i => ae_all_iff.mpr fun q => hGae n i q
  let M : ℕ → ℕ → (Ω × ContinuousPath ℂ) → ℝ≥0∞ := fun n i p =>
    ⨆ q : ℚ, ENNReal.ofReal |G n i q (p.2,p.1)|
  have hMm (n i : ℕ) : Measurable (M n i) := by
    apply Measurable.iSup
    intro q
    exact ENNReal.measurable_ofReal.comp ((hGm n i q).comp measurable_swap).abs
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hMfield : ∀ᵐ ω ∂P, ∀ b n i, i ≤ gridCount c (n+1) →
      M n i (ω,b) = ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |stoppedAnnularClock
        (fun z => (gridScale (gridCount c) (n+1) i)^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (gridScale (gridCount c) (n+1) i) z)) 0
          (fun _ => ((t : ℝ).toNNReal)) b -
        stoppedAnnularClock (fun z => (ε n)^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε n) z)) 0
          (fun _ => ((t : ℝ).toNNReal)) b| := by
    filter_upwards [hGall, hHae, ae_stoppedAnnularClock_sub_eq_annularRadiusIncrementSample hh γ α 0]
      with ω hG hω hsub
    intro b n i hi
    have hre : r n i = gridScale (gridCount c) (n+1) i := by simp [r, hi]
    have hcont (v : ℝ) (hv : 0 < v) : Continuous (fun t : ℝ =>
        stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) v z)) 0 (fun _ => t.toNNReal) b) := by
      have hc : Continuous (hcirc ω v) := by
        rw [← funext (hω v)]
        exact hHc ω v hv
      have hd : Continuous (fun z => v^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) v z)) :=
        continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
          (continuous_fieldCircleAverage_of_continuous (hcirc ω) α hv hc)))
      exact continuous_stoppedAnnularClock_time _ hd 0 b
    have hcF : Continuous (fun t : ℝ => ENNReal.ofReal |stoppedAnnularClock
        (fun z => (r n i)^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (r n i) z)) 0 (fun _ => t.toNNReal) b -
        stoppedAnnularClock (fun z => (ε n)^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε n) z)) 0 (fun _ => t.toNNReal) b|) :=
      ENNReal.continuous_ofReal.comp (((hcont (r n i) (hr n i)).sub (hcont (ε n) (hε n))).abs)
    rw [← hre, nonpositive_unit_iSup_eq_rational _ hcF]
    apply iSup_congr
    intro q
    dsimp [M]
    rw [hG n i q b, ← hsub (ε n) (r n i) (hε n) (hr n i) (τ q) b]
  let S : Set (Ω × ContinuousPath ℂ) := {p | (∑' n : ℕ,
    ∑ i ∈ Finset.range (gridCount c (n+1) + 1), M n i p) < ⊤}
  have hSm : MeasurableSet S := by
    apply measurableSet_lt _ measurable_const
    apply Measurable.tsum
    intro n
    exact Finset.measurable_fun_sum _ (fun i _ => hMm n i)
  have hS (y : ℂ) : ∀ᵐ p ∂(P.prod (planarBrownianMotion y)), p ∈ S := by
    filter_upwards [hbase y, (Measure.quasiMeasurePreserving_fst
      (μ := P) (ν := planarBrownianMotion y)).ae hMfield] with p hp hω
    change (∑' n : ℕ, ∑ i ∈ Finset.range (gridCount c (n+1) + 1), M n i p) < ⊤
    convert hp using 2
    ext n
    apply Finset.sum_congr rfl
    intro i hi
    exact hω p.2 n i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  refine ⟨c, hc, ?_⟩
  intro x
  apply ae_all_iff.mpr
  intro j
  have hshift := ae_prod_planarBrownianMotion_shift_of_forall_ae P x j S hSm hS
  filter_upwards [hshift, (Measure.quasiMeasurePreserving_fst
    (μ := P) (ν := planarBrownianMotion x)).ae hMfield] with p hp hω
  change (∑' n : ℕ, ∑ i ∈ Finset.range (gridCount c (n+1) + 1),
    ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |stoppedAnnularClock _ 0 (fun _ => ((t : ℝ).toNNReal))
      (ContinuousPath.shift j p.2) - stoppedAnnularClock _ 0 (fun _ => ((t : ℝ).toNNReal))
      (ContinuousPath.shift j p.2)|) < ⊤
  change (∑' n : ℕ, ∑ i ∈ Finset.range (gridCount c (n+1) + 1), M n i
    (p.1, ContinuousPath.shift j p.2)) < ⊤ at hp
  convert hp using 2
  ext n
  apply Finset.sum_congr rfl
  intro i hi
  exact (hω (ContinuousPath.shift j p.2) n i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).symm


private theorem nonpositive_ofReal_abs_le_sum_unit_bounds (D : ℝ → ℝ) (hD : D 0 = 0) (B : ℕ → ℝ≥0∞)
    (hB : ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1 →
      ENNReal.ofReal |D ((n : ℝ) + t) - D n| ≤ B n) :
    ∀ (N : ℕ) (t : ℝ), 0 ≤ t → t ≤ N →
      ENNReal.ofReal |D t| ≤ ∑ n ∈ Finset.range N, B n := by
  intro N
  induction N with
  | zero =>
    intro t ht0 htN
    have htN' : t ≤ (0 : ℝ) := by simpa only [Nat.cast_zero] using htN
    have ht : t = 0 := le_antisymm htN' ht0
    simp only [ht, hD, abs_zero, ENNReal.ofReal_zero, Finset.range_zero, Finset.sum_empty, le_refl]
  | succ N ih =>
    intro t ht0 htN
    rw [Finset.sum_range_succ]
    by_cases htn : t ≤ N
    · exact (ih t ht0 htn).trans (le_add_right le_rfl)
    · have htN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have htn' : (N : ℝ) < t := lt_of_not_ge htn
      have hsub0 : 0 ≤ t - N := by linarith
      have hsub1 : t - N ≤ 1 := by push_cast at htN; linarith
      have hprev := ih N htN0 le_rfl
      have hlast := hB N (t - N) hsub0 hsub1
      have hsum : (N : ℝ) + (t - N) = t := by ring
      rw [hsum] at hlast
      calc
        ENNReal.ofReal |D t| = ENNReal.ofReal |D N + (D t - D N)| := by congr 1; ring
        _ ≤ ENNReal.ofReal (|D N| + |D t - D N|) := ENNReal.ofReal_le_ofReal (abs_add_le _ _)
        _ = ENNReal.ofReal |D N| + ENNReal.ofReal |D t - D N| := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
        _ ≤ _ := add_le_add hprev hlast

/-- Radius-grid errors are summable uniformly on every finite time interval. -/
theorem exists_ae_tsum_nonpositive_halfDisc_radius_grid_clock_all_horizons_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ ^ 2 < 2) (α : ℝ) (hα : α ≤ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℂ,
      ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)), ∀ N : ℕ,
      let F : ℝ → ℝ → ℝ := fun v t => ∫ s in (0 : ℝ)..t,
        {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          v^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z))
            (p.2 s.toNNReal)
      (∑' n : ℕ, ∑ i ∈ Finset.range (gridCount c (n+1) + 1),
        ⨆ t : Icc (0 : ℝ) N, ENNReal.ofReal
          |F (gridScale (gridCount c) (n+1) i) t -
            F (LatticeProb.LQG.dyadicScale (n+1)) t|) < ⊤ := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨c, hc, hgrid⟩ :=
    exists_ae_tsum_nonpositive_halfDisc_shifted_radius_grid_clock_lt_top hh hγ hγ2 α hα
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  refine ⟨c, hc, ?_⟩
  intro x
  filter_upwards [hgrid x, (Measure.quasiMeasurePreserving_fst
    (μ := P) (ν := planarBrownianMotion x)).ae hHae] with q hq hω
  intro N
  let A : ℝ → ℝ → ℝ := fun v t => ∫ s in (0 : ℝ)..t,
    {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
      v^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) v z))
        (q.2 s.toNNReal)
  let F : ℝ → ℕ → ℝ → ℝ := fun v j t =>
    stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) v z)) 0
        (fun _ => t.toNNReal) (ContinuousPath.shift j q.2)
  let B : ℕ → ℕ → ℕ → ℝ≥0∞ := fun j n i =>
    ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal
      |F (gridScale (gridCount c) (n+1) i) j t -
        F (LatticeProb.LQG.dyadicScale (n+1)) j t|
  have hdensity (v : ℝ) (hv : 0 < v) : Continuous (fun z => v^(γ^2/2) * Real.exp
      (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) v z)) := by
    have hcv : Continuous (hcirc q.1 v) := by
      rw [← funext (hω v)]
      exact hHc q.1 v hv
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (continuous_fieldCircleAverage_of_continuous (hcirc q.1) α hv hcv)))
  have hpoint (n i : ℕ) (hi : i ∈ Finset.range (gridCount c (n+1)+1)) :
      (⨆ t : Icc (0 : ℝ) N, ENNReal.ofReal
        |A (gridScale (gridCount c) (n+1) i) t - A (LatticeProb.LQG.dyadicScale (n+1)) t|) ≤
        ∑ j ∈ Finset.range N, B j n i := by
    let r : ℝ := gridScale (gridCount c) (n+1) i
    let ε : ℝ := LatticeProb.LQG.dyadicScale (n+1)
    have he : 0 < ε := by dsimp [ε, LatticeProb.LQG.dyadicScale]; positivity
    have hi' : i ≤ gridCount c (n+1) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hr : 0 < r := (half_pos he).trans_le (gridScale_mem_Icc (gridCount c) hi').1
    let D : ℝ → ℝ := fun t => A r t - A ε t
    have hD : D 0 = 0 := by simp [D, A]
    have hblock (j : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
        ENNReal.ofReal |D ((j : ℝ) + t) - D j| ≤ B j n i := by
      have h1 := stoppedAnnularClock_shift_eq_time_increment _ (hdensity r hr) 0 q.2 j ⟨t, ht0, ht1⟩
      have h2 := stoppedAnnularClock_shift_eq_time_increment _ (hdensity ε he) 0 q.2 j ⟨t, ht0, ht1⟩
      change F r j t = A r ((j : ℝ) + t) - A r j at h1
      change F ε j t = A ε ((j : ℝ) + t) - A ε j at h2
      have heq : D ((j : ℝ) + t) - D j = F r j t - F ε j t := by
        dsimp [D]
        rw [h1, h2]
        ring
      rw [heq]
      exact le_iSup (fun t : Icc (0 : ℝ) 1 => ENNReal.ofReal |F r j t - F ε j t|) ⟨t, ht0, ht1⟩
    apply iSup_le
    intro t
    exact nonpositive_ofReal_abs_le_sum_unit_bounds D hD (fun j => B j n i) hblock N t t.2.1 t.2.2
  calc
    _ ≤ ∑' n : ℕ, ∑ i ∈ Finset.range (gridCount c (n+1)+1), ∑ j ∈ Finset.range N, B j n i := by
      apply ENNReal.tsum_le_tsum
      intro n
      exact Finset.sum_le_sum (fun i hi => hpoint n i hi)
    _ = ∑' n : ℕ, ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (gridCount c (n+1)+1), B j n i := by
      apply tsum_congr
      intro n
      exact Finset.sum_comm
    _ = ∑ j ∈ Finset.range N, ∑' n : ℕ, ∑ i ∈ Finset.range (gridCount c (n+1)+1), B j n i :=
      Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
    _ < ⊤ := ENNReal.sum_lt_top.mpr (fun j _ => hq j)

end HarmonicBalls
