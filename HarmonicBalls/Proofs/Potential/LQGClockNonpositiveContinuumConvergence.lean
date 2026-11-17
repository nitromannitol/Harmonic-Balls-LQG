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

end HarmonicBalls
