import HarmonicBalls.Proofs.Potential.LQGClockAnnularGridOccupationIncrement
import LatticeProb.LQG.GMCRatioLimit
import LatticeProb.LQG.LQGBallMassGrid2

/-! # Radial regularity of inserted circle averages

The insertion correction has a uniform radial modulus down to the origin.
-/

open MeasureTheory Filter LatticeProb.LQG MarkovProcess
open LatticeProb.LQG.GMCScaleGrid LatticeProb.LQG.GMCRatioLimit
open scoped Topology NNReal

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

end HarmonicBalls
