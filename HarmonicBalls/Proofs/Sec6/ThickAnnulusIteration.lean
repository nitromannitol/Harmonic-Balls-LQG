import HarmonicBalls.Proofs.Sec6.GeometricAnnulusIteration
import HarmonicBalls.Proofs.Sec6.ExponentialScaleDecay

/-! # Iteration for events in thick annuli

The annulus iteration uses Leonardo Bonanno's proof of the Gwynne–Miller
lemma in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- Local events on `A_{2r,6r}` have a polynomial lower-tail bound for
seven-adic radii in a three-quarter window. This permits events concerning
all centres in a neighborhood of the reference centre. -/
theorem thick_annulus_subrange_probability (α β : ℝ) (hα : 0 < α)
    (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ p ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc →
    ∀ (s : ℝ), 0 < s → ∀ (good : Ω → ℝ → Prop),
      (∀ n : ℕ, IsFieldMeasurableModConst P 0 hC
        (annulus 0 (2 * (s * ((7 : ℝ)⁻¹ ^ n))) (6 * (s * ((7 : ℝ)⁻¹ ^ n))))
        {ω | good ω (s * ((7 : ℝ)⁻¹ ^ n))}) →
      (∀ n : ℕ, ENNReal.ofReal p ≤ P {ω | good ω (s * ((7 : ℝ)⁻¹ ^ n))}) →
    ∀ ε : ℝ, 0 < ε → 16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      P {ω | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧ good ω (s * r)}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤
      ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) := by
  classical
  obtain ⟨p, hp, C, hCpos, hiter⟩ :=
    annulusIterationStmt_proved (2 / 7) (6 / 7) (by norm_num) (by norm_num)
      (by norm_num) α hα β hβ
  refine ⟨p, hp, C, hCpos, ?_⟩
  intro Ω _ P hC hcirc hgff s hs good hlocal hprob ε hε ht
  obtain ⟨n₀, K, hK, hrange⟩ :=
    exists_inverse_geometric_scales_in_three_quarter_window (b := (7 : ℝ))
      (by norm_num) hε 1 (by omega) (by simpa using ht)
  have hK' : Real.logb 7 (ε ^ (-1 : ℝ)) / 16 ≤ (K : ℝ) := by simpa using hK
  let r : ℕ → ℝ := fun k => 7 * s * (7 : ℝ)⁻¹ ^ (n₀ + k)
  let E : ℕ → Set Ω := fun k => {ω | good ω (s * (7 : ℝ)⁻¹ ^ (n₀ + k))}
  have hr : ∀ k, 0 < r k := fun k => by dsimp [r]; positivity
  have hratio : ∀ k, r (k + 1) ≤ (2 / 7 : ℝ) * r k := by
    intro k
    dsimp [r]
    rw [show n₀ + (k + 1) = (n₀ + k) + 1 by omega, pow_succ]
    have hpw : 0 ≤ (7 : ℝ)⁻¹ ^ (n₀ + k) := by positivity
    nlinarith
  have hloc : ∀ k, IsFieldMeasurableModConst P 0 hC
      (annulus 0 ((2 / 7 : ℝ) * r k) ((6 / 7 : ℝ) * r k)) (E k) := by
    intro k
    convert hlocal (n₀ + k) using 1
    all_goals dsimp [r, E]
    all_goals congr 1
    all_goals ring
  have hbound := hiter 0 Ω P hC hcirc hgff r hr hratio E hloc
    (fun k => hprob (n₀ + k)) K
  have hcount : P {ω | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧ good ω (s * r)}.ncard : ℝ)
        < β * K} ≤ ENNReal.ofReal (C * Real.exp (-α * K)) := by
    apply (measure_mono ?_).trans hbound
    intro ω hω
    have h := geometric_scale_count_le (by norm_num : (0 : ℝ) < 7⁻¹)
      (by norm_num : (7 : ℝ)⁻¹ < 1) hε
      (fun t => good ω (s * t)) n₀ 1 K (by omega) hrange
    simp only [one_mul] at h
    change (((Finset.range K).filter fun k => good ω
      (s * (7 : ℝ)⁻¹ ^ (n₀ + k))).card : ℝ) < β * K
    exact lt_of_le_of_lt (by exact_mod_cast h) hω
  have hthreshold : (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤ β * K := by
    nlinarith [mul_le_mul_of_nonneg_left hK' hβ.1.le]
  calc
    _ ≤ _ := measure_mono (fun _ h => lt_of_lt_of_le h hthreshold)
    _ ≤ _ := hcount
    _ ≤ _ := ofReal_exp_bound_le_rpow (by norm_num : (1 : ℝ) < 7) hε hα.le
      (by norm_num : (0 : ℝ) < 16) hCpos.le hK' 

/-- The annuli of centres within one hundredth of the radius are contained
in a single thick annulus. -/
theorem nearby_goodAnnulus_subset_thick_annulus {z w : ℂ} {r : ℝ}
    (hr : 0 < r) (hw : w ∈ ball z (r / 100)) :
    annulus w (3 * r) (5 * r) ⊆ annulus z (2 * r) (6 * r) := by
  intro x hx
  have hdist : dist w z < r / 100 := mem_ball.mp hw
  have hx' : dist x w < 5 * r ∧ 3 * r < dist x w := by
    simpa only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le] using hx
  have hu := dist_triangle x w z
  have hl := dist_triangle x z w
  have heq : dist z w = dist w z := dist_comm _ _
  change dist x z < 6 * r ∧ ¬ dist x z ≤ 2 * r
  constructor <;> linarith

/-- At level at least one, the phase-approximation displacement is less
than one hundredth of every radius in the tested window. -/
theorem phase_displacement_lt_radius_div_hundred {s r : ℝ} {n : ℕ} {d : ℂ}
    (hs : 0 < s) (hn : 1 ≤ n) (hr : dyadicScale n * s ≤ r)
    (hd : dist 0 d < 2 * (dyadicScale (2 * n) * s / 100)) :
    dist 0 d < r / 100 := by
  have hε : 0 < dyadicScale n := dyadicScale_pos n
  have hεhalf : dyadicScale n ≤ (1 / 2 : ℝ) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hk : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    simp only [dyadicScale, pow_add, pow_one]
    nlinarith
  have hdouble : dyadicScale (2 * n) = dyadicScale n * dyadicScale n := by
    simp only [show 2 * n = n + n by omega, dyadicScale, pow_add]
  rw [hdouble] at hd
  have hbound : 2 * (dyadicScale n * dyadicScale n * s / 100) ≤ r / 100 := by
    nlinarith [mul_nonneg hε.le hs.le,
      mul_nonneg (sub_nonneg.mpr hεhalf) (mul_nonneg hε.le hs.le)]
  exact hd.trans_le hbound

end HarmonicBalls.Section6
