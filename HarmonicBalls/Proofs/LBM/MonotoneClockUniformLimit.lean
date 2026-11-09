import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform convergence of monotone clocks on compact time intervals

Deterministic grid step behind the locally uniform convergence of the dyadic circle-average clocks
in the Bou-Rabee and Gwynne argument (arXiv:2208.11795, Section 6). The source estimate is the
rational-partition inequality of the written proof (`steps4-final.tex`, lines 2003-2022).

Let `C n : ℝ → ℝ` be monotone on `[0, ∞)` for every `n`, and let `a : ℝ → ℝ` be continuous and
monotone on `[0, ∞)`. If `C n q → a q` for every nonnegative rational `q`, then for every `T ≥ 0`
and `ε > 0`, eventually in `n`, `|C n t - a t| < ε` for all `t ∈ [0, T]`.

Only the monotonicity of the clocks in time and the rational convergence enter. No uniform
convergence, clock-continuity, inverse-continuity or stochastic hypothesis is assumed.
-/

open Filter Topology Set

namespace HarmonicBalls.MonotoneClockUniformLimit

/-- **Cell estimate** (finite rational-partition bound of the source). If `cx ≤ ct ≤ cy` and
`ax ≤ am ≤ ay`, then `|ct - am| ≤ max |cx - ax| |cy - ay| + (ay - ax)`.

Here `cx, ct, cy` are clock values at the two grid endpoints and `t`, and `ax, am, ay` are the
limit values; the maximum over a finite grid is reduced to the two endpoints of the cell that
contains `t`. -/
theorem abs_sub_le_max_add_oscillation {cx ct cy ax am ay : ℝ}
    (h₁ : cx ≤ ct) (h₂ : ct ≤ cy) (h₃ : ax ≤ am) (h₄ : am ≤ ay) :
    |ct - am| ≤ max |cx - ax| |cy - ay| + (ay - ax) := by
  have hL : -|cx - ax| ≤ cx - ax := neg_abs_le _
  have hU : cy - ay ≤ |cy - ay| := le_abs_self _
  have hM1 : |cx - ax| ≤ max |cx - ax| |cy - ay| := le_max_left _ _
  have hM2 : |cy - ay| ≤ max |cx - ax| |cy - ay| := le_max_right _ _
  rw [abs_le]
  constructor <;> linarith

/-- **Deterministic grid step.** Let `C n` be monotone on `[0, ∞)` for every `n`, and let `a` be
continuous and monotone on `[0, ∞)`. If `C n q → a q` for every nonnegative rational `q`, then for
every `T ≥ 0` and `ε > 0`, eventually in `n`, `|C n t - a t| < ε` for all `t ∈ [0, T]`.
Endpoints `t = 0` and `t = T` are included; `T = 0` is covered by the same grid argument. -/
theorem monotone_clock_uniform_limit
    (C : ℕ → ℝ → ℝ) (a : ℝ → ℝ)
    (hC : ∀ n, MonotoneOn (C n) (Ici 0))
    (ha : ContinuousOn a (Ici 0)) (ha_mono : MonotoneOn a (Ici 0))
    (hlim : ∀ q : ℚ, 0 ≤ q → Tendsto (fun n => C n (q : ℝ)) atTop (𝓝 (a (q : ℝ)))) :
    ∀ T : ℝ, 0 ≤ T → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T, |C n t - a t| < ε := by
  intro T _hT ε hε
  -- Heine-Cantor: `a` is uniformly continuous on the compact window `[0, T + 1]`.
  have hunif : UniformContinuousOn a (Icc (0 : ℝ) (T + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (ha.mono fun x hx => Set.mem_Ici.mpr hx.1)
  obtain ⟨δ, hδ, hδa⟩ :=
    Metric.uniformContinuousOn_iff.mp hunif (ε / 3) (div_pos hε (by norm_num))
  -- Grid mesh `1 / s < δ`, where `s = m + 1`.
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  set s : ℝ := (m : ℝ) + 1 with hs_def
  have hs1 : 1 ≤ s := by
    rw [hs_def]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hs_pos : 0 < s := by linarith
  have hstep_lt : 1 / s < δ := hm
  have hstep_le : 1 / s ≤ 1 := by
    rw [div_le_iff₀ hs_pos]; linarith
  have hstep_pos : 0 < 1 / s := one_div_pos.mpr hs_pos
  -- Rational grid points `q_j = j / (m + 1)`, all nonnegative.
  set qr : ℕ → ℚ := fun j => (j : ℚ) / ((m : ℚ) + 1) with hqr_def
  have hqr_nonneg : ∀ j : ℕ, 0 ≤ qr j := fun j => by
    simp only [hqr_def]; positivity
  have hqr_cast : ∀ j : ℕ, ((qr j : ℚ) : ℝ) = (j : ℝ) / s := by
    intro j; simp [hqr_def, hs_def]
  -- Only finitely many grid points carry the rational convergence hypothesis.
  obtain ⟨M0, hM0⟩ : ∃ M0 : ℕ, (T + 1) * s ≤ M0 := ⟨⌈(T + 1) * s⌉₊, Nat.le_ceil _⟩
  have hgrid : ∀ j ∈ Finset.range (M0 + 2),
      ∀ᶠ n in atTop, |C n ((qr j : ℚ) : ℝ) - a ((qr j : ℚ) : ℝ)| < ε / 3 := by
    intro j _
    have hconv := Metric.tendsto_nhds.mp (hlim (qr j) (hqr_nonneg j)) (ε / 3)
      (div_pos hε (by norm_num))
    filter_upwards [hconv] with n hn
    rwa [Real.dist_eq] at hn
  filter_upwards [(Filter.eventually_all_finset (Finset.range (M0 + 2))).mpr hgrid] with n hn
  intro t ht
  obtain ⟨ht0, htT⟩ := ht
  -- The grid cell `[i / s, (i + 1) / s]` containing `t`, where `i = ⌊t s⌋₊`.
  obtain ⟨i, hi_def⟩ : ∃ i : ℕ, i = ⌊t * s⌋₊ := ⟨_, rfl⟩
  have hts_nonneg : 0 ≤ t * s := mul_nonneg ht0 hs_pos.le
  have hi_le : (i : ℝ) ≤ t * s := by
    rw [hi_def]; exact Nat.floor_le hts_nonneg
  have hts_lt : t * s < (i : ℝ) + 1 := by
    rw [hi_def]; exact Nat.lt_floor_add_one (t * s)
  have hx_le_t : (i : ℝ) / s ≤ t := by
    rw [div_le_iff₀ hs_pos]; linarith
  have ht_lt_y : t < ((i : ℝ) + 1) / s := by
    rw [lt_div_iff₀ hs_pos]; linarith
  have hx_nonneg : 0 ≤ (i : ℝ) / s := div_nonneg (Nat.cast_nonneg i) hs_pos.le
  have hy_nonneg : 0 ≤ ((i : ℝ) + 1) / s := div_nonneg (by positivity) hs_pos.le
  have hsub : ((i : ℝ) + 1) / s - (i : ℝ) / s = 1 / s := by ring
  have hx_le : (i : ℝ) / s ≤ T + 1 := by linarith
  have hy_le : ((i : ℝ) + 1) / s ≤ T + 1 := by linarith
  -- The indices `i` and `i + 1` lie in the finite range.
  have hiM : i ≤ M0 := by
    have h1 : (i : ℝ) ≤ (T + 1) * s :=
      le_trans hi_le (mul_le_mul_of_nonneg_right (by linarith) hs_pos.le)
    exact_mod_cast le_trans h1 hM0
  have hi_mem : i ∈ Finset.range (M0 + 2) := Finset.mem_range.mpr (by omega)
  have hi1_mem : i + 1 ∈ Finset.range (M0 + 2) := Finset.mem_range.mpr (by omega)
  -- Grid estimates at the two endpoints of the cell.
  have hxi : |C n ((i : ℝ) / s) - a ((i : ℝ) / s)| < ε / 3 := by
    have h : |C n ((qr i : ℚ) : ℝ) - a ((qr i : ℚ) : ℝ)| < ε / 3 := hn i hi_mem
    rw [hqr_cast] at h
    exact h
  have hyi : |C n (((i : ℝ) + 1) / s) - a (((i : ℝ) + 1) / s)| < ε / 3 := by
    have h : |C n ((qr (i + 1) : ℚ) : ℝ) - a ((qr (i + 1) : ℚ) : ℝ)| < ε / 3 :=
      hn (i + 1) hi1_mem
    rw [hqr_cast] at h
    push_cast at h
    exact h
  -- Uniform continuity of `a` across the cell, since the cell length `1 / s` is below `δ`.
  have hay : |a (((i : ℝ) + 1) / s) - a ((i : ℝ) / s)| < ε / 3 := by
    have hd : dist (((i : ℝ) + 1) / s) ((i : ℝ) / s) < δ := by
      rw [Real.dist_eq, hsub, abs_of_pos hstep_pos]; exact hstep_lt
    have h := hδa (((i : ℝ) + 1) / s) ⟨hy_nonneg, hy_le⟩ ((i : ℝ) / s) ⟨hx_nonneg, hx_le⟩ hd
    rwa [Real.dist_eq] at h
  have hay' : a (((i : ℝ) + 1) / s) - a ((i : ℝ) / s) < ε / 3 := (abs_lt.mp hay).2
  -- Monotone sandwich of the clock and of the limit around `t`.
  have hCxt : C n ((i : ℝ) / s) ≤ C n t :=
    hC n (Set.mem_Ici.mpr hx_nonneg) (Set.mem_Ici.mpr ht0) hx_le_t
  have hCty : C n t ≤ C n (((i : ℝ) + 1) / s) :=
    hC n (Set.mem_Ici.mpr ht0) (Set.mem_Ici.mpr hy_nonneg) ht_lt_y.le
  have hAxt : a ((i : ℝ) / s) ≤ a t :=
    ha_mono (Set.mem_Ici.mpr hx_nonneg) (Set.mem_Ici.mpr ht0) hx_le_t
  have hAty : a t ≤ a (((i : ℝ) + 1) / s) :=
    ha_mono (Set.mem_Ici.mpr ht0) (Set.mem_Ici.mpr hy_nonneg) ht_lt_y.le
  have key := abs_sub_le_max_add_oscillation hCxt hCty hAxt hAty
  have hmax := max_lt hxi hyi
  linarith

end HarmonicBalls.MonotoneClockUniformLimit
