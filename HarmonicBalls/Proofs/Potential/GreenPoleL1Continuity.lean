import HarmonicBalls.Proofs.Potential.GreenLocalVolumeBound
import HarmonicBalls.Proofs.Potential.FiniteDiscGreenReciprocity

/-!
# L¹ continuity of the zero-extended Green row in the pole

For a bounded open planar set `U` and a pole `x ∈ U`, the zero-extended Green row `y ↦ G_U(x, y)`
(value `0` off `U`, as in `greenFunction`) is integrable on `ℂ`, and it depends continuously on the
pole in `L¹(ℂ)`: `∫ |G_U(xₙ, y) - G_U(x, y)| dy → 0` whenever `xₙ → x`.

Proof outline. Remove the disc `B(x, r)`.
* On `B(x, r)` both rows are nonnegative and their integrals are bounded uniformly in the pole by the
  local volume estimate `C r² (1 + |log r|)` of `GreenLocalVolumeBound`, small for small `r`.
* Off `B(x, r)`, for poles in `B(x, r/2)`, both rows are bounded by `(2π)⁻¹ log⁺(4R/r)` when
  `U ⊆ B(0, R)`, and they converge pointwise by continuity of the pole
  (`continuousAt_greenFunction_pole`), so dominated convergence applies on `B(x, r)ᶜ`.

Only `IsOpen U`, `IsBounded U` and `x ∈ U` are assumed. No boundary regularity and no literature
input is used. The local volume estimate and the potential-theoretic infrastructure use work of
Leonardo Bonanno; the Green function is the one of Armitage–Gardiner, as in `Defs/Green.lean`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Real Metric

/-- Pointwise logarithmic bound for the Green row with pole `x`: if `U ⊆ B(0, R)` with `R > 0`, then
`G_U(x, z) ≤ (2π)⁻¹ log⁺(2R / ‖z - x‖)` for every pole `x` and point `z`. For `x ∈ U` this is domain
monotonicity with the disc `B(x, 2R) ⊇ U` and the explicit disc formula; for `x ∉ U` the row vanishes. -/
theorem greenFunction_le_posLog_div_norm {U : Set ℂ} {R : ℝ} (hR : 0 < R)
    (hsub : U ⊆ ball (0 : ℂ) R) (x z : ℂ) :
    greenFunction U x z ≤ (2 * Real.pi)⁻¹ * log⁺ (2 * R / ‖z - x‖) := by
  by_cases hx : x ∈ U
  · have hs : U ⊆ ball x (2 * R) := by
      intro y hy
      have hyR := mem_ball_zero_iff.mp (hsub hy)
      have hxR := mem_ball_zero_iff.mp (hsub hx)
      rw [mem_ball, dist_eq_norm]
      have hh := norm_sub_le y x
      linarith
    calc greenFunction U x z ≤ greenFunction (ball x (2 * R)) x z :=
          Section6.greenFunction_le_of_subset hs isBounded_ball x z
      _ = (2 * Real.pi)⁻¹ * log⁺ (2 * R / ‖z - x‖) :=
          greenFunction_ball_center_eq_posLog (by positivity) x z
  · rw [greenFunction_of_notMem_left hx]
    exact mul_nonneg (by positivity) posLog_nonneg

/-- Monotonicity of the logarithmic kernel when the distance `d` is at least `r / 2`:
`log⁺(2R / d) ≤ log⁺(4R / r)`. -/
theorem posLog_two_mul_div_le {R r d : ℝ} (hR : 0 < R) (hr : 0 < r) (hd : r / 2 ≤ d) :
    log⁺ (2 * R / d) ≤ log⁺ (4 * R / r) := by
  have hdpos : 0 < d := lt_of_lt_of_le (half_pos hr) hd
  have hnn : 0 ≤ 2 * R / d := div_nonneg (by positivity) hdpos.le
  refine Real.posLog_le_posLog ?_ ?_
  · linarith
  · rw [div_le_div_iff₀ hdpos hr]
    nlinarith [mul_le_mul_of_nonneg_left hd hR.le]

/-- Integrability of the zero-extended Green row: for a bounded open `U` and every pole `z`, the
function `y ↦ G_U(z, y)` is integrable on `ℂ`. It vanishes off `U ⊆ B(0, R)`, and the local volume
estimate gives integrability on `B(0, R)`. -/
theorem integrable_greenFunction_pole {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (z : ℂ) : Integrable (greenFunction U z) := by
  obtain ⟨R, hR, hsub⟩ := hUb.subset_ball_lt 0 (0 : ℂ)
  obtain ⟨_C, -, hloc⟩ := exists_greenFunction_local_volume_bound hU hUb
  have hint : IntegrableOn (greenFunction U z) (ball (0 : ℂ) R) := (hloc R hR z 0).1
  have hsupp : Function.support (greenFunction U z) ⊆ ball (0 : ℂ) R := by
    intro y hy
    refine hsub ?_
    by_contra hyU
    exact (Function.mem_support.1 hy) (greenFunction_of_notMem_right hyU z)
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hint

/-- The absolute difference of two zero-extended Green rows is integrable on `ℂ`. -/
theorem integrable_abs_greenFunction_sub_pole {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (z x : ℂ) :
    Integrable (fun y => |greenFunction U z y - greenFunction U x y|) :=
  ((integrable_greenFunction_pole hU hUb z).sub (integrable_greenFunction_pole hU hUb x)).abs

/-- On any disc `B(c, r)`, the integral of `|G_U(p, ·) - G_U(q, ·)|` is at most twice the uniform local
volume estimate, for any two poles `p, q`. Nonnegativity of the Green row removes the absolute values
from the integrand bound. -/
theorem integral_ball_abs_greenFunction_sub_le {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {C : ℝ}
    (hloc : ∀ (r : ℝ), 0 < r → ∀ x c : ℂ, IntegrableOn (greenFunction U x) (ball c r) ∧
      (∫ z in ball c r, greenFunction U x z) ≤ C * r ^ 2 * (1 + |Real.log r|))
    {r : ℝ} (hr : 0 < r) (p q c : ℂ) :
    (∫ y in ball c r, |greenFunction U p y - greenFunction U q y|) ≤
      2 * (C * r ^ 2 * (1 + |Real.log r|)) := by
  have hp : IntegrableOn (greenFunction U p) (ball c r) := (hloc r hr p c).1
  have hq : IntegrableOn (greenFunction U q) (ball c r) := (hloc r hr q c).1
  have hab : IntegrableOn (fun y => |greenFunction U p y - greenFunction U q y|) (ball c r) :=
    (integrable_abs_greenFunction_sub_pole hU hUb p q).integrableOn
  calc (∫ y in ball c r, |greenFunction U p y - greenFunction U q y|)
      ≤ ∫ y in ball c r, (greenFunction U p y + greenFunction U q y) := by
        refine setIntegral_mono_on hab (Integrable.add hp hq) measurableSet_ball ?_
        intro y _
        have ha := greenFunction_nonneg hUb p y
        have hb := greenFunction_nonneg hUb q y
        rw [abs_sub_le_iff]
        constructor <;> linarith
    _ = (∫ y in ball c r, greenFunction U p y) + ∫ y in ball c r, greenFunction U q y :=
        integral_add hp hq
    _ ≤ C * r ^ 2 * (1 + |Real.log r|) + C * r ^ 2 * (1 + |Real.log r|) :=
        add_le_add (hloc r hr p c).2 (hloc r hr q c).2
    _ = 2 * (C * r ^ 2 * (1 + |Real.log r|)) := by ring

/-- Off a fixed disc `B(x, r)`, the integrals of `|G_U(xs i, ·) - G_U(x, ·)|` tend to zero along `l`, by
dominated convergence. The dominator is `(2π)⁻¹ log⁺(4R/r)` on `B(0, R) ⊇ U`, valid for poles in
`B(x, r/2)`; pointwise convergence holds by continuity of the pole (`continuousAt_greenFunction_pole`)
at `x ∈ U`, and both rows vanish off `U`. -/
theorem tendsto_integral_outside_ball_abs_greenFunction_sub {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {x : ℂ} (hx : x ∈ U) {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {xs : ι → ℂ} (hxs : Tendsto xs l (𝓝 x)) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun i => ∫ y, Set.indicator (ball x r)ᶜ
      (fun y' => |greenFunction U (xs i) y' - greenFunction U x y'|) y) l (𝓝 0) := by
  obtain ⟨R, hR, hsub⟩ := hUb.subset_ball_lt 0 (0 : ℂ)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = (2 * Real.pi)⁻¹ * log⁺ (4 * R / r) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (by positivity) posLog_nonneg
  have hpt : ∀ p y : ℂ, r / 2 ≤ ‖y - p‖ → 0 ≤ greenFunction U p y ∧ greenFunction U p y ≤ M := by
    intro p y hd
    refine ⟨greenFunction_nonneg hUb p y, ?_⟩
    rw [hMdef]
    exact (greenFunction_le_posLog_div_norm hR hsub p y).trans
      (mul_le_mul_of_nonneg_left (posLog_two_mul_div_le hR hr hd) (by positivity))
  have hbd : ∀ i, xs i ∈ ball x (r / 2) → ∀ y : ℂ,
      ‖Set.indicator (ball x r)ᶜ (fun y' => |greenFunction U (xs i) y' - greenFunction U x y'|) y‖
        ≤ Set.indicator (ball (0 : ℂ) R) (fun _ => M) y := by
    intro i hi y
    have hxi : ‖xs i - x‖ < r / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hi
    by_cases hy : y ∈ ball x r
    · have hy0 : y ∉ (ball x r)ᶜ := fun h => h hy
      rw [Set.indicator_of_notMem hy0, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hM0) y
    · have hy' : y ∈ (ball x r)ᶜ := hy
      have hyr : r ≤ ‖y - x‖ := by simpa [Metric.mem_ball, dist_eq_norm] using hy
      rw [Set.indicator_of_mem hy', Real.norm_eq_abs, abs_abs]
      by_cases hyU : y ∈ U
      · have htri := norm_add_le (y - xs i) (xs i - x)
        rw [sub_add_sub_cancel] at htri
        have hd1 : r / 2 ≤ ‖y - xs i‖ := by linarith
        have hd2 : r / 2 ≤ ‖y - x‖ := by linarith
        obtain ⟨ha0, ha1⟩ := hpt (xs i) y hd1
        obtain ⟨hb0, hb1⟩ := hpt x y hd2
        simp only [Set.indicator_of_mem (hsub hyU)]
        rw [abs_sub_le_iff]
        constructor <;> linarith
      · simp only [greenFunction_of_notMem_right hyU, sub_self, abs_zero]
        exact Set.indicator_nonneg (fun _ _ => hM0) y
  have hlimpt : ∀ y : ℂ, Tendsto (fun i => Set.indicator (ball x r)ᶜ
      (fun y' => |greenFunction U (xs i) y' - greenFunction U x y'|) y) l (𝓝 0) := by
    intro y
    by_cases hy : y ∈ ball x r
    · have hy0 : y ∉ (ball x r)ᶜ := fun h => h hy
      simpa only [Set.indicator_of_notMem hy0] using
        (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ)) l (𝓝 0))
    · have hy' : y ∈ (ball x r)ᶜ := hy
      simp only [Set.indicator_of_mem hy']
      by_cases hyU : y ∈ U
      · have hne : x ≠ y := by
          rintro rfl
          exact hy (mem_ball_self hr)
        have hc : ContinuousAt (fun p => greenFunction U p y) x :=
          continuousAt_greenFunction_pole hU hUb hx hyU hne
        have h1 : Tendsto (fun i => greenFunction U (xs i) y) l (𝓝 (greenFunction U x y)) :=
          hc.tendsto.comp hxs
        have h2 := (continuous_abs.tendsto _).comp (h1.sub_const (greenFunction U x y))
        simpa [Function.comp_def] using h2
      · simpa only [greenFunction_of_notMem_right hyU, sub_self, abs_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ)) l (𝓝 0))
  have hdomEv : ∀ᶠ i in l, xs i ∈ ball x (r / 2) := hxs (Metric.ball_mem_nhds x (half_pos hr))
  have hmeas : ∀ᶠ i in l, AEStronglyMeasurable (Set.indicator (ball x r)ᶜ
      (fun y' => |greenFunction U (xs i) y' - greenFunction U x y'|)) volume :=
    Eventually.of_forall fun i =>
      ((integrable_abs_greenFunction_sub_pole hU hUb (xs i) x).aestronglyMeasurable).indicator
        measurableSet_ball.compl
  have hbound_int : Integrable (Set.indicator (ball (0 : ℂ) R) (fun _ => M)) :=
    (integrableOn_const (measure_ball_lt_top : volume (ball (0 : ℂ) R) < ⊤).ne).integrable_indicator
      measurableSet_ball
  have h := tendsto_integral_filter_of_dominated_convergence
    (Set.indicator (ball (0 : ℂ) R) (fun _ => M)) hmeas
    (by
      filter_upwards [hdomEv] with i hi
      exact Eventually.of_forall (fun y => hbd i hi y))
    hbound_int (Eventually.of_forall hlimpt)
  simpa using h

/-- **L¹ continuity of the zero-extended Green row in the pole.** For a bounded open `U ⊆ ℂ` and a pole
`x ∈ U`, if `xs i → x` along a countably generated filter `l`, then
`∫ |G_U(xs i, y) - G_U(x, y)| dy → 0`. The pole must lie in `U`; the points `xs i` need not, since
`G_U(z, ·) = 0` for `z ∉ U`. -/
theorem tendsto_integral_abs_greenFunction_sub {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {x : ℂ} (hx : x ∈ U) {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {xs : ι → ℂ} (hxs : Tendsto xs l (𝓝 x)) :
    Tendsto (fun i => ∫ y, |greenFunction U (xs i) y - greenFunction U x y|) l (𝓝 0) := by
  obtain ⟨C, -, hloc⟩ := exists_greenFunction_local_volume_bound hU hUb
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hT : Tendsto (fun r : ℝ => C * r ^ 2 * (1 + |Real.log r|)) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_sq_mul_one_add_abs_log.const_mul C
    rw [mul_zero] at h
    exact Tendsto.congr (fun r => by simp only [mul_assoc]) h
  obtain ⟨r, hrsmall, hr⟩ : ∃ r : ℝ, C * r ^ 2 * (1 + |Real.log r|) < ε / 4 ∧ 0 < r := by
    have h1 := (tendsto_order.1 hT).2 (ε / 4) (by positivity)
    have h2 : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
    obtain ⟨r, hr1, hr2⟩ := (h1.and h2).exists
    exact ⟨r, hr1, hr2⟩
  have hout := tendsto_integral_outside_ball_abs_greenFunction_sub hU hUb hx hxs hr
  have hsmallOut : ∀ᶠ i in l, (∫ y, Set.indicator (ball x r)ᶜ
      (fun y' => |greenFunction U (xs i) y' - greenFunction U x y'|) y) < ε / 2 :=
    (tendsto_order.1 hout).2 (ε / 2) (by positivity)
  filter_upwards [hsmallOut] with i hDi
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun y => abs_nonneg _)]
  have hsplit : (∫ y, |greenFunction U (xs i) y - greenFunction U x y|) =
      (∫ y in ball x r, |greenFunction U (xs i) y - greenFunction U x y|) +
        ∫ y in (ball x r)ᶜ, |greenFunction U (xs i) y - greenFunction U x y| :=
    (integral_add_compl measurableSet_ball
      (integrable_abs_greenFunction_sub_pole hU hUb (xs i) x)).symm
  have hcompl : (∫ y in (ball x r)ᶜ, |greenFunction U (xs i) y - greenFunction U x y|) =
      ∫ y, Set.indicator (ball x r)ᶜ
        (fun y' => |greenFunction U (xs i) y' - greenFunction U x y'|) y :=
    (integral_indicator measurableSet_ball.compl).symm
  have hball := integral_ball_abs_greenFunction_sub_le hU hUb hloc hr (xs i) x x
  linarith

/-- The same conclusion along `𝓝[U] x`: the zero-extended Green row is `L¹`-continuous in the pole on `U`. -/
theorem tendsto_integral_abs_greenFunction_sub_nhdsWithin {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {x : ℂ} (hx : x ∈ U) :
    Tendsto (fun z => ∫ y, |greenFunction U z y - greenFunction U x y|) (𝓝[U] x) (𝓝 0) :=
  tendsto_integral_abs_greenFunction_sub hU hUb hx (tendsto_id.mono_right nhdsWithin_le_nhds)

/-- Sequential form: for `xₙ → x` with `xₙ` eventually in `U`, along `𝓝[U] x`. -/
theorem tendsto_integral_abs_greenFunction_sub_atTop {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {x : ℂ} (hx : x ∈ U) {xs : ℕ → ℂ}
    (hxs : Tendsto xs atTop (𝓝[U] x)) :
    Tendsto (fun n => ∫ y, |greenFunction U (xs n) y - greenFunction U x y|) atTop (𝓝 0) :=
  tendsto_integral_abs_greenFunction_sub hU hUb hx (hxs.mono_right nhdsWithin_le_nhds)

end HarmonicBalls
