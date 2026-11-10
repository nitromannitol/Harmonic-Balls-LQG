import HarmonicBalls.Defs.Notation
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.Basic

/-!
# Bridge 1.2: the annulus `𝔸_{6/5,5}(0)` minus a closed disk is connected

Deterministic topology for the bridge `1.2` of the first-pass closure (assembled in `Closure/Bridge12.lean`).
Write `T := 𝔸_{6/5,5}(0) \ B̄(-9/2, 1/4)` (`annulus` of `Defs/Notation.lean`). The closed disk lies in
`{4.25 ≤ |z| ≤ 4.75}`. Main result: `isConnected_annulus_diff_closedBall : IsConnected T`.

Elementary proof in polar coordinates. Every `w ∈ T` is joined inside `T` to the circle `|z| = 3`, which is
connected and lies in `T`.
* If `Im w ≥ 0`, let `ρ = |w|`, `θ = arg w ∈ [0, π]`. The arc `v(s) = ρ e^{i ψ(s)}`, `ψ(s) = θ + s(π/2 - θ)`,
  runs from `w` to `ρ i`; then the segment `[ρ i, 3 i]` runs to the circle. On the arc `|v| = ρ` and
  `|v + 9/2|² = ρ² + 9 Re v + 81/4` with `Re v ≥ min (Re w) 0`, so the arc misses the closed disk. The segment
  has `Re = 0`, so it misses the disk too.
* If `Im w < 0`, apply the first case to `conj w`; `T` is invariant under complex conjugation.
-/

open Complex Metric Set Real

namespace HarmonicBalls.Closure

/-- Coordinate description of `T = 𝔸_{6/5,5}(0) \ B̄(-9/2, 1/4)`. -/
lemma bridge12_mem_iff (w : ℂ) :
    w ∈ annulus 0 (6 / 5) 5 \ Metric.closedBall (-9 / 2 : ℂ) (1 / 4) ↔
      36 / 25 < w.re ^ 2 + w.im ^ 2 ∧ w.re ^ 2 + w.im ^ 2 < 25 ∧
        1 / 16 < (w.re + 9 / 2) ^ 2 + w.im ^ 2 := by
  have hn : ∀ x : ℂ, ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := fun x => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hc : (w - (-9 / 2 : ℂ)).re = w.re + 9 / 2 := by simp; ring
  have him : (w - (-9 / 2 : ℂ)).im = w.im := by simp
  have e := hn (w - (-9 / 2 : ℂ))
  rw [hc, him] at e
  have e0 := hn w
  simp only [annulus, Set.mem_sdiff, mem_ball_zero_iff, mem_closedBall, dist_eq_norm, sub_zero,
    not_le]
  constructor
  · rintro ⟨⟨h5, h6⟩, h7⟩
    exact ⟨by nlinarith [norm_nonneg w], by nlinarith [norm_nonneg w],
      by nlinarith [norm_nonneg (w - (-9 / 2 : ℂ))]⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨by nlinarith [norm_nonneg w], by nlinarith [norm_nonneg w]⟩,
      by nlinarith [norm_nonneg (w - (-9 / 2 : ℂ))]⟩

/-- `T` is invariant under complex conjugation. -/
lemma bridge12_mem_conj (w : ℂ) :
    starRingEnd ℂ w ∈ annulus 0 (6 / 5) 5 \ Metric.closedBall (-9 / 2 : ℂ) (1 / 4) ↔
      w ∈ annulus 0 (6 / 5) 5 \ Metric.closedBall (-9 / 2 : ℂ) (1 / 4) := by
  rw [bridge12_mem_iff, bridge12_mem_iff]
  simp [Complex.conj_re, Complex.conj_im]

/-- Trigonometric bounds along the arc from `θ ∈ [0, π]` to `π/2`: the cosine stays `≥ 0` when `θ ≤ π/2`,
and never drops below `cos θ` when `θ ≥ π/2`. -/
lemma bridge12_cos_arc {θ s : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ π) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (θ ≤ π / 2 → 0 ≤ Real.cos (θ + s * (π / 2 - θ))) ∧
      (π / 2 ≤ θ → Real.cos θ ≤ Real.cos (θ + s * (π / 2 - θ))) := by
  have hp := Real.pi_pos
  constructor
  · intro h
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · nlinarith [mul_nonneg hs0 (sub_nonneg.2 h)]
    · nlinarith [mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 h)]
  · intro h
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · nlinarith [mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 h)]
    · exact hθπ
    · nlinarith [mul_nonneg hs0 (sub_nonneg.2 h)]

/-- For `Im w ≥ 0`: the arc from `w` to `|w| i`, then the segment from `|w| i` to `3 i`, is a connected
subset of `T` through `w` meeting the circle `|z| = 3`. -/
lemma bridge12_connected_upper (w : ℂ)
    (hw : w ∈ annulus 0 (6 / 5) 5 \ Metric.closedBall (-9 / 2 : ℂ) (1 / 4)) (him0 : 0 ≤ w.im) :
    ∃ Γ ⊆ annulus 0 (6 / 5) 5 \ Metric.closedBall (-9 / 2 : ℂ) (1 / 4),
      IsPreconnected Γ ∧ w ∈ Γ ∧ ∃ z ∈ Γ, ‖z‖ = 3 := by
  obtain ⟨h1, h2, h3⟩ := (bridge12_mem_iff w).1 hw
  have hp := Real.pi_pos
  have hn : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hρ0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hρlo : 6 / 5 < ‖w‖ := by nlinarith [hn, h1, hρ0]
  have hρhi : ‖w‖ < 5 := by nlinarith [hn, h2, hρ0]
  set ρ := ‖w‖
  have hρpos : 0 < ρ := by linarith
  set θ := Complex.arg w
  have hre : w.re = ρ * Real.cos θ := (Complex.norm_mul_cos_arg w).symm
  have him : w.im = ρ * Real.sin θ := (Complex.norm_mul_sin_arg w).symm
  have hθ0 : 0 ≤ θ := Complex.arg_nonneg_iff.2 him0
  have hθπ : θ ≤ π := Complex.arg_le_pi w
  obtain ⟨v, hv⟩ : ∃ v : ℝ → ℂ, ∀ s, v s = ((ρ * Real.cos (θ + s * (π / 2 - θ)) : ℝ) : ℂ) +
      ((ρ * Real.sin (θ + s * (π / 2 - θ)) : ℝ) : ℂ) * I :=
    ⟨fun s => ((ρ * Real.cos (θ + s * (π / 2 - θ)) : ℝ) : ℂ) +
      ((ρ * Real.sin (θ + s * (π / 2 - θ)) : ℝ) : ℂ) * I, fun s => rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℂ, ∀ t, f t = ((ρ + t * (3 - ρ) : ℝ) : ℂ) * I :=
    ⟨fun t => ((ρ + t * (3 - ρ) : ℝ) : ℂ) * I, fun t => rfl⟩
  have hvre : ∀ s, (v s).re = ρ * Real.cos (θ + s * (π / 2 - θ)) := by
    intro s
    rw [hv, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero]
  have hvim : ∀ s, (v s).im = ρ * Real.sin (θ + s * (π / 2 - θ)) := by
    intro s
    rw [hv, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
  have hfre : ∀ t, (f t).re = 0 := by
    intro t; rw [hf]; simp
  have hfim : ∀ t, (f t).im = ρ + t * (3 - ρ) := by
    intro t; rw [hf]; simp
  have hvc : Continuous v := by
    have : v = fun s => ((ρ * Real.cos (θ + s * (π / 2 - θ)) : ℝ) : ℂ) +
        ((ρ * Real.sin (θ + s * (π / 2 - θ)) : ℝ) : ℂ) * I := funext hv
    rw [this]; fun_prop
  have hfc : Continuous f := by
    have : f = fun t => ((ρ + t * (3 - ρ) : ℝ) : ℂ) * I := funext hf
    rw [this]; fun_prop
  -- the arc stays in `T`
  have harc : ∀ s ∈ Icc (0 : ℝ) 1, v s ∈ annulus 0 (6 / 5) 5 \ Metric.closedBall (-9 / 2 : ℂ) (1 / 4) := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hb := bridge12_cos_arc hθ0 hθπ hs0 hs1
    rw [bridge12_mem_iff, hvre s, hvim s]
    set ψ := θ + s * (π / 2 - θ)
    have hsc := Real.sin_sq_add_cos_sq ψ
    have hA : (ρ * Real.cos ψ) ^ 2 + (ρ * Real.sin ψ) ^ 2 = ρ ^ 2 := by
      linear_combination ρ ^ 2 * hsc
    have hB : (ρ * Real.cos ψ + 9 / 2) ^ 2 + (ρ * Real.sin ψ) ^ 2 =
        ρ ^ 2 + 9 * (ρ * Real.cos ψ) + 81 / 4 := by
      linear_combination ρ ^ 2 * hsc
    have hreq : (w.re + 9 / 2) ^ 2 + w.im ^ 2 = ρ ^ 2 + 9 * w.re + 81 / 4 := by
      linear_combination -hn
    rw [hA, hB]
    refine ⟨by linarith, by linarith, ?_⟩
    rcases lt_or_ge w.re 0 with hneg | hnn
    · have hθ' : π / 2 ≤ θ := by
        by_contra hc
        have hc' : θ < π / 2 := not_le.1 hc
        have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hc'.le⟩
        linarith [mul_nonneg hρ0 hcos]
      have hc := hb.2 hθ'
      have hmul := mul_le_mul_of_nonneg_left hc hρ0
      linarith
    · have hθ' : θ ≤ π / 2 := by
        by_contra hc
        have hc' : π / 2 < θ := not_le.1 hc
        have hcos := Real.cos_neg_of_pi_div_two_lt_of_lt hc' (by linarith)
        linarith [mul_neg_of_pos_of_neg hρpos hcos]
      have hcs := hb.1 hθ'
      linarith [mul_nonneg hρ0 hcs, sq_nonneg ρ]
  -- the segment `[ρ i, 3 i]` stays in `T`
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, f t ∈ annulus 0 (6 / 5) 5 \ Metric.closedBall (-9 / 2 : ℂ) (1 / 4) := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have ha : 0 < ρ - 6 / 5 := by linarith
    have hb : 0 < 5 - ρ := by linarith
    have hd1 : 0 < min (ρ - 6 / 5) (9 / 5) := lt_min ha (by norm_num)
    have hd2 : 0 < min (5 - ρ) 2 := lt_min hb (by norm_num)
    have hm1 : 6 / 5 < ρ + t * (3 - ρ) := by
      nlinarith [mul_le_mul_of_nonneg_left (min_le_left (ρ - 6 / 5) (9 / 5)) (sub_nonneg.2 ht1),
        mul_le_mul_of_nonneg_left (min_le_right (ρ - 6 / 5) (9 / 5)) ht0]
    have hm2 : ρ + t * (3 - ρ) < 5 := by
      nlinarith [mul_le_mul_of_nonneg_left (min_le_left (5 - ρ) 2) (sub_nonneg.2 ht1),
        mul_le_mul_of_nonneg_left (min_le_right (5 - ρ) 2) ht0]
    have hm0 : 0 < ρ + t * (3 - ρ) := by linarith
    rw [bridge12_mem_iff, hfre t, hfim t]
    refine ⟨by nlinarith, by nlinarith, by nlinarith [sq_nonneg (ρ + t * (3 - ρ))]⟩
  -- endpoints
  have hv0 : v 0 = w := Complex.ext (by rw [hvre, zero_mul, add_zero]; exact hre.symm)
    (by rw [hvim, zero_mul, add_zero]; exact him.symm)
  have hv10 : f 0 = v 1 := Complex.ext
    (by rw [hfre, hvre, one_mul, show θ + (π / 2 - θ) = π / 2 by ring, Real.cos_pi_div_two]; ring)
    (by rw [hfim, hvim, one_mul, show θ + (π / 2 - θ) = π / 2 by ring, Real.sin_pi_div_two]; ring)
  have hA : IsPreconnected (v '' Icc (0 : ℝ) 1) :=
    (isPreconnected_Icc : IsPreconnected (Icc (0 : ℝ) 1)).image v hvc.continuousOn
  have hB : IsPreconnected (f '' Icc (0 : ℝ) 1) :=
    (isPreconnected_Icc : IsPreconnected (Icc (0 : ℝ) 1)).image f hfc.continuousOn
  refine ⟨v '' Icc (0 : ℝ) 1 ∪ f '' Icc (0 : ℝ) 1, ?_, ?_,
    Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, hv0⟩, ?_⟩
  · rintro _ (⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact harc s hs
    · exact hseg t ht
  · exact IsPreconnected.union (v 1) ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
      ⟨0, ⟨le_rfl, zero_le_one⟩, hv10⟩ hA hB
  · refine ⟨f 1, Or.inr ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩, ?_⟩
    rw [hf, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      show ρ + 1 * (3 - ρ) = (3 : ℝ) by ring, abs_of_pos (by norm_num : (0 : ℝ) < 3)]

/-- Every point of `T` is joined inside `T` to the circle `|z| = 3` by a connected set. -/
lemma bridge12_connected_gap (w : ℂ)
    (hw : w ∈ annulus 0 (6 / 5) 5 \ Metric.closedBall (-9 / 2 : ℂ) (1 / 4)) :
    ∃ Γ ⊆ annulus 0 (6 / 5) 5 \ Metric.closedBall (-9 / 2 : ℂ) (1 / 4),
      IsPreconnected Γ ∧ w ∈ Γ ∧ ∃ z ∈ Γ, ‖z‖ = 3 := by
  rcases le_total 0 w.im with him | him
  · exact bridge12_connected_upper w hw him
  · obtain ⟨Γ, hΓ, hc, hwΓ, z, hzΓ, hz⟩ :=
      bridge12_connected_upper (starRingEnd ℂ w) ((bridge12_mem_conj w).2 hw)
        (by rw [Complex.conj_im]; linarith)
    refine ⟨starRingEnd ℂ '' Γ, ?_, hc.image _ Complex.continuous_conj.continuousOn,
      ⟨starRingEnd ℂ w, hwΓ, Complex.conj_conj w⟩, starRingEnd ℂ z, ⟨z, hzΓ, rfl⟩, by simp [hz]⟩
    rintro _ ⟨u, hu, rfl⟩
    exact (bridge12_mem_conj u).2 (hΓ hu)

/-- **Bridge 1.2 topology.** The annulus `𝔸_{6/5,5}(0)` minus the closed disk `B̄(-9/2, 1/4)` is connected. -/
theorem isConnected_annulus_diff_closedBall :
    IsConnected (annulus 0 (6 / 5) 5 \ Metric.closedBall (-9 / 2 : ℂ) (1 / 4)) := by
  have hS : IsConnected (Metric.sphere (0 : ℂ) 3) :=
    isConnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0 (by norm_num)
  have hST : Metric.sphere (0 : ℂ) 3 ⊆
      annulus 0 (6 / 5) 5 \ Metric.closedBall (-9 / 2 : ℂ) (1 / 4) := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [hz] at hn
    rw [bridge12_mem_iff]
    have hre : -3 ≤ z.re := by nlinarith [sq_nonneg z.im]
    exact ⟨by nlinarith, by nlinarith, by nlinarith⟩
  refine ⟨⟨3, hST (mem_sphere_zero_iff_norm.2 (by norm_num))⟩, ?_⟩
  refine isPreconnected_of_forall (3 : ℂ) fun y hy => ?_
  obtain ⟨Γ, hΓT, hΓc, hyΓ, z, hzΓ, hz⟩ := bridge12_connected_gap y hy
  refine ⟨Γ ∪ Metric.sphere 0 3, Set.union_subset hΓT hST,
    Or.inr (mem_sphere_zero_iff_norm.2 (by norm_num)), Or.inl hyΓ, ?_⟩
  exact IsPreconnected.union z hzΓ (mem_sphere_zero_iff_norm.2 hz) hΓc hS.isPreconnected

end HarmonicBalls.Closure
