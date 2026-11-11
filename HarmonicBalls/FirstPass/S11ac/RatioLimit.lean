import HarmonicBalls.FirstPass.S11ac.LocalIdentity

/-! # Local ratio constants between overlapping pieces

For two overlapping pieces `Ua`, `Ub` with a common disk `ball c r`, the ratio of the two masses at `(c, w n)`, where
`w n → c`, is eventually the ratio of the piece constants `β a / β b`: the internal metrics of `Ua` and `Ub` agree at
`(c, w n)` for large `n` (`LocalIdentity.eventually_internalMetric_eq`), and both masses are constant multiples of it.
-/

namespace HarmonicBalls.S11ac

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

/-- The limsup of the ratios `M a (c, w n) / M b (c, w n)` along `w n = c + r/(n+2)`, in `ℝ≥0∞`. -/
noncomputable def ratioLim {Ω' : Type*} (M : Ω' → ℕ → ℂ → ℂ → ℝ) (a b : ℕ) (c : ℂ) (r : ℝ) (ω : Ω') : ℝ≥0∞ :=
  limsup (fun n : ℕ => ENNReal.ofReal (M ω a c (c + ((r / ((n : ℝ) + 2) : ℝ) : ℂ)) /
    M ω b c (c + ((r / ((n : ℝ) + 2) : ℝ) : ℂ)))) atTop

theorem ratioLim_measurable {Ω' : Type*} [MeasurableSpace Ω'] {M : Ω' → ℕ → ℂ → ℂ → ℝ}
    (hM : ∀ a z w, Measurable fun ω => M ω a z w) (a b : ℕ) (c : ℂ) (r : ℝ) :
    Measurable (ratioLim M a b c r) := by
  unfold ratioLim
  refine Measurable.limsup fun n => ?_
  exact ENNReal.measurable_ofReal.comp ((hM a _ _).div (hM b _ _))

/-- Equal positive constants: if `ofReal x = ofReal y` and `0 < y`, then `x = y`. -/
theorem eq_of_ofReal_eq_of_pos {x y : ℝ} (hy : 0 < y) (h : ENNReal.ofReal x = ENNReal.ofReal y) : x = y := by
  have hx : 0 < x := by
    by_contra hx
    have h0 : ENNReal.ofReal x = 0 := ENNReal.ofReal_of_nonpos (not_lt.1 hx)
    have hpos : 0 < ENNReal.ofReal y := ENNReal.ofReal_pos.2 hy
    rw [h0] at h
    exact absurd h (ne_of_lt hpos)
  exact (ENNReal.ofReal_eq_ofReal_iff hx.le hy.le).1 h

/-- **Eventual ratio.** Let `D` be a length metric (nonnegative), `Ua`, `Ub` open with `ball c r ⊆ Ua ∩ Ub`, and let the
masses satisfy the local identities `ofReal (M a z w) = ofReal (β a) * internalMetric D Ua z w` on `Ua`, and likewise for
`b`. Then the ratio limsup is `ofReal (β a / β b)`. -/
theorem ratioLim_eq_of_identity {Ω' : Type*} (M : Ω' → ℕ → ℂ → ℂ → ℝ) (ω : Ω') (a b : ℕ) {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) (hnonneg : ∀ x y, 0 ≤ D x y) {Ua Ub : Set ℂ} (hUa : IsOpen Ua)
    (hUb : IsOpen Ub) {c : ℂ} {r : ℝ} (hr : 0 < r) (hsub : ball c r ⊆ Ua ∩ Ub) {βa βb : ℝ}
    (hβa : 0 < βa) (hβb : 0 < βb)
    (hA : ∀ z ∈ Ua, ∀ w ∈ Ua, ENNReal.ofReal (M ω a z w) = ENNReal.ofReal βa * internalMetric D Ua z w)
    (hB : ∀ z ∈ Ub, ∀ w ∈ Ub, ENNReal.ofReal (M ω b z w) = ENNReal.ofReal βb * internalMetric D Ub z w) :
    ratioLim M a b c r ω = ENNReal.ofReal (βa / βb) := by
  set w : ℕ → ℂ := fun n => c + ((r / ((n : ℝ) + 2) : ℝ) : ℂ) with hw
  have hpos : ∀ n : ℕ, 0 < r / ((n : ℝ) + 2) := fun n => by positivity
  have hwball : ∀ n, w n ∈ ball c r := by
    intro n
    rw [mem_ball, hw, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hpos n)]
    exact div_lt_self hr (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  have hwne : ∀ n, w n ≠ c := by
    intro n h
    have : ((r / ((n : ℝ) + 2) : ℝ) : ℂ) = 0 := by
      have := congrArg (fun z => z - c) h
      simpa [hw] using this
    exact (hpos n).ne' (by exact_mod_cast this)
  have hcUa : c ∈ Ua := (hsub (mem_ball_self hr)).1
  have hcUb : c ∈ Ub := (hsub (mem_ball_self hr)).2
  have hwUa : ∀ n, w n ∈ Ua := fun n => (hsub (hwball n)).1
  have hwUb : ∀ n, w n ∈ Ub := fun n => (hsub (hwball n)).2
  have hlim : Tendsto w atTop (𝓝 c) := by
    have h1 : Tendsto (fun n : ℕ => r / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    have h2 : Tendsto (fun n : ℕ => ((r / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto (0:ℝ)).comp h1
      rw [Complex.ofReal_zero] at this
      exact this
    have h3 := (tendsto_const_nhds (x := c)).add h2
    simpa [hw] using h3
  have hev := eventually_internalMetric_eq hD hnonneg hUa hUb hcUa hcUb hlim
  have hratio : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (M ω a c (w n) / M ω b c (w n)) =
      ENNReal.ofReal (βa / βb) := by
    filter_upwards [hev] with n hn
    obtain ⟨hna, hnb⟩ := hn
    have hDpos : 0 < D c (w n) := by
      rcases (hnonneg c (w n)).lt_or_eq with h | h
      · exact h
      · exact absurd (hD.eq_of_eq_zero _ _ h.symm).symm (hwne n)
    have hA' := hA c hcUa (w n) (hwUa n)
    have hB' := hB c hcUb (w n) (hwUb n)
    rw [hna, ← ENNReal.ofReal_mul hβa.le] at hA'
    rw [hnb, ← ENNReal.ofReal_mul hβb.le] at hB'
    have ha := eq_of_ofReal_eq_of_pos (mul_pos hβa hDpos) hA'
    have hb := eq_of_ofReal_eq_of_pos (mul_pos hβb hDpos) hB'
    rw [ha, hb, mul_div_mul_right _ _ hDpos.ne']
  unfold ratioLim
  rw [limsup_congr hratio, limsup_const]

end HarmonicBalls.S11ac
