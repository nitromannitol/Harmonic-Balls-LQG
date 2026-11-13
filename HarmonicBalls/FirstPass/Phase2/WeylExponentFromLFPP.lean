import HarmonicBalls.FirstPass.Phase2.LQGMetricXiPos
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSExistence
import HarmonicBalls.Proofs.GFF.BackgroundChargeParameter

/-!
# The Weyl exponent of an LQG metric from the LFPP exponent

For `ξ > 0` let `λ(ξ)` be the exponent of the median LFPP crossing distance of the unit square,
`𝔞_ε = ε^{λ(ξ) + o(1)}` (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, l. 285 and p. 10; Pfeffer,
arXiv:2104.04020, (1.4)), and `Q(ξ) = (1 - λ(ξ)) / ξ`. Here `𝔞_ε` is `LQGMetric.Blueprint.aEpsDF ξ ε`, the lower
median, under the law of the whole-plane GFF normalized by `h_1(0) = 0`, of the LFPP distance between the left and
right sides of `[0,1]²` along paths in `[0,1]²`.

The Weyl exponent `ξ` of a γ-LQG metric (`IsLQGMetric γ ξ 𝔇`) is `γ / d_γ` as soon as:
* (Pfeffer, Proposition 1.9) the LFPP exponent at the Weyl exponent of a γ-LQG metric is `1 - ξ Q_γ`,
  `Q_γ = 2/γ + γ/2` the coordinate change parameter (an LQG metric has scaling constants `c_r = r^{ξ Q_γ}`);
* (Ding-Gwynne, *The fractal dimension of LQG*, Theorem 1.5, with Ding-Gwynne, *Tightness of supercritical LFPP*,
  Proposition 1.1; quoted in DFGPS, p. 10, and Pfeffer, (1.4)) the LFPP exponent at `ξ = γ / d_γ` is `1 - ξ Q_γ`;
* (Pfeffer, p. 3, after (1.4)) `ξ ↦ Q(ξ)` is nonincreasing on `(0, ∞)`;
* (Ding-Gwynne, Theorems 1.1 and 1.2) `d_γ > 2`, and `d_γ` is continuous on `(0, 2)`.

The case `ξ ≤ 0` is excluded outright (`isLQGMetric_xi_pos`). The argument: if `ξ = γ'/d_γ'` then the two LFPP
exponents give `Q_γ = Q_γ'`, so `γ = γ'` since `Q` is strictly decreasing on `(0, 2)`; the values `γ'/d_γ'` cover
`(0, γ/d_γ]` (intermediate values, `γ'/d_γ' ≤ γ'/2`); and above `γ/d_γ` either `ξ` is again a value `γ'/d_γ'` with
`γ < γ' < 2`, or `γ'/d_γ' ≤ ξ` and the monotonicity of `Q` gives `Q_γ ≤ Q_γ' < Q_γ`.

## Main results
* `HarmonicBalls.eq_of_lfppExponent_of_strictAntiOn`: the real-variable argument, for an abstract exponent relation.
* `HarmonicBalls.xi_eq_xiGamma_of_lfppExponent`: `IsLQGMetric γ ξ 𝔇 → ξ = LQGMetric.xiGamma γ` for `0 < γ < 2`,
  from the four facts above.
-/

open Filter Topology Set

namespace HarmonicBalls

/-- **The real-variable step.** Let `E ξ λ` be a relation ("`λ` is the exponent at `ξ`") with at most one `λ` for
each `ξ`, let `Q` be strictly decreasing on `(0, 2)` and `f` continuous on `(0, 2)` with `0 < f γ ≤ γ / 2`, such that
`E (f γ) (1 - f γ Q γ)` for `γ ∈ (0, 2)` and `(1 - λ)/ξ` is nonincreasing in `ξ > 0`. If `ξ > 0` and
`E ξ (1 - ξ Q γ)` for some `γ ∈ (0, 2)`, then `ξ = f γ`. -/
theorem eq_of_lfppExponent_of_strictAntiOn {E : ℝ → ℝ → Prop} (hE : ∀ ξ l l', E ξ l → E ξ l' → l = l')
    {f Q : ℝ → ℝ} (hQ : StrictAntiOn Q (Ioo (0 : ℝ) 2))
    (hDG : ∀ γ ∈ Ioo (0 : ℝ) 2, E (f γ) (1 - f γ * Q γ))
    (hM : ∀ ξ ξ' l l', 0 < ξ → ξ ≤ ξ' → E ξ l → E ξ' l' → (1 - l') / ξ' ≤ (1 - l) / ξ)
    (hC : ContinuousOn f (Ioo (0 : ℝ) 2)) (hS : ∀ γ ∈ Ioo (0 : ℝ) 2, 0 < f γ ∧ f γ ≤ γ / 2)
    {γ ξ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 2) (hξ : 0 < ξ) (hP : E ξ (1 - ξ * Q γ)) : ξ = f γ := by
  -- a value `f γ'' = ξ` forces `γ'' = γ`
  have hval : ∀ γ'' ∈ Ioo (0 : ℝ) 2, f γ'' = ξ → ξ = f γ := by
    intro γ'' hγ'' hfξ
    have h1 := hDG γ'' hγ''
    rw [hfξ] at h1
    have h2 := hE ξ _ _ hP h1
    have hQeq : Q γ = Q γ'' := by
      have : ξ * Q γ = ξ * Q γ'' := by linarith
      exact mul_left_cancel₀ hξ.ne' this
    rw [← hfξ, hQ.injOn hγ hγ'' hQeq]
  -- intermediate values on a subinterval `[a, b]` of `(0, 2)`
  have hivt : ∀ a b, 0 < a → a ≤ b → b < 2 → ξ ∈ Icc (f a) (f b) ∨ ξ ∈ Icc (f b) (f a) →
      ∃ γ'' ∈ Ioo (0 : ℝ) 2, f γ'' = ξ := by
    intro a b ha hab hb hmem
    have hsub : Icc a b ⊆ Ioo (0 : ℝ) 2 := fun x hx => ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
    have hCab : ContinuousOn f (Icc a b) := hC.mono hsub
    rcases hmem with hm | hm
    · obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hab hCab hm
      exact ⟨x, hsub hx, hfx⟩
    · obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' hab hCab hm
      exact ⟨x, hsub hx, hfx⟩
  rcases lt_trichotomy ξ (f γ) with hlt | heq | hgt
  · -- below `f γ`: some `γ' < γ` has `f γ' < ξ`
    set a := min (γ / 2) ξ with ha_def
    have ha0 : 0 < a := lt_min (by linarith [hγ.1]) hξ
    have haγ : a < γ := (min_le_left _ _).trans_lt (by linarith [hγ.1])
    have haI : a ∈ Ioo (0 : ℝ) 2 := ⟨ha0, haγ.trans hγ.2⟩
    have hfa : f a ≤ ξ := (hS a haI).2.trans (by linarith [min_le_right (γ / 2) ξ, ha0])
    obtain ⟨γ'', hγ'', hf⟩ := hivt a γ ha0 haγ.le hγ.2 (Or.inl ⟨hfa, hlt.le⟩)
    exact hval γ'' hγ'' hf
  · exact heq
  · -- above `f γ`: compare with `γ' = (γ + 2)/2`
    set b := (γ + 2) / 2 with hb_def
    have hγb : γ < b := by linarith [hγ.2]
    have hb2 : b < 2 := by linarith [hγ.2]
    have hbI : b ∈ Ioo (0 : ℝ) 2 := ⟨hγ.1.trans hγb, hb2⟩
    by_cases hfb : f b ≤ ξ
    · exfalso
      have hm := hM (f b) ξ _ _ (hS b hbI).1 hfb (hDG b hbI) hP
      have hfb0 : 0 < f b := (hS b hbI).1
      have hl : (1 - (1 - ξ * Q γ)) / ξ = Q γ := by field_simp; ring
      have hr : (1 - (1 - f b * Q b)) / f b = Q b := by field_simp; ring
      rw [hl, hr] at hm
      exact absurd (hQ hγ hbI hγb) (not_lt.2 hm)
    · obtain ⟨γ'', hγ'', hf⟩ :=
        hivt γ b hγ.1 hγb.le hb2 (Or.inl ⟨hgt.le, (not_le.1 hfb).le⟩)
      exact hval γ'' hγ'' hf

/-- **The Weyl exponent of a γ-LQG metric is `γ / d_γ`**, from the LFPP exponent facts:
* `hP` (Pfeffer, arXiv:2104.04020, Proposition 1.9 with (1.4)): at the Weyl exponent `ξ > 0` of a γ-LQG metric the
  median LFPP crossing distance is `𝔞_ε = ε^{1 - ξ Q_γ + o(1)}`;
* `hDG` (Ding-Gwynne, arXiv:1807.01072, Theorem 1.5, with Ding-Gwynne, Proposition 1.1 of *Tightness of
  supercritical Liouville first passage percolation*; DFGPS, p. 10): the same at `ξ = γ / d_γ`;
* `hM` (Pfeffer, p. 3): `Q(ξ) = (1 - λ(ξ))/ξ` is nonincreasing in `ξ > 0`;
* `hC`, `hS` (Ding-Gwynne, arXiv:1807.01072, Theorems 1.2 and 1.1): `d_γ` is continuous on `(0, 2)` and `d_γ > 2`. -/
theorem xi_eq_xiGamma_of_lfppExponent
    (hP : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      Tendsto (fun ε => Real.log (LQGMetric.Blueprint.aEpsDF ξ ε) / Real.log ε) (𝓝[>] 0)
        (𝓝 (1 - ξ * lqgQ γ)))
    (hDG : ∀ γ : ℝ, 0 < γ → γ < 2 →
      Tendsto (fun ε => Real.log (LQGMetric.Blueprint.aEpsDF (LQGMetric.xiGamma γ) ε) / Real.log ε) (𝓝[>] 0)
        (𝓝 (1 - LQGMetric.xiGamma γ * lqgQ γ)))
    (hM : ∀ ξ ξ' l l' : ℝ, 0 < ξ → ξ ≤ ξ' →
      Tendsto (fun ε => Real.log (LQGMetric.Blueprint.aEpsDF ξ ε) / Real.log ε) (𝓝[>] 0) (𝓝 l) →
      Tendsto (fun ε => Real.log (LQGMetric.Blueprint.aEpsDF ξ' ε) / Real.log ε) (𝓝[>] 0) (𝓝 l') →
      (1 - l') / ξ' ≤ (1 - l) / ξ)
    (hC : ContinuousOn LQGMetric.dGamma (Ioo (0 : ℝ) 2))
    (hS : ∀ γ : ℝ, 0 < γ → γ < 2 → 2 < LQGMetric.dGamma γ) :
    ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ := by
  intro γ ξ hγ hγ2 𝔇 h𝔇
  have hξ : 0 < ξ := isLQGMetric_xi_pos γ ξ 𝔇 hγ hγ2 h𝔇
  set E : ℝ → ℝ → Prop := fun ξ l =>
    Tendsto (fun ε => Real.log (LQGMetric.Blueprint.aEpsDF ξ ε) / Real.log ε) (𝓝[>] 0) (𝓝 l) with hE_def
  have hEu : ∀ ξ l l', E ξ l → E ξ l' → l = l' := fun _ _ _ h h' => tendsto_nhds_unique h h'
  have hxi : ∀ γ' ∈ Ioo (0 : ℝ) 2, LQGMetric.xiGamma γ' = γ' / LQGMetric.dGamma γ' := fun _ _ => rfl
  have hfC : ContinuousOn LQGMetric.xiGamma (Ioo (0 : ℝ) 2) := by
    refine (continuousOn_id.div hC fun x hx => ?_).congr fun x hx => hxi x hx
    exact (lt_trans two_pos (hS x hx.1 hx.2)).ne'
  have hfS : ∀ γ' ∈ Ioo (0 : ℝ) 2, 0 < LQGMetric.xiGamma γ' ∧ LQGMetric.xiGamma γ' ≤ γ' / 2 := by
    intro γ' hγ'
    have hd := hS γ' hγ'.1 hγ'.2
    rw [hxi γ' hγ']
    exact ⟨div_pos hγ'.1 (two_pos.trans hd), div_le_div_of_nonneg_left hγ'.1.le two_pos hd.le⟩
  exact eq_of_lfppExponent_of_strictAntiOn (E := E) hEu lqgQ_strictAntiOn
    (fun γ' hγ' => hDG γ' hγ'.1 hγ'.2) hM hfC hfS ⟨hγ, hγ2⟩ hξ (hP γ ξ hγ hγ2 hξ 𝔇 h𝔇)

end HarmonicBalls
