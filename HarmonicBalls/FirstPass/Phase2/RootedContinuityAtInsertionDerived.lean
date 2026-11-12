import HarmonicBalls.FirstPass.S11r.RootedRootContinuity

/-!
# Continuity of a Weyl-scaled metric at a root under a locally bounded weight perturbation

Deterministic step towards `RootedPhysicalMetricContinuousAtInsertionFrozen` (`FirstPass/S11r/Frozen.lean:115`, the
continuity at the insertion of the metric of the rooted field, Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380,
Proposition 3.17).

Let `D` be a Euclidean length metric and `F` a weight such that the Weyl scaling `e^{ξ F} · D` is finite and is itself a
Euclidean length metric (Axiom I of the LQG metric for a field with a logarithmic singularity, `F = -γ log|· - p|` after
translation). If `ξ g ≤ C` on a Euclidean ball around `p`, then `(e^{ξ (F + g)} · D)(x, p) ≤ e^C (e^{ξ F} · D)(x, p)` for `x`
close to `p`, so `(e^{ξ (F + g)} · D)(x, p) → 0` as `x → p`. Almost optimal paths for `e^{ξ F} · D` from `x` to `p` stay
in the ball, since every point of such a path is `e^{ξ F} · D`-close to `p` (segment cost bound), and `e^{ξ F} · D`
induces the Euclidean topology.

Terminology: Weyl scaling `e^{ξ f} · D` (Duplantier-Sheffield; Gwynne-Miller).
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

/-- **Pathwise comparison of Weyl scalings.** If `ξ g ≤ C` at every point `w` whose `e^{ξ F} · D`-distance to `p` is below
`ε`, and `(e^{ξ F} · D)(x, p) < a ≤ ε`, then `(e^{ξ (F + g)} · D)(x, p) ≤ e^C a`. -/
theorem weylScaling_add_le_of_lt {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (ξ : ℝ) {F g : ℂ → ℝ}
    {p x : ℂ} {C ε : ℝ} {a : ℝ≥0∞}
    (hloc : ∀ w, weylScaling D ξ F w p < ENNReal.ofReal ε → ξ * g w ≤ C)
    (hxa : weylScaling D ξ F x p < a) (haε : a ≤ ENNReal.ofReal ε) :
    weylScaling D ξ (fun w => F w + g w) x p ≤ ENNReal.ofReal (Real.exp C) * a := by
  obtain ⟨T, q, hq, hq0, hqT, hcost⟩ : ∃ (T : ℝ) (q : ℝ → ℂ), IsLengthParametrized D q T ∧ q 0 = x ∧ q T = p ∧
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * F (q t))) < a := by
    have h := hxa
    unfold weylScaling at h
    simp only [iInf_lt_iff] at h
    obtain ⟨T, q, hq, hq0, hqT, h⟩ := h
    exact ⟨T, q, hq, hq0, hqT, h⟩
  have hpt : ∀ t ∈ Icc (0 : ℝ) T, ξ * g (q t) ≤ C := by
    intro t ht
    apply hloc
    have h1 := hD.weylScaling_le_segment_cost ξ F hq ht.1 ht.2 le_rfl
    rw [hqT] at h1
    calc weylScaling D ξ F (q t) p ≤ ∫⁻ s in Icc t T, ENNReal.ofReal (Real.exp (ξ * F (q s))) := h1
      _ ≤ ∫⁻ s in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * F (q s))) :=
          lintegral_mono_set (Icc_subset_Icc ht.1 le_rfl)
      _ < a := hcost
      _ ≤ ENNReal.ofReal ε := haε
  calc weylScaling D ξ (fun w => F w + g w) x p
      ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * (F (q t) + g (q t)))) := by
        rw [← hq0, ← hqT]
        unfold weylScaling
        exact iInf₂_le_of_le T q (iInf_le_of_le hq (iInf_le_of_le rfl (iInf_le_of_le rfl le_rfl)))
    _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp C) * ENNReal.ofReal (Real.exp (ξ * F (q t))) := by
        refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
        rw [mul_add]
        linarith [hpt t ht]
    _ = ENNReal.ofReal (Real.exp C) * ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * F (q t))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp C) * a := by gcongr

/-- **Continuity at the root under a locally bounded weight perturbation.** Let `D` be a Euclidean length metric and `F`
a weight such that `e^{ξ F} · D` is finite and (after `toReal`) a Euclidean length metric. If `ξ g ≤ C` on `ball p δ`,
then `(e^{ξ (F + g)} · D)(x, p) → 0` as `x → p`. -/
theorem tendsto_weylScaling_add_root {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (ξ : ℝ) {F g : ℂ → ℝ}
    (hE : IsEuclideanLengthMetric fun u v => (weylScaling D ξ F u v).toReal)
    (hfin : ∀ u v, weylScaling D ξ F u v ≠ ⊤) {p : ℂ} {δ C : ℝ} (hδ : 0 < δ)
    (hg : ∀ w ∈ ball p δ, ξ * g w ≤ C) :
    Tendsto (fun x => weylScaling D ξ (fun w => F w + g w) x p) (𝓝 p) (𝓝 0) := by
  obtain ⟨ε, hε, hεball⟩ := exists_dist_lt_of_ball hE hδ
  have hloc : ∀ w, weylScaling D ξ F w p < ENNReal.ofReal ε → ξ * g w ≤ C := by
    intro w hw
    refine hg w (hεball w ?_)
    have hs : (weylScaling D ξ F p w).toReal = (weylScaling D ξ F w p).toReal := hE.symm p w
    show (weylScaling D ξ F p w).toReal < ε
    rw [hs]
    exact ENNReal.toReal_lt_of_lt_ofReal hw
  rw [ENNReal.tendsto_nhds_zero]
  intro b hb
  have hK0 : ENNReal.ofReal (Real.exp C) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos C)).ne'
  have hKt : ENNReal.ofReal (Real.exp C) ≠ ⊤ := ENNReal.ofReal_ne_top
  set a : ℝ≥0∞ := min (ENNReal.ofReal ε) (b / ENNReal.ofReal (Real.exp C)) with ha_def
  have ha : 0 < a := lt_min (ENNReal.ofReal_pos.2 hε) (ENNReal.div_pos hb.ne' hKt)
  have haTop : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)
  have hapos : 0 < a.toReal := ENNReal.toReal_pos ha.ne' haTop
  have hp0 : p ∈ {v | (weylScaling D ξ F p v).toReal < a.toReal} := by
    show (weylScaling D ξ F p p).toReal < a.toReal
    have h0 : (weylScaling D ξ F p p).toReal = 0 := hE.self_eq_zero p
    rw [h0]
    exact hapos
  filter_upwards [(isOpen_dist_lt_set hE p a.toReal).mem_nhds hp0] with x hx
  have hx' : weylScaling D ξ F x p < a := by
    have hs : (weylScaling D ξ F p x).toReal = (weylScaling D ξ F x p).toReal := hE.symm p x
    have hx2 : (weylScaling D ξ F x p).toReal < a.toReal := by
      rw [← hs]
      exact hx
    rw [← ENNReal.ofReal_toReal (hfin x p)]
    exact (ENNReal.ofReal_lt_iff_lt_toReal ENNReal.toReal_nonneg haTop).2 hx2
  calc weylScaling D ξ (fun w => F w + g w) x p ≤ ENNReal.ofReal (Real.exp C) * a :=
        weylScaling_add_le_of_lt hD ξ hloc hx' (min_le_left _ _)
    _ ≤ ENNReal.ofReal (Real.exp C) * (b / ENNReal.ofReal (Real.exp C)) := by gcongr; exact min_le_right _ _
    _ = b := ENNReal.mul_div_cancel hK0 hKt

end HarmonicBalls
