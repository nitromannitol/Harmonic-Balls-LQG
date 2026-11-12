import HarmonicBalls.FirstPass.Phase2.RootedContinuityAtInsertionDerived
import HarmonicBalls.FirstPass.Phase2.AxiomsUnivDerived
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsDerived
import HarmonicBalls.FirstPass.S11r.RootedTranslate

/-!
# Continuity of the physical metric of the rooted field at its insertion

`RootedPhysicalMetricContinuousAtInsertionFrozen` (`FirstPass/S11r/Frozen.lean:115`; Dubédat-Falconet-Gwynne-Pfeffer-Sun,
arXiv:1905.00380, Proposition 3.17) is proved here from results already established in this repository.

Fix `z ≠ 0`. Translating by `z`, the field `h(· + z)` is the normalised translated field `T` plus the constant circle
average `c = h_1(z)`, so by translation covariance and the constant Weyl shift (Axioms III and IV),
`𝔇_h(x + z, y + z) = e^{ξ c} 𝔇_T(x, y)`. The rooted weight `W(w) = -α log|w| - γ log|w - z| + γ log max(1, |w|)` becomes
`W(u + z) = -γ log|u| + g(u)` with `g` continuous at `0`. Axiom I for the field `T - γ log|·|` (Fact 2.2 with insertion
`γ < Q`) says that `e^{-ξ γ log|·|} · 𝔇_T` is finite and a Euclidean length metric; the deterministic comparison
`tendsto_weylScaling_add_root` then gives `(e^{ξ W} · 𝔇_h)(x, z) → 0` as `x → z`.

Terminology: Weyl scaling `e^{ξ f} · D` (Duplantier-Sheffield; Gwynne-Miller), insertion (Dubédat-Falconet-Gwynne-Pfeffer-Sun).
-/

universe u

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

/-- Continuity at the insertion of the metric of the rooted field (DFGPS Proposition 3.17, in the form of
`RootedPhysicalMetricContinuousAtInsertionFrozen`), from the field axioms at insertion `γ` (Fact 2.2) and the axioms of
the LQG metric (translation covariance and Weyl scaling). -/
theorem rootedPhysicalMetricContinuousAtInsertion_of_axioms (hU : LQGMetricSatisfiesAxiomsUnivFrozen.{u})
    (hField : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    RootedPhysicalMetricContinuousAtInsertionFrozen.{u} := by
  intro γ ξ α z hγ0 hγ2 _hα hz Ω _ P _ hC hcirc hG 𝔇 h𝔇
  have hγlt : γ < lqgQ γ := S11c.gamma_lt_lqgQ hγ0 hγ2
  have hGT := S11c.isWholePlaneGFF_translate hG z
  have hshift := ae_wholePlane_weylScaling_shift_univ hU P γ ξ (S11c.translatedPairing hC hcirc z)
    (S11c.translatedCircle hcirc z) 𝔇 h𝔇 hGT (fun ω _ => hcirc ω 1 z) (fun ω => continuous_const)
    (fun _ => hG.measurable_circle 1 z one_pos)
  have hSat := hU γ ξ 𝔇 h𝔇 Ω P hC hcirc (fun _ _ => 0) hG (fun ω => continuous_const) (fun _ => measurable_const)
  have hIV := hSat.coordChange 1 one_pos z
  have hI := (hField Ω P γ ξ γ (S11c.translatedPairing hC hcirc z)
    (S11c.translatedCircle hcirc z) hGT hγ0 hγ2 hγlt 𝔇 h𝔇).1
  filter_upwards [hshift, hIV, hI] with ω hsh hiv hi
  set T := S11c.translatedPairing hC hcirc z ω with hT
  set c : ℝ := hcirc ω 1 z with hc
  set D : ℂ → ℂ → ℝ := 𝔇 T with hD_def
  have hD : IsEuclideanLengthMetric D := hsh.1
  have hBlen : IsEuclideanLengthMetric (𝔇 (addFunPairing T (fun _ => c))) := hsh.2.1
  have hBW := hsh.2.2.2.1
  -- the field identity at translated points (Axiom IV at `r = 1`)
  have hIVω : ∀ x y : ℂ, 𝔇 (hC ω) (x + z) (y + z) = 𝔇 (addFunPairing T (fun _ => c)) x y := by
    intro x y
    have h := hiv x y
    simp only [Complex.ofReal_one, one_mul, addFunPairing_zero_const', Real.log_one, mul_zero] at h
    rw [affinePullback_one_eq_translated hC hcirc z ω] at h
    exact h
  -- the constant Weyl shift of the field (Axiom III)
  have hBfun : ∀ x y : ℂ, 𝔇 (addFunPairing T (fun _ => c)) x y = Real.exp (ξ * c) * D x y := by
    intro x y
    have h2 : weylScaling D ξ (fun _ => c) x y =
        ENNReal.ofReal (Real.exp (ξ * c)) * ENNReal.ofReal (D x y) := by
      have h := weylScaling_add_const D ξ c (fun _ => 0) x y
      have h0 : weylScaling D ξ (fun _ => (0 : ℝ)) x y = ENNReal.ofReal (D x y) := hD.weylScaling_zero ξ x y
      simp only [zero_add] at h
      rw [h, h0]
    refine (ENNReal.ofReal_eq_ofReal_iff (nonneg_of_isEuclideanLengthMetric' hBlen x y)
      (mul_nonneg (Real.exp_pos _).le (nonneg_of_isEuclideanLengthMetric' hD x y))).mp ?_
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ← h2]
    exact hBW x y
  have hfunR : (fun x y => 𝔇 (hC ω) ((Homeomorph.addRight z) x) ((Homeomorph.addRight z) y)) =
      fun x y => Real.exp (ξ * c) * D x y := by
    funext x y
    rw [Homeomorph.coe_addRight, hIVω, hBfun]
  -- the weights: the rooted weight at `u + z` is the insertion weight at `0` plus a weight continuous at `0`
  set W : ℂ → ℝ := fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖) with hW
  set F : ℂ → ℝ := fun u => -γ * Real.log ‖u‖ with hF
  set g : ℂ → ℝ := fun u => -α * Real.log ‖u + z‖ + γ * Real.log (max 1 ‖u + z‖) with hg
  have hWc : W ∘ (Homeomorph.addRight z) = fun u => F u + g u := by
    funext u
    simp only [Function.comp_apply, Homeomorph.coe_addRight, hW, hF, hg, add_sub_cancel_right]
    ring
  have hkey : ∀ u, weylScaling (𝔇 (hC ω)) ξ W (u + z) z =
      ENNReal.ofReal (Real.exp (ξ * c)) * weylScaling D ξ (fun u => F u + g u) u 0 := by
    intro u
    have h := weylScaling_comp_homeomorph (𝔇 (hC ω)) ξ W (Homeomorph.addRight z) u 0
    have e1 : (Homeomorph.addRight z) u = u + z := rfl
    have e2 : (Homeomorph.addRight z) 0 = z := by simp
    rw [e1, e2, hfunR, hWc, hD.weylScaling_const_mul (Real.exp_pos _)] at h
    exact h.symm
  -- Axiom I at insertion `γ` for the translated field
  have hE : IsEuclideanLengthMetric fun u v => (weylScaling D ξ F u v).toReal := hi.2
  have hfin : ∀ u v, weylScaling D ξ F u v ≠ ⊤ := fun u v => (hi.1 u v).ne
  -- the perturbation `ξ g` is bounded above near `0`
  have hgc : ContinuousAt (fun u : ℂ => ξ * g u) 0 := by
    have h1 : ContinuousAt (fun u : ℂ => Real.log ‖u + z‖) 0 :=
      ContinuousAt.log (continuous_norm.comp (continuous_id.add continuous_const)).continuousAt
        (by simpa using hz)
    have h2 : Continuous (fun u : ℂ => Real.log (max 1 ‖u + z‖)) :=
      Continuous.log (continuous_const.max (continuous_norm.comp (continuous_id.add continuous_const)))
        (fun x => (lt_of_lt_of_le one_pos (le_max_left _ _)).ne')
    exact continuousAt_const.mul ((continuousAt_const.mul h1).add (continuousAt_const.mul h2.continuousAt))
  have hev : ∀ᶠ u in 𝓝 (0 : ℂ), ξ * g u ≤ ξ * g 0 + 1 := hgc (Iic_mem_nhds (lt_add_one _))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have htend := tendsto_weylScaling_add_root hD ξ hE hfin hδ (fun w hw => hball w hw)
  have hsub : Tendsto (fun x : ℂ => x - z) (𝓝 z) (𝓝 0) := tendsto_sub_nhds_zero_iff.mpr tendsto_id
  have hlim := ENNReal.Tendsto.const_mul (htend.comp hsub)
    (Or.inr (ENNReal.ofReal_ne_top (r := Real.exp (ξ * c))))
  rw [mul_zero] at hlim
  refine hlim.congr (fun x => ?_)
  simp only [Function.comp_apply]
  rw [← hkey (x - z), sub_add_cancel]

/-- **Derived.** `RootedPhysicalMetricContinuousAtInsertionFrozen` (DFGPS Proposition 3.17, continuity of the metric of
the rooted field at its insertion) in every universe, without inputs: the field axioms (Fact 2.2) and the axioms of the
LQG metric are proved (`lqgMetricFieldAxiomsUnivFrozen_derived`, `lqgMetricSatisfiesAxiomsUniv_derived`). -/
theorem rootedPhysicalMetricContinuousAtInsertion_derived :
    RootedPhysicalMetricContinuousAtInsertionFrozen.{u} :=
  rootedPhysicalMetricContinuousAtInsertion_of_axioms lqgMetricSatisfiesAxiomsUniv_derived
    lqgMetricFieldAxiomsUnivFrozen_derived

end HarmonicBalls
