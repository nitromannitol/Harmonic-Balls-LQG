import HarmonicBalls.Draft.Section11

/-! # Strict margins for the second auxiliary pinch event

Proposition 11.9 supplies weak diameter and mass estimates at arbitrary
positive thresholds. Tightening those thresholds gives simultaneous strict
inequalities with positive inner probability. Conditional transfer through the
GFF domain Markov property remains a separate step.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

universe u

/-- Proposition 11.9 gives a strict small internal diameter and strict large
mass with positive inner probability, for arbitrary positive diameter and
nonnegative mass thresholds. -/
theorem strict_internalDiam_largeMass_of_smallMetricDiameterLargeMass
    (hsmall : SmallMetricDiameterLargeMassStmt.{u})
    {γ α₀ ξ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (U V : Set ℂ) (δ : ℝ)
    (hU : IsOpen U) (hcU : IsConnected U) (hbU : Bornology.IsBounded U)
    (hV : IsOpen V) (hcV : IsConnected V) (hbV : Bornology.IsBounded V)
    (hW : IsOpen (thickening δ V)) (hcW : IsConnected (thickening δ V))
    (hbW : Bornology.IsBounded (thickening δ V))
    (hUV : U ⊆ V) (hVW : V ⊆ thickening δ V)
    (hclV : closure V ⊆ thickening δ V)
    (hdisj : Disjoint (thickening δ V) (sphere 0 1))
    (C ε : ℝ) (hC₀ : 0 ≤ C) (hε : 0 < ε) :
    ∃ A ⊆ {ω | internalDiam (D ω) δ V < ENNReal.ofReal ε ∧
      ENNReal.ofReal C < μ ω U}, MeasurableSet A ∧ 0 < P A := by
  have hεhalf : 0 < ε / 2 := by linarith
  have horder : ε / 2 < C + ε + 1 := by linarith
  obtain ⟨A, hA, hAm, hAp⟩ := hsmall γ α₀ ξ hγ hγ₂ hα Ω P hC hcirc μ D
    hgff hμ hD U V (thickening δ V) hU hcU hbU hV hcV hbV hW hcW hbW
    hUV hVW hclV hdisj (C + ε + 1) (ε / 2) hεhalf horder
  refine ⟨A, ?_, hAm, hAp⟩
  intro ω hω
  obtain ⟨hdiam, hmass⟩ := hA hω
  have hdiam' : internalDiam (D ω) δ V ≤ ENNReal.ofReal (ε / 2) := by
    unfold internalDiam
    exact iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy =>
      hdiam x hx y hy
  have hεstrict : ENNReal.ofReal (ε / 2) < ENNReal.ofReal ε :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hεhalf.le).2 (by linarith)
  have hCstrict : ENNReal.ofReal C < ENNReal.ofReal (C + ε + 1) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hC₀).2 (by linarith)
  exact ⟨hdiam'.trans_lt hεstrict, hCstrict.trans_le hmass⟩

/-- The geometry of the pinch proof configuration supplies the hypotheses
needed for the strict mass and diameter estimates. -/
theorem IsPinchPointProofConfiguration.strict_internalDiam_largeMass
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hconfig : IsPinchPointProofConfiguration U V W T Q' Q δ)
    (hsmall : SmallMetricDiameterLargeMassStmt.{u})
    {γ α₀ ξ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (C ε : ℝ) (hC₀ : 0 ≤ C) (hε : 0 < ε) :
    ∃ A ⊆ {ω | internalDiam (D ω) δ V < ENNReal.ofReal ε ∧
      ENNReal.ofReal C < μ ω U}, MeasurableSet A ∧ 0 < P A := by
  have hδ := hconfig.δ₀_mem.1
  have hUV : U ⊆ V := subset_closure.trans hconfig.closure_U_subset_V
  have hbU : Bornology.IsBounded U :=
    isBounded_ball.subset (hconfig.U_subset.trans (by intro x hx; exact hx.1))
  have hbV : Bornology.IsBounded V :=
    isBounded_ball.subset (hconfig.V_subset.trans (by intro x hx; exact hx.1))
  obtain ⟨c, ρU, ρV, ρW, hU, hV, hW⟩ := hconfig.concentric
  have hVne : V.Nonempty := hconfig.isConnected_U.nonempty.mono hUV
  have hρV : 0 < ρV := by rw [hV, nonempty_ball] at hVne; exact hVne
  have hcV : IsConnected V := by rw [hV]; exact isConnected_ball hρV
  have hVopen : IsOpen V := by rw [hV]; exact isOpen_ball
  have hcTh : IsConnected (thickening δ V) := by
    rw [hV, thickening_ball hδ hρV]
    exact isConnected_ball (by linarith)
  have hThW : thickening δ V ⊆ W := by
    exact (thickening_mono (by linarith : δ ≤ 10 * δ) V).trans
      (subset_closure.trans hconfig.thickening_V)
  have hdisj : Disjoint (thickening δ V) (sphere (0 : ℂ) 1) := by
    apply disjoint_left.mpr
    intro x hx hxsp
    have hxann := hconfig.W_subset (hThW hx)
    have hxclosed : x ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall, ← mem_sphere.mp hxsp]
    exact hxann.2 hxclosed
  exact strict_internalDiam_largeMass_of_smallMetricDiameterLargeMass hsmall hγ hγ₂ hα
    P hC hcirc μ D hgff hμ hD U V δ hconfig.isOpen_U hconfig.isConnected_U hbU
    hVopen hcV hbV isOpen_thickening hcTh hbV.thickening hUV
    (self_subset_thickening hδ V) (closure_subset_thickening hδ V) hdisj C ε hC₀ hε

end HarmonicBalls
