import HarmonicBalls.Steps.Sec11.PunctureCrossing
import HarmonicBalls.Steps.Sec11.BoundaryClearance

/-! # Locality of point removal

Point removal for the internal metric is a local property: once it holds on
one open neighborhood, it holds on every smaller open neighborhood.
-/

namespace HarmonicBalls

open Set Metric Filter Topology
open scoped ENNReal NNReal

/-- Point removal on an open neighborhood restricts to each smaller open
neighborhood of the origin. -/
theorem IsEuclideanLengthMetric.internalMetric_sdiff_zero_eq_of_subset
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {V W : Set ℂ} (hV : IsOpen V) (hW : IsOpen W)
    (hzero : (0 : ℂ) ∈ W) (hWV : W ⊆ V)
    (hremove : ∀ a ∈ V \ {0}, ∀ b ∈ V \ {0},
      internalMetric D (V \ {0}) a b = internalMetric D V a b) :
    ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
      internalMetric D (W \ {0}) x y = internalMetric D W x y := by
  have hzeroV : (0 : ℂ) ∈ V := hWV hzero
  have hnonneg (x y : ℂ) : 0 ≤ D x y := by
    have h := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at h
    linarith
  obtain ⟨δ, hδ, hball⟩ := (hD.isOpen_iff W).mp hW 0 hzero
  have hcont : Continuous (fun x => D 0 x) := by
    simpa only [hD.symm 0] using hD.continuous_left 0
  have hopen : IsOpen {x : ℂ | D 0 x < δ / 4} :=
    isOpen_lt hcont continuous_const
  have hmem : (0 : ℂ) ∈ {x : ℂ | D 0 x < δ / 4} := by
    simp only [mem_ofPred_eq, hD.self_eq_zero]
    linarith
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hopen 0 hmem
  have hdetour := hD.small_detours_of_internalMetric_sdiff_zero_eq hV hzeroV hremove
  intro x y hx hy
  apply hD.internalMetric_sdiff_zero_eq_of_small_detours hx hy
  intro ε hε
  let τ : ℝ≥0 := ⟨δ / 4, by linarith⟩
  let e : ℝ≥0 := min ε τ
  have he : 0 < e := lt_min hε (by dsimp [τ]; exact_mod_cast (show 0 < δ / 4 by linarith))
  obtain ⟨r, hr, hshort⟩ := hdetour e he
  refine ⟨min r ρ, lt_min hr hρ, ?_⟩
  intro a b ha hb ha0 hb0 har hbr
  have har' : ‖a‖ < r := lt_of_lt_of_le har (min_le_left _ _)
  have hbr' : ‖b‖ < r := lt_of_lt_of_le hbr (min_le_left _ _)
  have haρ : ‖a‖ < ρ := lt_of_lt_of_le har (min_le_right _ _)
  have haδ : D 0 a < δ / 4 := hρsub (by simpa only [mem_ball, dist_zero_right] using haρ)
  have hclear : ∀ w ∉ W, δ / 2 ≤ D a w := by
    intro w hw
    have hwδ : δ ≤ D 0 w := by
      by_contra hn
      exact hw (hball w (lt_of_not_ge hn))
    have ht := hD.triangle 0 a w
    linarith
  have hp := hshort a b (hWV ha) (hWV hb) ha0 hb0 har' hbr'
  obtain ⟨p, hpV, hplen⟩ : ∃ p : Path a b,
      (∀ u, p u ∈ V \ {0}) ∧ pathLength D p < e := by
    unfold internalMetric at hp
    simpa only [iInf_lt_iff, exists_prop] using hp
  have heτ : (e : ℝ≥0∞) ≤ τ := by exact_mod_cast (min_le_right ε τ)
  have hτδ : (τ : ℝ≥0∞) < ENNReal.ofReal (δ / 2) := by
    rw [ENNReal.coe_nnreal_eq]
    change ENNReal.ofReal (δ / 4) < ENNReal.ofReal (δ / 2)
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).2 (by linarith)
  have hpW := hD.path_stays_inside_of_boundary_clearance hnonneg hclear p
    ((hplen.trans_le heτ).trans hτδ)
  have hpW0 : ∀ u, p u ∈ W \ {0} := fun u => ⟨hpW u, (hpV u).2⟩
  have hle : internalMetric D (W \ {0}) a b ≤ pathLength D p :=
    iInf_le_of_le p (iInf_le _ hpW0)
  exact (hle.trans_lt hplen).trans_le (by exact_mod_cast (min_le_left ε τ))


end HarmonicBalls
