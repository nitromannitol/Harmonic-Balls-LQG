import HarmonicBalls.Proofs.Sec10.CrossingLocalization

/-!
# Crossing counts with a pole-containing exceptional component

The component containing the pole is unique. If a local Harnack estimate
holds for all other components, it controls all crossing components up to
one exception. The local estimate is an explicit deterministic hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Topology
open scoped ENNReal

/-- A mass lower bound for all but one crossing component gives one extra
term in the crossing count. -/
theorem encard_crossingComponents_le_ceil_inv_add_one
    (μ : Measure ℂ) (Λ A : Set ℂ) (hΛ : IsOpen Λ) (hA : MeasurableSet A)
    (hAfin : μ A ≠ ∞) {α : ℝ} (hα : 0 < α) (w : ℂ) (r s : ℝ)
    (C₀ : Set ℂ)
    (hmass : ∀ C ∈ crossingComponents (Λ ∩ ball w s) w r s, C ≠ C₀ →
      ENNReal.ofReal α * μ A < μ (C ∩ A)) :
    (crossingComponents (Λ ∩ ball w s) w r s).encard ≤ ⌈1 / α⌉₊ + 1 := by
  classical
  let S := crossingComponents (Λ ∩ ball w s) w r s
  let T := S \ {C₀}
  have hcount : T.encard ≤ ⌈1 / α⌉₊ := by
    by_cases hzero : μ A = 0
    · have hT : T = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro C hC
        have hlt := hmass C hC.1 (by simpa using hC.2)
        have hle : μ (C ∩ A) ≤ μ A := measure_mono inter_subset_right
        rw [hzero] at hlt hle
        simp only [mul_zero] at hlt
        exact (not_lt_of_ge hle) hlt
      simp [hT]
    · apply encard_le_ceil_inv_of_disjoint_mass μ A hzero hAfin hα T (fun C => C ∩ A)
      · intro C hC
        obtain ⟨⟨x, hx, rfl⟩, _⟩ := hC.1
        exact ((hΛ.inter isOpen_ball).connectedComponentIn.measurableSet).inter hA
      · intro C hC
        exact inter_subset_right
      · intro C hC D hD hne
        have hd := pairwiseDisjoint_connectedComponentsIn (Λ ∩ ball w s) hC.1.1 hD.1.1 hne
        exact hd.mono inter_subset_left inter_subset_left
      · intro C hC
        exact (hmass C hC.1 (by simpa using hC.2)).le
  have hle := encard_le_encard_sdiff_add_encard S ({C₀} : Set (Set ℂ))
  have hbound : (S \ {C₀}).encard + 1 ≤ (⌈1 / α⌉₊ : ℕ∞) + 1 :=
    add_le_add hcount le_rfl
  exact hle.trans (by simpa only [encard_singleton] using hbound)

/-- A local mass estimate away from the pole bounds the large-ball crossing
count with only the pole-containing component left exceptional. -/
theorem encard_crossingComponents_of_local_mass_away_from_pole
    (μ : Measure ℂ) (Λ A : Set ℂ) (hΛ : IsOpen Λ) (hA : MeasurableSet A)
    (hAfin : μ A ≠ ∞) {α : ℝ} (hα : 0 < α)
    (w x₀ z : ℂ) (r R q ρ : ℝ) (hqr : q ≤ ρ)
    (hinner : sphere w r ⊆ ball x₀ q) (houter : ball x₀ ρ ⊆ ball w R)
    (hcomponent : ∀ D ∈ connectedComponentsIn (Λ ∩ ball x₀ ρ), z ∉ D →
      μ (D ∩ A) ≤ ENNReal.ofReal α * μ A → D ∩ closedBall x₀ q = ∅) :
    (crossingComponents (Λ ∩ ball w R) w r R).encard ≤ ⌈1 / α⌉₊ + 1 := by
  let C₀ := connectedComponentIn (Λ ∩ ball w R) z
  apply encard_crossingComponents_le_ceil_inv_add_one μ Λ A hΛ hA hAfin hα w r R C₀
  intro C hC hCne
  obtain ⟨x, hxcl, hxsphere⟩ := hC.2.1
  have hxball : x ∈ ball x₀ q := hinner hxsphere
  obtain ⟨y, hyball, hyC⟩ := mem_closure_iff.mp hxcl _ isOpen_ball hxball
  obtain ⟨p, hp, hpC⟩ := hC.1
  have hyF : y ∈ Λ ∩ ball x₀ ρ := by
    refine ⟨(connectedComponentIn_subset (Λ ∩ ball w R) p (hpC ▸ hyC)).1, ?_⟩
    exact ball_subset_ball hqr hyball
  let D := connectedComponentIn (Λ ∩ ball x₀ ρ) y
  have hD : D ∈ connectedComponentsIn (Λ ∩ ball x₀ ρ) := ⟨y, hyF, rfl⟩
  have hDC : D ⊆ C := by
    rw [← hpC]
    exact connectedComponentIn_mono_of_mem (inter_subset_inter_right Λ houter) hyF (hpC ▸ hyC)
  have hzC : z ∉ C := by
    intro hzC
    apply hCne
    rw [← hpC]
    exact connectedComponentIn_eq (hpC ▸ hzC)
  have hzD : z ∉ D := fun hzD => hzC (hDC hzD)
  have hmassD : ENNReal.ofReal α * μ A < μ (D ∩ A) := by
    apply lt_of_not_ge
    intro hsmall
    have hyD : y ∈ D := mem_connectedComponentIn hyF
    have hy : y ∈ D ∩ closedBall x₀ q := ⟨hyD, ball_subset_closedBall hyball⟩
    rw [hcomponent D hD hzD hsmall] at hy
    exact hy
  exact hmassD.trans_le (measure_mono (inter_subset_inter_left A hDC))

/-- The extra exceptional component can be absorbed into the usual
`⌈1 / α⌉` form by halving the positive mass fraction. -/
theorem ceil_inv_add_one_le_ceil_inv_half {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ⌈1 / α⌉₊ + 1 ≤ ⌈1 / (α / 2)⌉₊ := by
  have hinv : 1 ≤ 1 / α := (le_div_iff₀ hα).2 (by linarith)
  have hle : 1 / α + 1 ≤ 1 / (α / 2) := by
    have hαne : α ≠ 0 := ne_of_gt hα
    field_simp
    linarith
  simpa only [Nat.ceil_add_one (one_div_nonneg.mpr hα.le)] using Nat.ceil_mono hle

/-- A displaced good ball gives the Lemma 10.1 crossing bound when the
componentwise mass estimate holds away from the pole. -/
theorem encard_crossingComponents_of_nearby_harnack_away_from_pole
    (μ : Measure ℂ) (Λ : Set ℂ) (hΛ : IsOpen Λ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (w x₀ z : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hnear : dist w x₀ < ρ / 6)
    (hAfin : μ (annulus x₀ (ρ / 2) ρ) ≠ ∞)
    (hcomponent : ∀ C ∈ connectedComponentsIn (Λ ∩ ball x₀ ρ), z ∉ C →
      μ (C ∩ annulus x₀ (ρ / 2) ρ) ≤
        ENNReal.ofReal α * μ (annulus x₀ (ρ / 2) ρ) →
      C ∩ closedBall x₀ (ρ / 2) = ∅) :
    (crossingComponents (Λ ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤
      ⌈1 / (α / 2)⌉₊ := by
  have hcount := encard_crossingComponents_of_local_mass_away_from_pole μ Λ
    (annulus x₀ (ρ / 2) ρ) hΛ
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet hAfin hα
    w x₀ z (ρ / 3) (2 * ρ) (ρ / 2) ρ (by linarith) (by
      intro x hx
      have hxw : dist x w = ρ / 3 := mem_sphere.mp hx
      have htriangle := dist_triangle x w x₀
      apply mem_ball.mpr
      linarith) (by
      intro x hx
      have hxx₀ : dist x x₀ < ρ := mem_ball.mp hx
      have htriangle := dist_triangle x x₀ w
      have hnear' : dist x₀ w < ρ / 6 := by simpa [dist_comm] using hnear
      apply mem_ball.mpr
      linarith) hcomponent
  exact hcount.trans (by exact_mod_cast ceil_inv_add_one_le_ceil_inv_half hα hα1)

end HarmonicBalls
