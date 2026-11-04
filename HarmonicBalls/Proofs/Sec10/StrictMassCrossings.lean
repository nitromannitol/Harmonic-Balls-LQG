import HarmonicBalls.Proofs.Sec10.PoleExceptionalCrossings

/-!
# Strict mass bounds and one exceptional component

Strict mass inequalities leave room for one exceptional component in the
same ceiling bound. The local estimate away from the pole is still an
explicit hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Topology
open scoped BigOperators ENNReal

/-- A finite disjoint family with strict mass lower bounds has strictly
fewer than `1 / α` members. -/
theorem card_lt_inv_of_disjoint_mass
    {X ι : Type*} [MeasurableSpace X] (μ : Measure X) (A : Set X)
    (hApos : μ A ≠ 0) (hAfin : μ A ≠ ∞) {α : ℝ} (hα : 0 < α)
    (s : Finset ι) (F : ι → Set X)
    (hFmeas : ∀ i ∈ s, MeasurableSet (F i))
    (hFsub : ∀ i ∈ s, F i ⊆ A)
    (hFdisj : Set.PairwiseDisjoint (↑s : Set ι) F)
    (hFmass : ∀ i ∈ s, ENNReal.ofReal α * μ A < μ (F i)) :
    (s.card : ℝ) < 1 / α := by
  classical
  by_cases hs : s.Nonempty
  · have hsum : (∑ i ∈ s, μ (F i)) ≤ μ A := by
      rw [← measure_biUnion_finset hFdisj hFmeas]
      exact measure_mono (iUnion₂_subset hFsub)
    have hFi : ∀ i ∈ s, μ (F i) ≠ ∞ := by
      intro i hi
      exact ne_top_of_le_ne_top hAfin (measure_mono (hFsub i hi))
    have hsumR : (∑ i ∈ s, (μ (F i)).toReal) ≤ (μ A).toReal := by
      have := ENNReal.toReal_mono hAfin hsum
      rwa [ENNReal.toReal_sum hFi] at this
    have hbound : ∀ i ∈ s, α * (μ A).toReal < (μ (F i)).toReal := by
      intro i hi
      have := (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin)
        (hFi i hi)).2 (hFmass i hi)
      simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hα.le] using this
    have hsumlower : (∑ _i ∈ s, α * (μ A).toReal) <
        ∑ i ∈ s, (μ (F i)).toReal := by
      exact Finset.sum_lt_sum_of_nonempty hs hbound
    simp only [Finset.sum_const, nsmul_eq_mul] at hsumlower
    have hpos : 0 < (μ A).toReal := ENNReal.toReal_pos hApos hAfin
    apply (lt_div_iff₀ hα).2
    nlinarith
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [hempty, Finset.card_empty, Nat.cast_zero]
    exact one_div_pos.mpr hα

/-- If at most one member is exceptional, the strict lower bounds for the
others still give the ceiling bound. -/
theorem encard_le_ceil_inv_of_one_exception
    {X ι : Type*} [MeasurableSpace X] (μ : Measure X) (A : Set X)
    (hApos : μ A ≠ 0) (hAfin : μ A ≠ ∞) {α : ℝ} (hα : 0 < α)
    (S : Set ι) (F : ι → Set X) (i₀ : ι)
    (hFmeas : ∀ i ∈ S, MeasurableSet (F i))
    (hFsub : ∀ i ∈ S, F i ⊆ A)
    (hFdisj : Set.PairwiseDisjoint S F)
    (hFmass : ∀ i ∈ S, i ≠ i₀ → ENNReal.ofReal α * μ A < μ (F i)) :
    S.encard ≤ ⌈1 / α⌉₊ := by
  classical
  let T := S \ {i₀}
  have hTle : T.encard ≤ ⌈1 / α⌉₊ := by
    apply encard_le_ceil_inv_of_disjoint_mass μ A hApos hAfin hα T F
    · exact fun i hi => hFmeas i hi.1
    · exact fun i hi => hFsub i hi.1
    · exact fun i hi j hj hij => hFdisj hi.1 hj.1 hij
    · exact fun i hi => (hFmass i hi.1 (by simpa using hi.2)).le
  have hTfin : T.Finite := Set.encard_lt_top_iff.mp (hTle.trans_lt (ENat.natCast_lt_top _))
  have hTlt : hTfin.toFinset.card < ⌈1 / α⌉₊ := by
    apply Nat.lt_ceil.mpr
    apply card_lt_inv_of_disjoint_mass μ A hApos hAfin hα hTfin.toFinset F
    · intro i hi
      exact hFmeas i ((hTfin.mem_toFinset.mp hi).1)
    · intro i hi
      exact hFsub i ((hTfin.mem_toFinset.mp hi).1)
    · intro i hi j hj hij
      exact hFdisj ((hTfin.mem_toFinset.mp hi).1) ((hTfin.mem_toFinset.mp hj).1) hij
    · intro i hi
      have hi' := hTfin.mem_toFinset.mp hi
      exact hFmass i hi'.1 (by simpa using hi'.2)
  have hle := encard_le_encard_sdiff_add_encard S ({i₀} : Set ι)
  have hnat : hTfin.toFinset.card + 1 ≤ ⌈1 / α⌉₊ := hTlt
  have hbound : T.encard + 1 ≤ (⌈1 / α⌉₊ : ℕ∞) := by
    rw [hTfin.encard_eq_coe_toFinset_card]
    exact_mod_cast hnat
  exact hle.trans (by simpa only [encard_singleton] using hbound)

/-- One exceptional crossing component fits in the same ceiling bound. -/
theorem encard_crossingComponents_le_ceil_inv_of_one_exception
    (μ : Measure ℂ) (Λ A : Set ℂ) (hΛ : IsOpen Λ) (hA : MeasurableSet A)
    (hAfin : μ A ≠ ∞) {α : ℝ} (hα : 0 < α) (w : ℂ) (r s : ℝ)
    (C₀ : Set ℂ)
    (hmass : ∀ C ∈ crossingComponents (Λ ∩ ball w s) w r s, C ≠ C₀ →
      ENNReal.ofReal α * μ A < μ (C ∩ A)) :
    (crossingComponents (Λ ∩ ball w s) w r s).encard ≤ ⌈1 / α⌉₊ := by
  classical
  let S := crossingComponents (Λ ∩ ball w s) w r s
  by_cases hzero : μ A = 0
  · have hsub : S ⊆ {C₀} := by
      intro C hC
      by_contra hne
      have hlt := hmass C hC (by simpa using hne)
      have hle : μ (C ∩ A) ≤ μ A := measure_mono inter_subset_right
      rw [hzero] at hlt hle
      simp only [mul_zero] at hlt
      exact (not_lt_of_ge hle) hlt
    have hceil : (1 : ℕ) ≤ ⌈1 / α⌉₊ := Nat.ceil_pos.mpr (one_div_pos.mpr hα)
    calc
      S.encard ≤ ({C₀} : Set (Set ℂ)).encard := encard_le_encard hsub
      _ = 1 := encard_singleton _
      _ ≤ ⌈1 / α⌉₊ := by exact_mod_cast hceil
  · apply encard_le_ceil_inv_of_one_exception μ A hzero hAfin hα S (fun C => C ∩ A) C₀
    · intro C hC
      obtain ⟨⟨x, hx, rfl⟩, _⟩ := hC
      exact ((hΛ.inter isOpen_ball).connectedComponentIn.measurableSet).inter hA
    · intro C hC
      exact inter_subset_right
    · intro C hC D hD hne
      have hd := pairwiseDisjoint_connectedComponentsIn (Λ ∩ ball w s) hC.1 hD.1 hne
      exact hd.mono inter_subset_left inter_subset_left
    · exact hmass

/-- A local mass estimate away from the pole bounds the large-ball crossing
count with only the pole-containing component left exceptional. -/
theorem encard_crossingComponents_of_local_mass_away_from_pole_sharp
    (μ : Measure ℂ) (Λ A : Set ℂ) (hΛ : IsOpen Λ) (hA : MeasurableSet A)
    (hAfin : μ A ≠ ∞) {α : ℝ} (hα : 0 < α)
    (w x₀ z : ℂ) (r R q ρ : ℝ) (hqr : q ≤ ρ)
    (hinner : sphere w r ⊆ ball x₀ q) (houter : ball x₀ ρ ⊆ ball w R)
    (hcomponent : ∀ D ∈ connectedComponentsIn (Λ ∩ ball x₀ ρ), z ∉ D →
      μ (D ∩ A) ≤ ENNReal.ofReal α * μ A → D ∩ closedBall x₀ q = ∅) :
    (crossingComponents (Λ ∩ ball w R) w r R).encard ≤ ⌈1 / α⌉₊ := by
  let C₀ := connectedComponentIn (Λ ∩ ball w R) z
  apply encard_crossingComponents_le_ceil_inv_of_one_exception μ Λ A hΛ hA hAfin hα w r R C₀
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

/-- A displaced good ball gives the Lemma 10.1 crossing bound when the
componentwise mass estimate holds away from the pole. -/
theorem encard_crossingComponents_of_nearby_harnack_away_from_pole_sharp
    (μ : Measure ℂ) (Λ : Set ℂ) (hΛ : IsOpen Λ)
    {α : ℝ} (hα : 0 < α) (w x₀ z : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hnear : dist w x₀ < ρ / 6)
    (hAfin : μ (annulus x₀ (ρ / 2) ρ) ≠ ∞)
    (hcomponent : ∀ C ∈ connectedComponentsIn (Λ ∩ ball x₀ ρ), z ∉ C →
      μ (C ∩ annulus x₀ (ρ / 2) ρ) ≤
        ENNReal.ofReal α * μ (annulus x₀ (ρ / 2) ρ) →
      C ∩ closedBall x₀ (ρ / 2) = ∅) :
    (crossingComponents (Λ ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤
      ⌈1 / α⌉₊ := by
  exact encard_crossingComponents_of_local_mass_away_from_pole_sharp μ Λ
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


end HarmonicBalls
