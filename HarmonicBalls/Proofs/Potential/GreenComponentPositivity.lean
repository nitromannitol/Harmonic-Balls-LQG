import HarmonicBalls.Proofs.Potential.GreenPositivity
import HarmonicBalls.Proofs.Potential.FiniteDiscGreenReciprocity
import HarmonicBalls.Proofs.Sec6.GeneralDomainStopped
import HarmonicBalls.Proofs.Sec6.PlanarHarnack
import HarmonicBalls.Proofs.Sec5.GreenConnectedComponent

/-! # Strict positivity of the Green function on a component

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open Set Metric Filter InnerProductSpace
open scoped Topology

/-- A bounded open planar Green function is positive at distinct points in
its pole's connected component. The diagonal value is zero by convention. -/
theorem greenFunction_pos_of_mem_connectedComponentIn
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {z x : ℂ} (hz : z ∈ U) (hx : x ∈ connectedComponentIn U z)
    (hxz : x ≠ z) : 0 < greenFunction U z x := by
  classical
  let A : Set ℂ := U ∩ ({z} ∪ {y | 0 < greenFunction U z y})
  let B : Set ℂ := {y | y ∈ U ∧ y ≠ z ∧ greenFunction U z y = 0}
  have hh := Section6.harmonicOnNhd_greenFunction_right hU hUb hz
  have hA : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    rcases hy.2 with hyz | hypos
    · have hyz : y = z := by simpa using hyz
      subst y
      obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU z hz
      have hclosed : closedBall z (δ / 2) ⊆ U :=
        (closedBall_subset_ball (half_lt_self hδ)).trans hδU
      have hball : ball z (δ / 2) ⊆ A := by
        intro w hw
        refine ⟨hδU (ball_subset_ball (half_le_self hδ.le) hw), ?_⟩
        by_cases hwz : w = z
        · left; simpa using hwz
        · right
          change 0 < greenFunction U z w
          rw [greenFunction_bounded_open_comm hU hUb z w]
          apply greenFunction_pos hUb (half_pos hδ) hclosed
          · exact norm_pos_iff.mpr (sub_ne_zero.mpr hwz)
          · simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hw
      exact Filter.mem_of_superset (ball_mem_nhds z (half_pos hδ)) hball
    · change 0 < greenFunction U z y at hypos
      have hyne : y ≠ z := by
        intro heq
        subst y
        simp only [greenFunction_self, lt_self_iff_false] at hypos
      have hc := (hh y ⟨hy.1, by simpa using hyne⟩).1.continuousAt
      have hp : ∀ᶠ w in 𝓝 y, 0 < greenFunction U z w :=
        hc.eventually (Ioi_mem_nhds hypos)
      filter_upwards [hU.mem_nhds hy.1, hp] with w hw hpw
      exact ⟨hw, Or.inr hpw⟩
  have hB : IsOpen B := by
    rw [Metric.isOpen_iff]
    intro y hy
    have hy' : y ∈ U \ {z} := ⟨hy.1, by simpa using hy.2.1⟩
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp (hU.sdiff isClosed_singleton) y hy'
    have hclosed : closedBall y (δ / 2) ⊆ U \ {z} :=
      (closedBall_subset_ball (half_lt_self hδ)).trans hδU
    refine ⟨δ / 4, by positivity, ?_⟩
    intro w hw
    have heq : δ / 2 / 2 = δ / 4 := by ring
    have hwclosed : w ∈ closedBall y ((δ / 2) / 2) := by
      rw [heq]
      exact ball_subset_closedBall hw
    have hwU := hδU (ball_subset_ball (by linarith) hw)
    refine ⟨hwU.1, by simpa using hwU.2, ?_⟩
    have hle := Section6.harmonic_le_four_mul_center (half_pos hδ) (hh.mono hclosed)
      (fun w _ => greenFunction_nonneg hUb z w) hwclosed
    rw [hy.2.2, mul_zero] at hle
    exact le_antisymm hle (greenFunction_nonneg hUb z w)
  have hdis : Disjoint A B := by
    refine disjoint_left.mpr ?_
    intro y hyA hyB
    rcases hyA.2 with heq | hp
    · exact hyB.2.1 (by simpa using heq)
    · change 0 < greenFunction U z y at hp
      rw [hyB.2.2] at hp
      exact (lt_irrefl 0) hp
  have hcover : connectedComponentIn U z ⊆ A ∪ B := by
    intro y hy
    have hyU := connectedComponentIn_subset U z hy
    by_cases hyz : y = z
    · exact Or.inl ⟨hyU, Or.inl (by simpa using hyz)⟩
    · rcases (greenFunction_nonneg hUb z y).eq_or_lt with heq | hp
      · exact Or.inr ⟨hyU, hyz, heq.symm⟩
      · exact Or.inl ⟨hyU, Or.inr hp⟩
  have hne : (connectedComponentIn U z ∩ A).Nonempty :=
    ⟨z, mem_connectedComponentIn hz, hz, Or.inl (by simp)⟩
  have hsub := isPreconnected_connectedComponentIn.subset_left_of_subset_union
    hA hB hdis hcover hne
  rcases (hsub hx).2 with heq | hp
  · exact (hxz (by simpa using heq)).elim
  · exact hp

/-- Positivity characterizes distinct points in the pole's component. In
particular, the prescribed diagonal and exterior values are zero. -/
theorem greenFunction_pos_iff_mem_connectedComponentIn
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (z x : ℂ) :
    0 < greenFunction U z x ↔
      z ∈ U ∧ x ∈ connectedComponentIn U z ∧ x ≠ z := by
  constructor
  · intro hp
    have hz : z ∈ U := by
      by_contra hz
      rw [greenFunction_of_notMem_left hz x] at hp
      exact (lt_irrefl 0) hp
    have hx : x ∈ connectedComponentIn U z := by
      by_contra hx
      rw [greenFunction_eq_zero_of_not_mem_connectedComponentIn hU hUb hz hx] at hp
      exact (lt_irrefl 0) hp
    have hxz : x ≠ z := by
      intro heq
      subst x
      rw [greenFunction_self] at hp
      exact (lt_irrefl 0) hp
    exact ⟨hz, hx, hxz⟩
  · rintro ⟨hz, hx, hxz⟩
    exact greenFunction_pos_of_mem_connectedComponentIn hU hUb hz hx hxz

/-- The Green kernel vanishes exactly at exterior poles, outside the pole's
component, or on the diagonal. -/
theorem greenFunction_eq_zero_iff_not_mem_component_or_eq
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (z x : ℂ) :
    greenFunction U z x = 0 ↔
      z ∉ U ∨ x ∉ connectedComponentIn U z ∨ x = z := by
  have heq : greenFunction U z x = 0 ↔ ¬ 0 < greenFunction U z x := by
    constructor
    · intro h; rw [h]; exact lt_irrefl 0
    · intro h; exact le_antisymm (le_of_not_gt h) (greenFunction_nonneg hUb z x)
  rw [heq, greenFunction_pos_iff_mem_connectedComponentIn hU hUb z x]
  classical
  tauto

#print axioms greenFunction_pos_of_mem_connectedComponentIn
#print axioms greenFunction_pos_iff_mem_connectedComponentIn
#print axioms greenFunction_eq_zero_iff_not_mem_component_or_eq

end HarmonicBalls
