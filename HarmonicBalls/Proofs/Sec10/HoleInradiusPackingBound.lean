import HarmonicBalls.Proofs.Sec10.LateTimeHoles
import HarmonicBalls.Proofs.Sec10.ComplementaryHolePacking

/-! # Quantitative packing of bounded holes

Euclidean area bounds the number of complementary components that each
contain a ball of a prescribed radius. The estimate applies to every cluster
contained in the unit disc, without probabilistic assumptions.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Topology
open scoped ENNReal

/-- For a closed set in the closed unit disc, `n` bounded complementary
components each containing an `r`-ball satisfy `n * r² ≤ 1`. -/
theorem bounded_complement_components_inradius_packing
    {K : Set ℂ} (hKclosed : IsClosed K) (hK : K ⊆ closedBall 0 1)
    {r : ℝ} (hr : 0 < r) (F : Finset (Set ℂ))
    (hF : ∀ U ∈ F, U ∈ connectedComponentsIn Kᶜ ∧ Bornology.IsBounded U ∧
      ∃ p : ℂ, ball p r ⊆ U) :
    (F.card : ℝ) * r ^ 2 ≤ 1 := by
  classical
  have hsub : ∀ U ∈ F, U ⊆ ball (0 : ℂ) 1 := by
    intro U hU
    exact bounded_complement_component_subset_unit_ball hKclosed hK (hF U hU).1 (hF U hU).2.1
  have hmeas : ∀ U ∈ F, MeasurableSet U := by
    intro U hU
    obtain ⟨x, hx, rfl⟩ := (hF U hU).1
    exact hKclosed.isOpen_compl.connectedComponentIn.measurableSet
  have hdis : (↑F : Set (Set ℂ)).PairwiseDisjoint id := by
    intro U hU V hV hne
    exact connectedComponentsIn_pairwise_disjoint _ (hF U hU).1 (hF V hV).1 hne
  have hsum : (∑ U ∈ F, volume (id U)) ≤ volume (ball (0 : ℂ) 1) := by
    rw [← measure_biUnion_finset hdis hmeas]
    exact measure_mono (iUnion₂_subset hsub)
  have hfin : ∀ U ∈ F, volume U ≠ ∞ := by
    intro U hU
    exact ne_top_of_le_ne_top (show volume (ball (0 : ℂ) 1) ≠ ∞ from measure_ball_lt_top.ne)
      (measure_mono (hsub U hU))
  have hsumR : (∑ U ∈ F, (volume U).toReal) ≤ (volume (ball (0 : ℂ) 1)).toReal := by
    have h := ENNReal.toReal_mono (show volume (ball (0 : ℂ) 1) ≠ ∞ from measure_ball_lt_top.ne) hsum
    simp only [id_eq] at h
    rwa [ENNReal.toReal_sum hfin] at h
  have hlower : ∀ U ∈ F, (volume (ball (0 : ℂ) r)).toReal ≤ (volume U).toReal := by
    intro U hU
    obtain ⟨p, hp⟩ := (hF U hU).2.2
    have h := ENNReal.toReal_mono (hfin U hU) (measure_mono (μ := volume) hp)
    simpa only [Complex.volume_ball] using h
  have hsumlower := Finset.sum_le_sum hlower
  simp only [Finset.sum_const, nsmul_eq_mul] at hsumlower
  have hv1 : (volume (ball (0 : ℂ) 1)).toReal = Real.pi := by
    simp [Complex.volume_ball]
  have hvr : (volume (ball (0 : ℂ) r)).toReal = r ^ 2 * Real.pi := by
    simp [Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr.le]
  have hprod : ((F.card : ℝ) * r ^ 2) * Real.pi ≤ 1 * Real.pi := by
    rw [hv1] at hsumR
    rw [hvr] at hsumlower
    nlinarith
  exact le_of_mul_le_mul_right hprod Real.pi_pos

/-- The packing bound holds for every unit-disc cluster, every pole and time,
without any condition on its measure. -/
theorem cluster_bounded_holes_inradius_packing
    (μ : Measure ℂ) (z : ℂ) (t : ℝ) {r : ℝ} (hr : 0 < r)
    (F : Finset (Set ℂ))
    (hF : ∀ U ∈ F, U ∈ connectedComponentsIn (closure (cluster μ 1 z t))ᶜ ∧
      Bornology.IsBounded U ∧ ∃ p : ℂ, ball p r ⊆ U) :
    (F.card : ℝ) * r ^ 2 ≤ 1 := by
  apply bounded_complement_components_inradius_packing isClosed_closure
    (closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall)
    hr F hF

/-- Two distinct bounded holes cannot both contain a ball whose squared
radius exceeds one half. -/
theorem cluster_at_most_one_large_hole
    (μ : Measure ℂ) (z : ℂ) (t : ℝ) {r : ℝ} (hr : 0 < r)
    (hrlarge : (1 / 2 : ℝ) < r ^ 2) (F : Finset (Set ℂ))
    (hF : ∀ U ∈ F, U ∈ connectedComponentsIn (closure (cluster μ 1 z t))ᶜ ∧
      Bornology.IsBounded U ∧ ∃ p : ℂ, ball p r ⊆ U) : F.card ≤ 1 := by
  have hbound := cluster_bounded_holes_inradius_packing μ z t hr F hF
  by_contra hn
  have hc : (2 : ℝ) ≤ F.card := by exact_mod_cast (show 2 ≤ F.card by omega)
  nlinarith

end HarmonicBalls
