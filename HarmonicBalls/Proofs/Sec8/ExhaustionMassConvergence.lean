import HarmonicBalls.Proofs.Sec8.CenteredLQGApproximation

/-! # Normalized masses along an interior exhaustion -/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace HarmonicBalls

/-- If the masses of an increasing exhaustion and of its union converge for
each fixed set, then the mass of the moving exhaustion also converges. -/
theorem tendsto_measure_exhaustion {X : Type*} [MeasurableSpace X]
    (ν : ℕ → Measure X) (μ : Measure X) (E : ℕ → Set X)
    (hmono : Monotone E)
    (hfixed : ∀ k, Tendsto (fun n => ν n (E k)) atTop (𝓝 (μ (E k))))
    (hunion : Tendsto (fun n => ν n (⋃ k, E k)) atTop (𝓝 (μ (⋃ k, E k)))) :
    Tendsto (fun n => ν n (E n)) atTop (𝓝 (μ (⋃ k, E k))) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    have ha' : a < ⨆ k, μ (E k) := by
      simpa only [hmono.measure_iUnion] using ha
    obtain ⟨k, hk⟩ := lt_iSup_iff.mp ha'
    filter_upwards [(tendsto_order.1 (hfixed k)).1 a hk, eventually_ge_atTop k] with n hn hkn
    exact hn.trans_le (measure_mono (hmono hkn))
  · intro b hb
    filter_upwards [(tendsto_order.1 hunion).2 b hb] with n hn
    exact (measure_mono (subset_iUnion E n)).trans_lt hn

/-- Along an increasing exhaustion, convergence of the fixed-set masses
implies convergence of the normalized masses, provided the limiting mass of
the reference set is positive and finite. -/
theorem tendsto_normalizedRestriction_exhaustion {X : Type*} [MeasurableSpace X]
    (ν : ℕ → Measure X) (μ : Measure X) (E : ℕ → Set X)
    (hmono : Monotone E) (A : Set X)
    (hzero : μ (⋃ k, E k) ≠ 0) (htop : μ (⋃ k, E k) ≠ ∞)
    (hfixed : ∀ k, Tendsto (fun n => ν n (E k)) atTop (𝓝 (μ (E k))))
    (hfixedA : ∀ k, Tendsto (fun n => ν n (A ∩ E k)) atTop (𝓝 (μ (A ∩ E k))))
    (hunion : Tendsto (fun n => ν n (⋃ k, E k)) atTop (𝓝 (μ (⋃ k, E k))))
    (hunionA : Tendsto (fun n => ν n (A ∩ ⋃ k, E k)) atTop
      (𝓝 (μ (A ∩ ⋃ k, E k)))) :
    Tendsto (fun n => (ν n (E n))⁻¹ * ν n (A ∩ E n)) atTop
      (𝓝 ((μ (⋃ k, E k))⁻¹ * μ (A ∩ ⋃ k, E k))) := by
  have hmass := tendsto_measure_exhaustion ν μ E hmono hfixed hunion
  have hAmono : Monotone (fun n => A ∩ E n) := fun _ _ h => inter_subset_inter_right A (hmono h)
  have hAmass := tendsto_measure_exhaustion ν μ (fun n => A ∩ E n) hAmono hfixedA (by
    simpa only [← inter_iUnion] using hunionA)
  rw [← inter_iUnion] at hAmass
  have hdiv := ENNReal.Tendsto.div hAmass (Or.inr hzero) hmass (Or.inl htop)
  simpa only [ENNReal.div_eq_inv_mul] using hdiv

end HarmonicBalls
