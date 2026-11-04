import HarmonicBalls.Proofs.Sec6.PlanarHarnack

/-! # Harnack chains in the plane

Iterating the local Poisson-kernel estimate compares a nonnegative harmonic
function along any finite chain of discs inside its domain.
-/

namespace HarmonicBalls.Section6

open Metric Set InnerProductSpace

/-- A chain of `n` half-disc steps gives a Harnack constant `4 ^ n`. -/
theorem harmonic_le_of_harnack_chain {U : Set ℂ} {f : ℂ → ℝ}
    (hf : HarmonicOnNhd f U) (hnonneg : ∀ z ∈ U, 0 ≤ f z)
    {r : ℝ} (hr : 0 < r) (p : ℕ → ℂ) (n : ℕ)
    (hdisc : ∀ i < n, closedBall (p i) r ⊆ U)
    (hstep : ∀ i < n, p (i + 1) ∈ closedBall (p i) (r / 2)) :
    f (p n) ≤ (4 : ℝ) ^ n * f (p 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : f (p n) ≤ (4 : ℝ) ^ n * f (p 0) :=
      ih (fun i hi => hdisc i (Nat.lt_succ_of_lt hi))
        (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    have hlocal := harmonic_le_four_mul_center hr (hf.mono (hdisc n (Nat.lt_succ_self n)))
      (fun z hz => hnonneg z (hdisc n (Nat.lt_succ_self n) (sphere_subset_closedBall hz)))
      (hstep n (Nat.lt_succ_self n))
    calc
      f (p (n + 1)) ≤ 4 * f (p n) := hlocal
      _ ≤ 4 * ((4 : ℝ) ^ n * f (p 0)) := mul_le_mul_of_nonneg_left hn (by norm_num)
      _ = (4 : ℝ) ^ (n + 1) * f (p 0) := by rw [pow_succ]; ring

/-- An odometer vanishing at the start of a Harnack chain is bounded at the
end by the annular Green potential, with the chain constant. -/
theorem odometer_le_annulusGreenPotentialSup_of_harnack_chain
    {μ : MeasureTheory.Measure ℂ} (hμ : MeasureTheory.IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {c : ℂ} {a b : ℝ} (hab : a < b) (hb : 0 < b)
    (hA : annulus c a b ⊆ ball (0 : ℂ) R \ {z})
    {r : ℝ} (hr : 0 < r) (p : ℕ → ℂ) (n : ℕ)
    (hp0 : p 0 ∈ annulus c a b)
    (hzero : odometer μ R z t (p 0) = 0)
    (hdisc : ∀ i < n, closedBall (p i) r ⊆ annulus c a b)
    (hstep : ∀ i < n, p (i + 1) ∈ closedBall (p i) (r / 2)) :
    ENNReal.ofReal (odometer μ R z t (p n)) ≤
      ENNReal.ofReal ((4 : ℝ) ^ n) * annulusGreenPotentialSup μ c a b := by
  obtain ⟨q, _, hq0, hqbound, hsum0, hharm⟩ :=
    exists_annulus_odometer_classical_harmonic_correction hμ hR hV hz ht hab hb hA
  have hchain := harmonic_le_of_harnack_chain hharm hsum0 hr p n hdisc hstep
  have hle : odometer μ R z t (p n) ≤ (4 : ℝ) ^ n * q (p 0) := by
    rw [hzero, zero_add] at hchain
    have hq := hq0 (p n)
    linarith
  calc
    ENNReal.ofReal (odometer μ R z t (p n)) ≤
        ENNReal.ofReal ((4 : ℝ) ^ n * q (p 0)) := ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal ((4 : ℝ) ^ n) * ENNReal.ofReal (q (p 0)) :=
      ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal ((4 : ℝ) ^ n) * annulusGreenPotentialSup μ c a b :=
      by simpa only [mul_comm] using
        (mul_le_mul_left (hqbound (p 0) hp0) (ENNReal.ofReal ((4 : ℝ) ^ n)))

/-- Outside the cluster, the odometer vanishes at every point of the
annulus away from its pole. -/
theorem odometer_eq_zero_of_not_mem_cluster_in_annulus
    {μ : MeasureTheory.Measure ℂ} {R t a b : ℝ} {z c x : ℂ}
    (ht : 0 < t) (hA : annulus c a b ⊆ ball (0 : ℂ) R \ {z})
    (hx : x ∈ annulus c a b) (hnot : x ∉ cluster μ R z t) :
    odometer μ R z t x = 0 := by
  have hx' := hA hx
  have hxz : x ≠ z := by simpa using hx'.2
  have hnonneg := odometer_nonneg (μ := μ) ht.le (ball_subset_closedBall hx'.1) hxz
  apply le_antisymm _ hnonneg
  apply le_of_not_gt
  intro hpos
  apply hnot
  exact mem_cluster_iff.mpr ⟨hx'.1, Or.inr hpos⟩

/-- The odometer estimate on any set reached by uniformly bounded Harnack
chains from a point outside the cluster. -/
theorem odometer_iSup_le_annulusGreenPotentialSup_of_harnack_chains
    {μ : MeasureTheory.Measure ℂ} (hμ : MeasureTheory.IsLocallyFiniteMeasure μ)
    {R βminus βplus : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {c : ℂ} {a b : ℝ} (hab : a < b) (hb : 0 < b)
    (hA : annulus c a b ⊆ ball (0 : ℂ) R \ {z})
    {y : ℂ} (hy : y ∈ annulus c a b) (hnot : y ∉ cluster μ R z t)
    {K : Set ℂ} {r : ℝ} (hr : 0 < r) (N : ℕ)
    (hchains : ∀ x ∈ K, ∃ p : ℕ → ℂ,
      p 0 = y ∧ p N = x ∧
      (∀ i < N, closedBall (p i) r ⊆ annulus c a b) ∧
      (∀ i < N, p (i + 1) ∈ closedBall (p i) (r / 2))) :
    ⨆ x ∈ K, ENNReal.ofReal (odometer μ R z t x) ≤
      ENNReal.ofReal ((4 : ℝ) ^ N) * annulusGreenPotentialSup μ c a b := by
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  obtain ⟨p, hp0, hpN, hdisc, hstep⟩ := hchains x hx
  have hzero := odometer_eq_zero_of_not_mem_cluster_in_annulus ht hA hy hnot
  have hbnd := odometer_le_annulusGreenPotentialSup_of_harnack_chain
    hμ hR hV hz ht hab hb hA hr p N (by simpa [hp0] using hy)
    (by simpa [hp0] using hzero) hdisc hstep
  simpa [hpN] using hbnd

end HarmonicBalls.Section6
