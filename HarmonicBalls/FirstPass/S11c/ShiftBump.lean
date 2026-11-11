import HarmonicBalls.FirstPass.S11d.SmoothCutoff

/-!
# Proposition 11.10, smooth bumps equal to one on a compact set and zero on a closed set

This is the cutoff `φ` of the printed proof of `lemma:mass-diam` (paper lines 3071-3090):
a smooth compactly supported bump with values in `[0,1]`, identically one on the exterior set `G` and identically zero on
the unit circle and on the chosen small squares. The shift `h̃ := h + a φ` with `a ≤ 0` is smooth with compact support,
takes values in `[a, 0]`, and is zero on the closed set `F`; it is the input of `CameronMartinEventTransferFrozen`.
-/

open Set Metric

namespace HarmonicBalls

/-- A smooth bump with values in `[0,1]`, identically one on a compact set `K` and identically zero on a closed set `F`
disjoint from `K`. -/
theorem exists_bump_one_zero {K F : Set ℂ} (hK : IsCompact K) (hF : IsClosed F) (hKF : Disjoint K F) :
    ∃ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ (∀ z ∈ F, φ z = 0) ∧
      (∀ z ∈ K, φ z = 1) ∧ ∀ z, 0 ≤ φ z ∧ φ z ≤ 1 := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  set U : Set ℂ := ball (0 : ℂ) (R + 1) \ F with hU
  have hUo : IsOpen U := isOpen_ball.sdiff hF
  have hKU : K ⊆ U := by
    intro z hz
    refine ⟨?_, fun h => Set.disjoint_left.1 hKF hz h⟩
    have hzR := hR hz
    rw [mem_closedBall, dist_zero_right] at hzR
    rw [mem_ball, dist_zero_right]
    linarith
  have hUb : Bornology.IsBounded U := isBounded_ball.subset sdiff_subset
  obtain ⟨φ, hφs, hφc, htsub, hrange, hφ1⟩ := exists_smooth_cutoff hK hUo hKU hUb
  refine ⟨φ, hφs, hφc, ?_, hφ1, hrange⟩
  intro z hz
  have hzt : z ∉ tsupport φ := fun h => (htsub h).2 hz
  exact image_eq_zero_of_notMem_tsupport hzt

/-- A smooth compactly supported shift, equal to the constant `a ≤ 0` on a compact set `K` and to zero on a closed set `F`
disjoint from `K`, with values in `[a, 0]`. -/
theorem exists_shift_const_on_zero {K F : Set ℂ} (hK : IsCompact K) (hF : IsClosed F) (hKF : Disjoint K F)
    {a : ℝ} (ha : a ≤ 0) :
    ∃ f : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ (∀ z ∈ F, f z = 0) ∧
      (∀ z ∈ K, f z = a) ∧ ∀ z, a ≤ f z ∧ f z ≤ 0 := by
  obtain ⟨φ, hφs, hφc, hφF, hφK, hφr⟩ := exists_bump_one_zero hK hF hKF
  refine ⟨fun z => a * φ z, contDiff_const.mul hφs, hφc.mul_left, ?_, ?_, ?_⟩
  · intro z hz
    simp [hφF z hz]
  · intro z hz
    simp [hφK z hz]
  · intro z
    obtain ⟨h0, h1⟩ := hφr z
    constructor
    · nlinarith
    · nlinarith

end HarmonicBalls
