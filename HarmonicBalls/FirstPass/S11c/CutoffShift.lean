import HarmonicBalls.FirstPass.S11d.SmoothCutoff

/-!
# Proposition 11.10, smooth shifts constant on a square

For a compact set `S` disjoint from the unit circle and a real `a`, there is a smooth,
compactly supported function `f` with `f = a` on `S` and `f = 0` on the unit circle (the admissible shifts of the
Cameron-Martin transfer, `CameronMartinEventTransferFrozen`, Frozen/S11c.lean). This is the bump `φ₁` of the paper's proof of
`lemma:mass-diam` (corrected line 3050: `φ ≡ 1` on `S₁`, `φ ≡ 0` near the unit circle) times the constant `a`, built from
the repo's smooth cutoff `exists_smooth_cutoff` (FirstPass/S11d/SmoothCutoff.lean).
-/

namespace HarmonicBalls

open Set Metric Filter Topology

theorem exists_const_shift_on {S : Set ℂ} (hS : IsCompact S) (hSd : Disjoint S (sphere (0 : ℂ) 1)) (a : ℝ) :
    ∃ f : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ (∀ z : ℂ, ‖z‖ = 1 → f z = 0) ∧
      ∀ z ∈ S, f z = a := by
  obtain ⟨R, hR⟩ := hS.isBounded.subset_closedBall (0 : ℂ)
  set U : Set ℂ := ball (0 : ℂ) (R + 1) ∩ (sphere (0 : ℂ) 1)ᶜ with hU
  have hUo : IsOpen U := isOpen_ball.inter isClosed_sphere.isOpen_compl
  have hSU : S ⊆ U := by
    intro z hz
    refine ⟨?_, ?_⟩
    · have := hR hz
      rw [mem_closedBall, dist_zero_right] at this
      rw [mem_ball, dist_zero_right]
      linarith
    · exact fun h => Set.disjoint_left.1 hSd hz h
  have hUb : Bornology.IsBounded U := isBounded_ball.subset inter_subset_left
  obtain ⟨φ, hφs, hφc, htsub, -, hφ1⟩ := exists_smooth_cutoff hS hUo hSU hUb
  refine ⟨fun z => a * φ z, contDiff_const.mul hφs, hφc.mul_left, ?_, ?_⟩
  · intro z hz
    have hzt : z ∉ tsupport φ := by
      intro h
      have := htsub h
      exact this.2 (by simp [mem_sphere_iff_norm, hz])
    simp [image_eq_zero_of_notMem_tsupport hzt]
  · intro z hz
    simp [hφ1 z hz]

end HarmonicBalls
