import HarmonicBalls.Steps.Sec11.InternalMetricExhaustion

/-!
# Punctured internal distances as a limit over an exhaustion (write-up Step 3.4, display (7))

FIRST-PASS NEW (deterministic metric geometry, no external input), fp-S11m, owner z4.
Source: `notes/fp-gaps/CHATGPT-11-12-11-13-fixes.md` lines 286-317 (Step 3.4, display (7)): for an open `O ⊆ B_7`, the
punctured internal distance `D(x, y; O \ {0})` is the decreasing limit of the internal distances in the punctured shells
`O ∩ V_n`, where `V_n = B_{7 - 1/(n+1)} \ closedBall 0 (1/(n+1))` is an increasing open exhaustion of `B_7 \ {0}`.
The limit is an infimum over `n`, by monotonicity of the internal metric in its domain.
-/

namespace HarmonicBalls.S11m

open Set Metric

/-- The punctured shell `V_n = B_{7 - 1/(n+1)} \ closedBall 0 (1/(n+1))` of the exhaustion (write-up Step 3.2). -/
def puncturedShell (n : ℕ) : Set ℂ :=
  ball (0 : ℂ) (7 - 1 / ((n : ℝ) + 1)) \ closedBall (0 : ℂ) (1 / ((n : ℝ) + 1))

theorem isOpen_puncturedShell (n : ℕ) : IsOpen (puncturedShell n) :=
  isOpen_ball.sdiff isClosed_closedBall

theorem puncturedShell_monotone : Monotone puncturedShell := by
  intro n m hnm z hz
  have hle : (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  simp only [puncturedShell, mem_sdiff, mem_ball, mem_closedBall, dist_zero_right, not_le] at hz ⊢
  constructor
  · linarith [hz.1]
  · linarith [hz.2]

theorem iUnion_puncturedShell : ⋃ n, puncturedShell n = {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 7} := by
  ext z
  simp only [mem_iUnion, mem_ofPred_eq, puncturedShell, mem_sdiff, mem_ball, mem_closedBall, dist_zero_right, not_le]
  constructor
  · rintro ⟨n, h1, h2⟩
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact ⟨lt_trans hpos h2, by linarith [h1]⟩
  · rintro ⟨h0, h7⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min h0 (show (0 : ℝ) < 7 - ‖z‖ by linarith))
    refine ⟨n, ?_, ?_⟩
    · linarith [min_le_right ‖z‖ (7 - ‖z‖)]
    · linarith [min_le_left ‖z‖ (7 - ‖z‖)]

/-- Display (7): for an open set `O ⊆ B_7`, the punctured internal distance is the infimum over the punctured shells
`O ∩ V_n` of the internal distances (write-up Step 3.4). -/
theorem internalMetric_sdiff_zero_eq_iInf_shell (D : ℂ → ℂ → ℝ) {O : Set ℂ} (hO : IsOpen O)
    (hOB : O ⊆ ball (0 : ℂ) 7) (x y : ℂ) :
    internalMetric D (O \ {0}) x y = ⨅ n : ℕ, internalMetric D (O ∩ puncturedShell n) x y := by
  have hset : O \ {0} = ⋃ n, O ∩ puncturedShell n := by
    rw [← inter_iUnion, iUnion_puncturedShell]
    ext z
    constructor
    · rintro ⟨hzO, hz0⟩
      have hz7 : ‖z‖ < 7 := by
        have := hOB hzO
        rwa [mem_ball, dist_zero_right] at this
      exact ⟨hzO, norm_pos_iff.2 hz0, hz7⟩
    · rintro ⟨hzO, h0, _⟩
      refine ⟨hzO, ?_⟩
      intro h
      rw [mem_singleton_iff.mp h, norm_zero] at h0
      exact lt_irrefl 0 h0
  rw [hset, internalMetric_iUnion_of_monotone_isOpen D
    (fun n => O ∩ puncturedShell n) (fun n => hO.inter (isOpen_puncturedShell n))
    (fun a b hab => inter_subset_inter_right O (puncturedShell_monotone hab)) x y]

end HarmonicBalls.S11m

#print axioms HarmonicBalls.S11m.internalMetric_sdiff_zero_eq_iInf_shell
