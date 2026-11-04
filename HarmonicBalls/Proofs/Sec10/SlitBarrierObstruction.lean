import HarmonicBalls.Proofs.Sec10.AnnularHoleModel
import Mathlib.Analysis.Complex.ReImTopology

/-! # Closure can create a hole

An open slit annulus gives a deterministic obstruction to constructing a
barrier solely from a bounded hole of the closure. This is not an LQG model.
-/

namespace HarmonicBalls

open Set Metric Topology

/-- A slit annulus is the exponential image of a convex rectangle. -/
theorem isPreconnected_slit_annulus {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    IsPreconnected (annulus 0 r R ∩ Complex.slitPlane) := by
  let S : Set ℂ := {w | Real.log r < w.re ∧ w.re < Real.log R ∧
    -Real.pi < w.im ∧ w.im < Real.pi}
  have hSc : Convex ℝ S :=
    (convex_halfSpace_re_gt _).inter ((convex_halfSpace_re_lt _).inter
      ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)))
  have heq : Complex.exp '' S = annulus 0 r R ∩ Complex.slitPlane := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [mem_ball, dist_zero_right, Complex.norm_exp]
        exact (Real.exp_lt_exp.mpr hw.2.1).trans_eq (Real.exp_log hR)
      · rw [mem_closedBall, dist_zero_right, Complex.norm_exp, not_le]
        exact (Real.exp_log hr).symm ▸ Real.exp_lt_exp.mpr hw.1
      · rw [Complex.exp_mem_slitPlane,
          (toIocMod_eq_self Real.two_pi_pos).2 ⟨hw.2.2.1, by
            simpa [two_mul] using hw.2.2.2.le⟩]
        exact hw.2.2.2.ne
    · rintro ⟨hzA, hzs⟩
      have hzne : z ≠ 0 := Complex.slitPlane_ne_zero hzs
      refine ⟨Complex.log z, ?_, Complex.exp_log hzne⟩
      change Real.log r < (Complex.log z).re ∧ (Complex.log z).re < Real.log R ∧
        -Real.pi < (Complex.log z).im ∧ (Complex.log z).im < Real.pi
      rw [Complex.log_re, Complex.log_im]
      have hzr : r < ‖z‖ := by
        have := hzA.2
        simpa [mem_closedBall, dist_zero_right, not_le] using this
      have hzR : ‖z‖ < R := by simpa [mem_ball, dist_zero_right] using hzA.1
      exact ⟨Real.log_lt_log hr hzr, Real.log_lt_log (norm_pos_iff.mpr hzne) hzR,
        Complex.neg_pi_lt_arg z,
        lt_of_le_of_ne (Complex.arg_le_pi z) (Complex.slitPlane_arg_ne_pi hzs)⟩
  rw [← heq]
  exact hSc.isPreconnected.image _ Complex.continuous_exp.continuousOn

/-- A slit annulus has a bounded hole in its closure, but no subset of the
annulus has a bounded complementary component containing the origin. -/
theorem exists_slit_annulus_hole_without_barrier :
    ∃ G : Set ℂ, IsOpen G ∧ IsConnected G ∧ closure G ⊆ ball 0 1 ∧
      ∃ U ∈ connectedComponentsIn (closure G)ᶜ,
        Bornology.IsBounded U ∧ (0 : ℂ) ∈ U ∧
        ∀ K ⊆ G, ∀ W ∈ connectedComponentsIn Kᶜ,
          (0 : ℂ) ∈ W → ¬ Bornology.IsBounded W := by
  let A : Set ℂ := annulus 0 (1 / 2) (3 / 4)
  let G : Set ℂ := A ∩ Complex.slitPlane
  have hAo : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  have hd : Dense {z : ℂ | z.im ≠ 0} := by
    change Dense ((Complex.im ⁻¹' ({0} : Set ℝ))ᶜ)
    exact (dense_compl_singleton (0 : ℝ)).preimage Complex.isOpenMap_im
  have hs : Dense Complex.slitPlane := hd.mono (fun z hz => Or.inr hz)
  have hA : A ⊆ closure G := by
    simpa [G, inter_comm] using hs.open_subset_closure_inter hAo
  have hcl : closure G = closure A :=
    subset_antisymm (closure_mono inter_subset_left) (closure_minimal hA isClosed_closure)
  have hclunit : closure G ⊆ ball 0 1 := by
    rw [hcl]
    exact (closure_minimal (fun _ hx => ball_subset_closedBall hx.1) isClosed_closedBall).trans
      (closedBall_subset_ball (by norm_num))
  have h0 : (0 : ℂ) ∈ (closure G)ᶜ := by
    rw [hcl]
    have hclout : closure A ⊆ (ball (0 : ℂ) (1 / 2))ᶜ := by
      apply closure_minimal _ isOpen_ball.isClosed_compl
      intro x hx hxball
      exact hx.2 (ball_subset_closedBall hxball)
    exact fun h => hclout h (mem_ball_self (by norm_num))
  let U := connectedComponentIn (closure G)ᶜ 0
  have hU : U ∈ connectedComponentsIn (closure G)ᶜ := ⟨0, h0, rfl⟩
  have h0U : (0 : ℂ) ∈ U := mem_connectedComponentIn h0
  have hUb : Bornology.IsBounded U := by
    refine (isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) (5 / 8))).subset ?_
    intro x hx
    by_contra h
    have hxnorm : (5 / 8 : ℝ) ≤ dist x 0 := by simpa [mem_ball, not_lt] using h
    obtain ⟨q, hqU, hqdist⟩ := isPreconnected_connectedComponentIn.intermediate_value
      h0U hx (continuous_id.dist continuous_const).continuousOn
      (show dist (0 : ℂ) 0 ≤ (5 / 8 : ℝ) ∧ (5 / 8 : ℝ) ≤ dist x 0 by
        exact ⟨by norm_num, hxnorm⟩)
    have hqA : q ∈ A := by
      change dist q 0 = (5 / 8 : ℝ) at hqdist
      change q ∈ ball (0 : ℂ) (3 / 4) \ closedBall 0 (1 / 2)
      rw [mem_sdiff, mem_ball, mem_closedBall, not_le, hqdist]
      norm_num
    exact (connectedComponentIn_subset _ _ hqU) (hA hqA)
  have hGc : IsConnected G := by
    refine ⟨⟨((5 / 8 : ℝ) : ℂ), ?_⟩, isPreconnected_slit_annulus (by norm_num) (by norm_num)⟩
    norm_num [G, A, annulus, mem_ball, mem_closedBall, dist_zero_right,
      Complex.norm_real, Complex.mem_slitPlane_iff]
  refine ⟨G, hAo.inter Complex.isOpen_slitPlane, hGc, hclunit, U, hU, hUb, h0U, ?_⟩
  intro K hKG W hW h0W hWb
  let L : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Iic 0
  have hLpre : IsPreconnected L := isPreconnected_Iic.image _ Complex.continuous_ofReal.continuousOn
  have h0L : (0 : ℂ) ∈ L := ⟨0, (show (0 : ℝ) ≤ 0 from le_rfl), by simp⟩
  have hLK : L ⊆ Kᶜ := by
    rintro _ ⟨t, ht, rfl⟩ hk
    have hslt := (hKG hk).2
    rw [Complex.mem_slitPlane_iff] at hslt
    simp only [Complex.ofReal_re, Complex.ofReal_im, ne_eq, not_true_eq_false, or_false] at hslt
    exact (not_lt_of_ge ht) hslt
  have hLW : L ⊆ W := by
    obtain ⟨p, hp, hpW⟩ := hW
    have h0p : (0 : ℂ) ∈ connectedComponentIn Kᶜ p := hpW.symm ▸ h0W
    have heq : connectedComponentIn Kᶜ 0 = W := (connectedComponentIn_eq h0p).symm.trans hpW
    exact heq ▸ hLpre.subset_connectedComponentIn h0L hLK
  obtain ⟨r, hr⟩ := hWb.subset_ball (0 : ℂ)
  have ht : -(abs r + 1) ≤ (0 : ℝ) := by linarith [abs_nonneg r]
  have hm := hr (hLW (show (((-(abs r + 1) : ℝ) : ℂ)) ∈ L from ⟨_, ht, rfl⟩))
  rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_pos (show 0 < |r| + 1 by positivity)] at hm
  linarith [le_abs_self r]

end HarmonicBalls
