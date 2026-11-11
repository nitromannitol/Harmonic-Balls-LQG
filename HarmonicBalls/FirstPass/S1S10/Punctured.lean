import HarmonicBalls.Defs.Geometry

/-! # Connectedness after removing a point from a planar open set

Used for the no-cut-point clause of the corrected Lemma 10.5 ([C48]): for an open preconnected `U ⊂ ℂ` and `p ∈ U`,
`U \ {p}` is preconnected. Classical; proved here from the polar parametrisation of a punctured disc.
-/

namespace HarmonicBalls

open Set Complex Metric

/-- A punctured open disc in `ℂ` is preconnected (polar parametrisation by `(0,R) × ℝ`). -/
theorem isPreconnected_ball_diff_center (p : ℂ) (R : ℝ) :
    IsPreconnected (ball p R \ {p}) := by
  have hpc : IsPreconnected (Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ)) :=
    isPreconnected_Ioo.prod isPreconnected_univ
  have hcont : Continuous fun q : ℝ × ℝ => p + (q.1 : ℂ) * exp ((q.2 : ℂ) * I) := by fun_prop
  have himg := hpc.image _ hcont.continuousOn
  have heq : (fun q : ℝ × ℝ => p + (q.1 : ℂ) * exp ((q.2 : ℂ) * I)) '' (Ioo (0 : ℝ) R ×ˢ (univ : Set ℝ))
      = ball p R \ {p} := by
    ext z
    constructor
    · rintro ⟨⟨s, θ⟩, ⟨hs, -⟩, rfl⟩
      have hn : ‖(s : ℂ) * exp ((θ : ℂ) * I)‖ = s := by
        rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hs.1.le]
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, hn]
        exact hs.2
      · intro hmem
        have hX : (s : ℂ) * exp ((θ : ℂ) * I) = 0 := by
          have h1 : p + (s : ℂ) * exp ((θ : ℂ) * I) = p := hmem
          linear_combination h1
        rcases mul_eq_zero.mp hX with h0 | h0
        · exact hs.1.ne' (by exact_mod_cast h0)
        · exact exp_ne_zero _ h0
    · intro hz
      have hzp : z - p ≠ 0 := sub_ne_zero.mpr hz.2
      have hpos : 0 < ‖z - p‖ := norm_pos_iff.mpr hzp
      have hlt : ‖z - p‖ < R := by
        have := hz.1
        rw [mem_ball, dist_eq_norm] at this
        exact this
      refine ⟨(‖z - p‖, arg (z - p)), ⟨⟨hpos, hlt⟩, mem_univ _⟩, ?_⟩
      have h := norm_mul_exp_arg_mul_I (z - p)
      simp only
      linear_combination h
  rw [← heq]
  exact himg

/-- Removing a point `p` of an open preconnected set `U ⊂ ℂ` leaves `U \ {p}` preconnected. -/
theorem isPreconnected_open_diff_point {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    {p : ℂ} (hp : p ∈ U) : IsPreconnected (U \ {p}) := by
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hU p hp
  have hD : IsPreconnected (ball p R \ {p}) := isPreconnected_ball_diff_center p R
  have hDA : ball p R \ {p} ⊆ U \ {p} := sdiff_subset_sdiff_left hball
  intro u v hu hv hsub hun hvn
  by_contra hempty
  have hnoint : ∀ x ∈ U \ {p}, x ∉ u ∩ v := fun x hx hx' => hempty ⟨x, hx, hx'⟩
  have hDsub : ball p R \ {p} ⊆ u ∪ v := fun x hx => hsub (hDA hx)
  -- the punctured disc lies on one side of the separation
  have hside : (ball p R \ {p} ⊆ u) ∨ (ball p R \ {p} ⊆ v) := by
    by_cases hDu : ((ball p R \ {p}) ∩ u).Nonempty
    · by_cases hDv : ((ball p R \ {p}) ∩ v).Nonempty
      · obtain ⟨x, hxD, hxuv⟩ := hD u v hu hv hDsub hDu hDv
        exact (hnoint x (hDA hxD) hxuv).elim
      · left
        intro x hx
        rcases hDsub hx with h | h
        · exact h
        · exact (hDv ⟨x, hx, h⟩).elim
    · right
      intro x hx
      rcases hDsub hx with h | h
      · exact (hDu ⟨x, hx, h⟩).elim
      · exact h
  have hpball : p ∈ ball p R := mem_ball_self hR
  rcases hside with hDu' | hDv'
  · -- the disc lies in `u`: separate `U` by `u ∪ ball p R` and `v \ {p}`
    have hu' : IsOpen (u ∪ ball p R) := hu.union isOpen_ball
    have hv' : IsOpen (v \ {p}) := hv.sdiff isClosed_singleton
    have hcover : U ⊆ (u ∪ ball p R) ∪ (v \ {p}) := by
      intro x hx
      by_cases hxp : x = p
      · exact Or.inl (Or.inr (hxp ▸ hpball))
      · rcases hsub (show x ∈ U \ {p} from ⟨hx, hxp⟩) with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr ⟨h, hxp⟩
    obtain ⟨y, hyU, hyv⟩ := hvn
    have hne1 : (U ∩ (u ∪ ball p R)).Nonempty := ⟨p, hp, Or.inr hpball⟩
    have hne2 : (U ∩ (v \ {p})).Nonempty := ⟨y, hyU.1, hyv, hyU.2⟩
    obtain ⟨x, hxU, hx1, hx2⟩ := hUc _ _ hu' hv' hcover hne1 hne2
    rcases hx1 with h | h
    · exact (hnoint x ⟨hxU, hx2.2⟩ ⟨h, hx2.1⟩).elim
    · exact (hnoint x ⟨hxU, hx2.2⟩ ⟨hDu' ⟨h, hx2.2⟩, hx2.1⟩).elim
  · -- the disc lies in `v`: separate `U` by `v ∪ ball p R` and `u \ {p}`
    have hv' : IsOpen (v ∪ ball p R) := hv.union isOpen_ball
    have hu' : IsOpen (u \ {p}) := hu.sdiff isClosed_singleton
    have hcover : U ⊆ (v ∪ ball p R) ∪ (u \ {p}) := by
      intro x hx
      by_cases hxp : x = p
      · exact Or.inl (Or.inr (hxp ▸ hpball))
      · rcases hsub (show x ∈ U \ {p} from ⟨hx, hxp⟩) with h | h
        · exact Or.inr ⟨h, hxp⟩
        · exact Or.inl (Or.inl h)
    obtain ⟨y, hyU, hyu⟩ := hun
    have hne1 : (U ∩ (v ∪ ball p R)).Nonempty := ⟨p, hp, Or.inr hpball⟩
    have hne2 : (U ∩ (u \ {p})).Nonempty := ⟨y, hyU.1, hyu, hyU.2⟩
    obtain ⟨x, hxU, hx1, hx2⟩ := hUc _ _ hv' hu' hcover hne1 hne2
    rcases hx1 with h | h
    · exact (hnoint x ⟨hxU, hx2.2⟩ ⟨hx2.1, h⟩).elim
    · exact (hnoint x ⟨hxU, hx2.2⟩ ⟨hx2.1, hDv' ⟨h, hx2.2⟩⟩).elim

end HarmonicBalls
