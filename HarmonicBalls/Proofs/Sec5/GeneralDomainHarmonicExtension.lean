import HarmonicBalls.Proofs.Sec5.GeneralDomainAvoidingCircles

/-! # Removable locally finite-rank sets for bounded harmonic functions -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian InnerProductSpace

/-- A locally bounded harmonic function on the complement of a closed,
locally finite-rank set extends harmonically across it. -/
theorem exists_harmonic_extension_of_locallyFiniteRankOn
    {U K : Set ℂ} {R : ℝ} {h : ℂ → ℝ}
    (hU : IsOpen U) (hUR : U ⊆ ball (0 : ℂ) R)
    (hKclosed : IsClosed K) (hK : LocallyFiniteRankOn (ball (0 : ℂ) R) K)
    (hh : HarmonicOnNhd h (U \ K))
    (hbounded : ∀ a ∈ U, ∃ ε M : ℝ, 0 < ε ∧
      ∀ y ∈ ball a ε \ K, |h y| ≤ M) :
    ∃ H : ℂ → ℝ, HarmonicOnNhd H U ∧ EqOn H h (U \ K) := by
  classical
  have hex : ∀ a : U, ∃ r : ℝ, 0 < r ∧ ∃ q : ℂ → ℝ,
      HarmonicOnNhd q (ball (a : ℂ) r) ∧ EqOn q h (ball (a : ℂ) r \ K) := by
    intro a
    obtain ⟨ε, M, hε, hb⟩ := hbounded a a.property
    exact exists_local_harmonic_replacement_of_locallyFiniteRankOn hU hUR a.property
      hKclosed hK hh hε hb
  let r : U → ℝ := fun a => Classical.choose (hex a)
  have hr : ∀ a : U, 0 < r a := fun a => (Classical.choose_spec (hex a)).1
  let q : U → ℂ → ℝ := fun a => Classical.choose (Classical.choose_spec (hex a)).2
  have hq : ∀ a : U, HarmonicOnNhd (q a) (ball (a : ℂ) (r a)) ∧
      EqOn (q a) h (ball (a : ℂ) (r a) \ K) :=
    fun a => Classical.choose_spec (Classical.choose_spec (hex a)).2
  let H : ℂ → ℝ := fun x => if hx : x ∈ U then q ⟨x, hx⟩ x else 0
  have hcount : (K ∩ U).Countable :=
    countable_inter_open_of_locallyFiniteRankOn hU (hK.mono_domain hUR)
  have hagree : ∀ a : U, ∀ x ∈ U ∩ ball (a : ℂ) (r a), H x = q a x := by
    intro a x hx
    let b : U := ⟨x, hx.1⟩
    let V : Set ℂ := U ∩ ball (a : ℂ) (r a) ∩ ball (b : ℂ) (r b)
    have hV : IsOpen V := (hU.inter isOpen_ball).inter isOpen_ball
    have hxV : x ∈ V := ⟨hx, mem_ball_self (hr b)⟩
    have hcountV : (K ∩ V).Countable := hcount.mono (by
      intro y hy
      exact ⟨hy.1, hy.2.1.1⟩)
    have hcl : closure (V \ K) = closure V := closure_sdiff_countable_inter hV hcountV
    have heq : EqOn (q b) (q a) (V \ K) := by
      intro y hy
      exact ((hq b).2 ⟨hy.1.2, hy.2⟩).trans
        (((hq a).2 ⟨hy.1.1.2, hy.2⟩).symm)
    have heqV : EqOn (q b) (q a) V := heq.of_subset_closure
      ((hq b).1.continuousOn.mono (fun _ hy => hy.2))
      ((hq a).1.continuousOn.mono (fun _ hy => hy.1.2)) sdiff_subset
      (by rw [hcl]; exact subset_closure)
    simpa only [H, dite_eq_left hx.1] using heqV hxV
  refine ⟨H, ?_, ?_⟩
  · intro a ha
    let b : U := ⟨a, ha⟩
    apply (harmonicAt_congr_nhds (f₁ := q b) (f₂ := H) ?_).mp
      ((hq b).1 a (mem_ball_self (hr b)))
    filter_upwards [(hU.inter isOpen_ball).mem_nhds
      (show a ∈ U ∩ ball (b : ℂ) (r b) from ⟨ha, mem_ball_self (hr b)⟩)] with x hx
    exact (hagree b x hx).symm
  · intro x hx
    let b : U := ⟨x, hx.1⟩
    exact (hagree b x ⟨hx.1, mem_ball_self (hr b)⟩).trans
      ((hq b).2 ⟨mem_ball_self (hr b), hx.2⟩)

/-- Harmonic extensions across a locally finite-rank set are unique. -/
theorem harmonic_extension_unique_of_locallyFiniteRankOn
    {U K : Set ℂ} {f g : ℂ → ℝ} (hU : IsOpen U)
    (hK : LocallyFiniteRankOn U K) (hf : HarmonicOnNhd f U)
    (hg : HarmonicOnNhd g U) (heq : EqOn f g (U \ K)) : EqOn f g U := by
  have hcl : closure (U \ K) = closure U :=
    closure_sdiff_countable_inter hU (countable_inter_open_of_locallyFiniteRankOn hU hK)
  exact heq.of_subset_closure hf.continuousOn hg.continuousOn sdiff_subset
    (by rw [hcl]; exact subset_closure)



end HarmonicBalls
